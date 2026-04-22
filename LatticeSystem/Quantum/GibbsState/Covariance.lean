/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.GibbsState

/-!
# Gibbs state variance + covariance + bilinearity decompositions

The variance / covariance machinery built on top of the basic
Gibbs expectation:
- variance,
- complex covariance + bilinearity + scalar-vanishing,
- anticommutator real / commutator purely imaginary,
- symmetric covariance (real-valued for Hermitian observables),
  bilinearity, scalar-shift behaviour, symmetric/antisymmetric
  decomposition.

(Refactor Phase 2 PR 21 — first GibbsState extraction, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Variance -/

/-- The canonical-ensemble variance of an observable `O` at inverse
temperature `β` under Hamiltonian `H`:
`Var_β(O) := ⟨O²⟩_β − (⟨O⟩_β)²`. -/
noncomputable def gibbsVariance (β : ℝ) (H O : ManyBodyOp Λ) : ℂ :=
  gibbsExpectation β H (O * O) - (gibbsExpectation β H O) ^ 2

/-- Unfolding lemma: `Var_β(O) = ⟨O · O⟩_β − ⟨O⟩_β²`. -/
theorem gibbsVariance_eq (β : ℝ) (H O : ManyBodyOp Λ) :
    gibbsVariance β H O =
      gibbsExpectation β H (O * O) - (gibbsExpectation β H O) ^ 2 :=
  rfl

/-- For Hermitian Gibbs `H` and Hermitian observable `O`, the variance
is real. The second moment is real by `gibbsExpectation_sq_im_of_isHermitian`,
the squared first moment by squaring a real complex number, and the
difference of two reals is real. -/
theorem gibbsVariance_im_of_isHermitian {H O : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) :
    (gibbsVariance β H O).im = 0 := by
  unfold gibbsVariance
  have h1 : (gibbsExpectation β H (O * O)).im = 0 :=
    gibbsExpectation_sq_im_of_isHermitian hH hO β
  have h2 : (gibbsExpectation β H O).im = 0 :=
    gibbsExpectation_im_of_isHermitian hH hO β
  have h2sq : ((gibbsExpectation β H O) ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im, h2, zero_mul, mul_zero, add_zero]
  rw [Complex.sub_im, h1, h2sq, sub_zero]

/-- At `β = 0`, the variance reduces to the normalised-trace formula
`Var_0(O) = (1/dim) · Tr(O²) − ((1/dim) · Tr O)²`. -/
theorem gibbsVariance_zero (H O : ManyBodyOp Λ) :
    gibbsVariance 0 H O =
      ((Fintype.card (Λ → Fin 2) : ℂ))⁻¹ * (O * O).trace
        - (((Fintype.card (Λ → Fin 2) : ℂ))⁻¹ * O.trace) ^ 2 := by
  unfold gibbsVariance
  rw [gibbsExpectation_zero, gibbsExpectation_zero]

/-- The variance equals the second moment of the centered observable
`Ô := O − ⟨O⟩ · 1`:
`Var_β(O) = ⟨(O − ⟨O⟩_β · 1) · (O − ⟨O⟩_β · 1)⟩_β` (when `Z(β) ≠ 0`). -/
theorem gibbsVariance_eq_centered_sq {H O : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) :
    gibbsExpectation β H ((O - (gibbsExpectation β H O) • (1 : ManyBodyOp Λ)) *
        (O - (gibbsExpectation β H O) • 1)) = gibbsVariance β H O := by
  set c := gibbsExpectation β H O with hc
  have hsq : (O - c • (1 : ManyBodyOp Λ)) * (O - c • 1) =
             O * O - c • O - c • O + (c * c) • (1 : ManyBodyOp Λ) := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul]
    abel
  rw [hsq]
  simp only [gibbsExpectation_add, gibbsExpectation_sub, gibbsExpectation_smul]
  rw [show gibbsExpectation β H 1 = 1 from gibbsExpectation_one β hZ]
  unfold gibbsVariance
  rw [pow_two, ← hc]
  ring

/-! ## Covariance -/

/-- The canonical-ensemble covariance of two observables `A`, `B` at
inverse temperature `β` under Hamiltonian `H`:
`Cov_β(A, B) := ⟨A · B⟩_β − ⟨A⟩_β · ⟨B⟩_β`. -/
noncomputable def gibbsCovariance (β : ℝ) (H A B : ManyBodyOp Λ) : ℂ :=
  gibbsExpectation β H (A * B) - gibbsExpectation β H A * gibbsExpectation β H B

/-- Unfolding lemma:
`Cov_β(A, B) = ⟨A · B⟩_β − ⟨A⟩_β · ⟨B⟩_β`. -/
theorem gibbsCovariance_eq (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsCovariance β H A B =
      gibbsExpectation β H (A * B)
        - gibbsExpectation β H A * gibbsExpectation β H B :=
  rfl

/-- Self-covariance is the variance:
`Cov_β(O, O) = Var_β(O)`. -/
theorem gibbsCovariance_self_eq_variance (β : ℝ) (H O : ManyBodyOp Λ) :
    gibbsCovariance β H O O = gibbsVariance β H O := by
  unfold gibbsCovariance gibbsVariance
  rw [pow_two]

/-- The antisymmetric part of the complex covariance equals the
commutator expectation:
`Cov_β(A, B) − Cov_β(B, A) = ⟨A · B − B · A⟩_β`.
The product terms `⟨A⟩ · ⟨B⟩` cancel, isolating the noncommutativity
of `A` and `B`. -/
theorem gibbsCovariance_sub_swap_eq_commutator (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsCovariance β H A B - gibbsCovariance β H B A
      = gibbsExpectation β H (A * B - B * A) := by
  unfold gibbsCovariance
  rw [gibbsExpectation_sub]
  ring

/-! ### Bilinearity of the complex covariance -/

/-- Additivity in the left argument:
`Cov_β(A₁ + A₂, B) = Cov_β(A₁, B) + Cov_β(A₂, B)`. -/
theorem gibbsCovariance_add_left (β : ℝ) (H A₁ A₂ B : ManyBodyOp Λ) :
    gibbsCovariance β H (A₁ + A₂) B
      = gibbsCovariance β H A₁ B + gibbsCovariance β H A₂ B := by
  unfold gibbsCovariance
  rw [add_mul, gibbsExpectation_add, gibbsExpectation_add]
  ring

/-- Additivity in the right argument:
`Cov_β(A, B₁ + B₂) = Cov_β(A, B₁) + Cov_β(A, B₂)`. -/
theorem gibbsCovariance_add_right (β : ℝ) (H A B₁ B₂ : ManyBodyOp Λ) :
    gibbsCovariance β H A (B₁ + B₂)
      = gibbsCovariance β H A B₁ + gibbsCovariance β H A B₂ := by
  unfold gibbsCovariance
  rw [mul_add, gibbsExpectation_add, gibbsExpectation_add]
  ring

/-- Scalar pull-out from the left argument:
`Cov_β(c • A, B) = c · Cov_β(A, B)`. -/
theorem gibbsCovariance_smul_left (β : ℝ) (H : ManyBodyOp Λ) (c : ℂ)
    (A B : ManyBodyOp Λ) :
    gibbsCovariance β H (c • A) B = c * gibbsCovariance β H A B := by
  unfold gibbsCovariance
  rw [Matrix.smul_mul, gibbsExpectation_smul, gibbsExpectation_smul]
  ring

/-- Scalar pull-out from the right argument:
`Cov_β(A, c • B) = c · Cov_β(A, B)`. -/
theorem gibbsCovariance_smul_right (β : ℝ) (H A : ManyBodyOp Λ) (c : ℂ)
    (B : ManyBodyOp Λ) :
    gibbsCovariance β H A (c • B) = c * gibbsCovariance β H A B := by
  unfold gibbsCovariance
  rw [Matrix.mul_smul, gibbsExpectation_smul, gibbsExpectation_smul]
  ring

/-! #### Vanishing on constant-scalar arguments -/

/-- The complex covariance vanishes when its left argument is a scalar
multiple of the identity, provided `Z(β) ≠ 0`. -/
theorem gibbsCovariance_const_smul_one_left_eq_zero {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) (c : ℂ) (B : ManyBodyOp Λ) :
    gibbsCovariance β H (c • (1 : ManyBodyOp Λ)) B = 0 := by
  unfold gibbsCovariance
  rw [Matrix.smul_mul, Matrix.one_mul, gibbsExpectation_smul,
    gibbsExpectation_smul, gibbsExpectation_one β hZ, mul_one]
  ring

/-- The complex covariance vanishes when its right argument is a scalar
multiple of the identity, provided `Z(β) ≠ 0`. -/
theorem gibbsCovariance_const_smul_one_right_eq_zero {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) (A : ManyBodyOp Λ) (c : ℂ) :
    gibbsCovariance β H A (c • (1 : ManyBodyOp Λ)) = 0 := by
  unfold gibbsCovariance
  rw [Matrix.mul_smul, Matrix.mul_one, gibbsExpectation_smul,
    gibbsExpectation_smul, gibbsExpectation_one β hZ, mul_one]
  ring

/-! ## Anticommutator real, commutator purely imaginary

For Hermitian `ρ` and arbitrary `X`,
  `star Tr(ρ · X) = Tr((ρ · X)ᴴ) = Tr(Xᴴ · ρ) = Tr(ρ · Xᴴ)`,
combining `trace_conjTranspose`, `conjTranspose_mul`, Hermiticity of
`ρ`, and the cyclic property `Matrix.trace_mul_comm`. Specialising
`X = A · B` with `A, B` Hermitian gives
`star ⟨A · B⟩_β = ⟨B · A⟩_β`. From this, `⟨A·B + B·A⟩_β` (an "anti-
commutator") is `z + star z = 2·Re z`, hence real, and `⟨A·B − B·A⟩_β`
is `z − star z = 2 i·Im z`, hence purely imaginary. -/

/-- For Hermitian `ρ : Matrix n n ℂ` and arbitrary `X`,
`star Tr(ρ · X) = Tr(ρ · Xᴴ)`. -/
theorem _root_.Matrix.trace_mul_conjTranspose_swap_of_isHermitian
    {n : Type*} [Fintype n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (X : Matrix n n ℂ) :
    star (ρ * X).trace = (ρ * X.conjTranspose).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hρ.eq,
    Matrix.trace_mul_comm]

/-- For Hermitian `H` and Hermitian `A, B`,
`star ⟨A · B⟩_β = ⟨B · A⟩_β`. -/
theorem gibbsExpectation_star_swap_of_isHermitian {H A B : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) (β : ℝ) :
    star (gibbsExpectation β H (A * B)) = gibbsExpectation β H (B * A) := by
  unfold gibbsExpectation
  rw [Matrix.trace_mul_conjTranspose_swap_of_isHermitian
        (gibbsState_isHermitian hH β) (A * B),
      Matrix.conjTranspose_mul, hA.eq, hB.eq]

/-- For Hermitian `H` and Hermitian `A, B`, the anticommutator
expectation `⟨A · B + B · A⟩_β` is real. -/
theorem gibbsExpectation_anticommutator_im {H A B : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) (β : ℝ) :
    (gibbsExpectation β H (A * B + B * A)).im = 0 := by
  rw [gibbsExpectation_add, ← gibbsExpectation_star_swap_of_isHermitian hH hA hB β,
    Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]

/-- For Hermitian `H` and Hermitian `A, B`, the commutator expectation
`⟨A · B − B · A⟩_β` is purely imaginary. -/
theorem gibbsExpectation_commutator_re {H A B : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) (β : ℝ) :
    (gibbsExpectation β H (A * B - B * A)).re = 0 := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ (B * A), gibbsExpectation_add,
    gibbsExpectation_smul,
    ← gibbsExpectation_star_swap_of_isHermitian hH hA hB β]
  simp [Complex.add_re, Complex.conj_re]

/-- For Hermitian `H` and Hermitian observable `O`,
`(⟨H · O⟩_β).im = 0`, i.e.\ the expectation of the (generally
non-Hermitian) product `H · O` is real. -/
theorem gibbsExpectation_mul_hamiltonian_im {H O : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (β : ℝ) :
    (gibbsExpectation β H (H * O)).im = 0 := by
  have hcomm := gibbsExpectation_mul_hamiltonian_comm β H O
  have hstar := gibbsExpectation_star_swap_of_isHermitian hH hH hO β
  have : star (gibbsExpectation β H (H * O)) = gibbsExpectation β H (H * O) := by
    rw [hstar, ← hcomm]
  exact Complex.conj_eq_iff_im.mp this

/-! ## Symmetric covariance (real-valued for Hermitian observables) -/

/-- The symmetric (real-valued for Hermitian observables) canonical
covariance: `Cov^s_β(A, B) := (1/2) · ⟨A · B + B · A⟩_β − ⟨A⟩_β · ⟨B⟩_β`.
The complex covariance `gibbsCovariance` for non-commuting Hermitian
observables generally has a nonzero imaginary part; averaging over the
anticommutator restores realness. -/
noncomputable def gibbsCovarianceSymm (β : ℝ) (H A B : ManyBodyOp Λ) : ℂ :=
  (2 : ℂ)⁻¹ * gibbsExpectation β H (A * B + B * A)
    - gibbsExpectation β H A * gibbsExpectation β H B

/-- Unfolding lemma:
`Cov^s_β(A, B) = (1/2) · ⟨A · B + B · A⟩_β − ⟨A⟩_β · ⟨B⟩_β`. -/
theorem gibbsCovarianceSymm_eq (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H A B =
      (2 : ℂ)⁻¹ * gibbsExpectation β H (A * B + B * A)
        - gibbsExpectation β H A * gibbsExpectation β H B :=
  rfl

/-- Self symmetric-covariance is the variance:
`Cov^s_β(O, O) = Var_β(O)`. The anticommutator `O · O + O · O = 2(O · O)`
collapses the (1/2) prefactor. -/
theorem gibbsCovarianceSymm_self_eq_variance (β : ℝ) (H O : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H O O = gibbsVariance β H O := by
  unfold gibbsCovarianceSymm gibbsVariance
  have h2 : O * O + O * O = (2 : ℂ) • (O * O) := by
    rw [two_smul]
  rw [h2, gibbsExpectation_smul, ← mul_assoc, inv_mul_cancel₀ two_ne_zero,
    one_mul, pow_two]

/-- The symmetric covariance is symmetric in its observable arguments:
`Cov^s_β(A, B) = Cov^s_β(B, A)`. The anticommutator
`A · B + B · A = B · A + A · B` is unchanged under swap, and the product
`⟨A⟩ · ⟨B⟩ = ⟨B⟩ · ⟨A⟩` is commutative in `ℂ`. -/
theorem gibbsCovarianceSymm_comm (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H A B = gibbsCovarianceSymm β H B A := by
  unfold gibbsCovarianceSymm
  rw [add_comm (A * B) (B * A), mul_comm (gibbsExpectation β H A)]

/-! #### Bilinearity of the symmetric covariance -/

/-- Additivity in the left argument:
`Cov^s_β(A₁ + A₂, B) = Cov^s_β(A₁, B) + Cov^s_β(A₂, B)`. -/
theorem gibbsCovarianceSymm_add_left (β : ℝ) (H A₁ A₂ B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H (A₁ + A₂) B
      = gibbsCovarianceSymm β H A₁ B + gibbsCovarianceSymm β H A₂ B := by
  unfold gibbsCovarianceSymm
  have hexp : (A₁ + A₂) * B + B * (A₁ + A₂)
              = (A₁ * B + B * A₁) + (A₂ * B + B * A₂) := by
    rw [add_mul, mul_add]; abel
  rw [hexp, gibbsExpectation_add, gibbsExpectation_add,
      gibbsExpectation_add (β := β) (H := H) A₁ A₂]
  ring

/-- Additivity in the right argument:
`Cov^s_β(A, B₁ + B₂) = Cov^s_β(A, B₁) + Cov^s_β(A, B₂)`. -/
theorem gibbsCovarianceSymm_add_right (β : ℝ) (H A B₁ B₂ : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H A (B₁ + B₂)
      = gibbsCovarianceSymm β H A B₁ + gibbsCovarianceSymm β H A B₂ := by
  rw [gibbsCovarianceSymm_comm β H A (B₁ + B₂),
      gibbsCovarianceSymm_add_left,
      gibbsCovarianceSymm_comm β H B₁ A, gibbsCovarianceSymm_comm β H B₂ A]

/-- Scalar pull-out from the left argument:
`Cov^s_β(c • A, B) = c · Cov^s_β(A, B)`. -/
theorem gibbsCovarianceSymm_smul_left (β : ℝ) (H : ManyBodyOp Λ) (c : ℂ)
    (A B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H (c • A) B = c * gibbsCovarianceSymm β H A B := by
  unfold gibbsCovarianceSymm
  have hexp : (c • A) * B + B * (c • A) = c • (A * B + B * A) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_add]
  rw [hexp, gibbsExpectation_smul, gibbsExpectation_smul]
  ring

/-- Scalar pull-out from the right argument:
`Cov^s_β(A, c • B) = c · Cov^s_β(A, B)`. -/
theorem gibbsCovarianceSymm_smul_right (β : ℝ) (H A : ManyBodyOp Λ) (c : ℂ)
    (B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H A (c • B) = c * gibbsCovarianceSymm β H A B := by
  rw [gibbsCovarianceSymm_comm β H A (c • B),
      gibbsCovarianceSymm_smul_left,
      gibbsCovarianceSymm_comm β H B A]

/-- The sum-of-observables variance identity:
`Var_β(A + B) = Var_β(A) + Var_β(B) + 2 · Cov^s_β(A, B)`.
The cross term is the symmetric covariance (averaged anticommutator);
for commuting `A, B` it reduces to `2·Cov(A, B)`. -/
theorem gibbsVariance_add (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsVariance β H (A + B)
      = gibbsVariance β H A + gibbsVariance β H B
        + 2 * gibbsCovarianceSymm β H A B := by
  unfold gibbsVariance gibbsCovarianceSymm
  have hexpand : (A + B) * (A + B) = A * A + A * B + B * A + B * B := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  simp only [gibbsExpectation_add]
  ring

/-! #### Variance under scalar / negation / constant shift -/

/-- Variance of the identity is zero when `Z ≠ 0`:
`Var_β(1) = ⟨1⟩ - ⟨1⟩² = 1 - 1 = 0`. -/
theorem gibbsVariance_one {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) :
    gibbsVariance β H 1 = 0 := by
  unfold gibbsVariance
  rw [Matrix.one_mul, gibbsExpectation_one β hZ]
  ring

/-- Variance scales as the square: `Var_β(c • A) = c² · Var_β(A)`. -/
theorem gibbsVariance_smul (β : ℝ) (H : ManyBodyOp Λ) (c : ℂ) (A : ManyBodyOp Λ) :
    gibbsVariance β H (c • A) = c ^ 2 * gibbsVariance β H A := by
  unfold gibbsVariance
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, gibbsExpectation_smul,
    gibbsExpectation_smul]
  ring

/-- Variance of a scalar multiple of the identity is zero
(when `Z ≠ 0`): `Var_β(c • 1) = c² · 0 = 0`. -/
theorem gibbsVariance_smul_one {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) (c : ℂ) :
    gibbsVariance β H (c • (1 : ManyBodyOp Λ)) = 0 := by
  rw [gibbsVariance_smul, gibbsVariance_one β hZ, mul_zero]

/-- Variance is invariant under negation: `Var_β(−A) = Var_β(A)`.
Specialisation of `gibbsVariance_smul` at `c = −1`. -/
theorem gibbsVariance_neg (β : ℝ) (H A : ManyBodyOp Λ) :
    gibbsVariance β H (-A) = gibbsVariance β H A := by
  rw [show -A = ((-1 : ℂ)) • A by simp]
  rw [gibbsVariance_smul]
  ring

/-- Variance is invariant under a constant additive shift
(when `Z ≠ 0`): `Var_β(A + c • 1) = Var_β(A)`. -/
theorem gibbsVariance_add_const_smul_one {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) (A : ManyBodyOp Λ) (c : ℂ) :
    gibbsVariance β H (A + c • (1 : ManyBodyOp Λ)) = gibbsVariance β H A := by
  unfold gibbsVariance
  have hexp_self : (A + c • (1 : ManyBodyOp Λ)) * (A + c • 1)
                 = A * A + c • A + c • A + (c * c) • (1 : ManyBodyOp Λ) := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul]
    abel
  rw [hexp_self]
  simp only [gibbsExpectation_add, gibbsExpectation_smul,
    gibbsExpectation_one β hZ]
  ring

/-! #### Symmetric / antisymmetric decomposition -/

/-- The complex covariance decomposes into its symmetric part plus
half the commutator expectation:
`Cov_β(A, B) = Cov^s_β(A, B) + (1/2) · ⟨A · B − B · A⟩_β`. -/
theorem gibbsCovariance_eq_symm_add_half_commutator
    (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsCovariance β H A B
      = gibbsCovarianceSymm β H A B
        + (2 : ℂ)⁻¹ * gibbsExpectation β H (A * B - B * A) := by
  unfold gibbsCovariance gibbsCovarianceSymm
  rw [gibbsExpectation_sub, gibbsExpectation_add]
  ring

/-- The symmetric covariance is the symmetrisation of the complex
covariance:
`Cov^s_β(A, B) = (1/2) · (Cov_β(A, B) + Cov_β(B, A))`. -/
theorem gibbsCovarianceSymm_eq_half_add_swap
    (β : ℝ) (H A B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H A B
      = (2 : ℂ)⁻¹ * (gibbsCovariance β H A B + gibbsCovariance β H B A) := by
  unfold gibbsCovariance gibbsCovarianceSymm
  rw [gibbsExpectation_add]
  ring

/-- For commuting observables `A, B`, the complex covariance equals
the symmetric covariance: `Cov_β(A, B) = Cov^s_β(A, B)`. The
commutator-based antisymmetric part vanishes when `[A, B] = 0`. -/
theorem gibbsCovariance_eq_symm_of_commute (β : ℝ) (H : ManyBodyOp Λ)
    {A B : ManyBodyOp Λ} (h : Commute A B) :
    gibbsCovariance β H A B = gibbsCovarianceSymm β H A B := by
  rw [gibbsCovariance_eq_symm_add_half_commutator]
  have hzero : A * B - B * A = 0 := by rw [h.eq, sub_self]
  rw [hzero]
  unfold gibbsExpectation
  rw [Matrix.mul_zero, Matrix.trace_zero, mul_zero, add_zero]

/-- The symmetric covariance vanishes when its left argument is a
scalar multiple of the identity, provided `Z(β) ≠ 0`. Direct
corollary of `gibbsCovariance_const_smul_one_left_eq_zero` /
`_right_eq_zero` via the symmetrisation identity. -/
theorem gibbsCovarianceSymm_const_smul_one_left_eq_zero {H : ManyBodyOp Λ}
    (β : ℝ) (hZ : partitionFn β H ≠ 0) (c : ℂ) (B : ManyBodyOp Λ) :
    gibbsCovarianceSymm β H (c • (1 : ManyBodyOp Λ)) B = 0 := by
  rw [gibbsCovarianceSymm_eq_half_add_swap,
    gibbsCovariance_const_smul_one_left_eq_zero β hZ,
    gibbsCovariance_const_smul_one_right_eq_zero β hZ]
  ring

/-- The symmetric covariance vanishes when its right argument is a
scalar multiple of the identity, provided `Z(β) ≠ 0`. -/
theorem gibbsCovarianceSymm_const_smul_one_right_eq_zero {H : ManyBodyOp Λ}
    (β : ℝ) (hZ : partitionFn β H ≠ 0) (A : ManyBodyOp Λ) (c : ℂ) :
    gibbsCovarianceSymm β H A (c • (1 : ManyBodyOp Λ)) = 0 := by
  rw [gibbsCovarianceSymm_comm,
    gibbsCovarianceSymm_const_smul_one_left_eq_zero β hZ]

/-- For Hermitian `H` and Hermitian `A, B`, the symmetric covariance
is real. The anticommutator term is real by
`gibbsExpectation_anticommutator_im` (the (1/2) prefactor preserves
realness), and `⟨A⟩ · ⟨B⟩` is the product of two real complex numbers. -/
theorem gibbsCovarianceSymm_im_of_isHermitian {H A B : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) (β : ℝ) :
    (gibbsCovarianceSymm β H A B).im = 0 := by
  unfold gibbsCovarianceSymm
  have h_anti : (gibbsExpectation β H (A * B + B * A)).im = 0 :=
    gibbsExpectation_anticommutator_im hH hA hB β
  have h_a : (gibbsExpectation β H A).im = 0 :=
    gibbsExpectation_im_of_isHermitian hH hA β
  have h_b : (gibbsExpectation β H B).im = 0 :=
    gibbsExpectation_im_of_isHermitian hH hB β
  have h_prod : (gibbsExpectation β H A * gibbsExpectation β H B).im = 0 := by
    rw [Complex.mul_im, h_a, h_b, zero_mul, mul_zero, add_zero]
  have h_inv : ((2 : ℂ)⁻¹).im = 0 := by simp
  have h_half : ((2 : ℂ)⁻¹ * gibbsExpectation β H (A * B + B * A)).im = 0 := by
    rw [Complex.mul_im, h_inv, h_anti, mul_zero, zero_mul, add_zero]
  rw [Complex.sub_im, h_half, h_prod, sub_zero]


end LatticeSystem.Quantum
