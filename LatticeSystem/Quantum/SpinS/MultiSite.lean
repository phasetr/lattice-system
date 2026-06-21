import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.LinearAlgebra.Matrix.Hermitian
import LatticeSystem.Quantum.SpinS.MultiSiteCore

/-!
# Multi-site spin-`S` operator space and site-embedded operators
(Tasaki §2.5 Phase B-β β-3a)

This module generalises the spin-1/2 many-body operator space
(`Quantum/ManyBody.lean`, `ManyBodyOp Λ`) to **arbitrary spin** by
indexing configurations on `Λ → Fin (N + 1)` (with `N = 2S`).

The principal construction is the site-embedded operator

  `onSiteS i A : ManyBodyOpS Λ N`

which acts as a single-site spin-`S` operator
`A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ` on site `i ∈ Λ` and as
the identity on every other site.

This is the multi-site analogue needed for the spin-`S` Heisenberg
Hamiltonian and the §2.5 Marshall–Lieb–Mattis machinery for general
spin (Issue #412 Phase B-γ).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
/-! ## Specialised site-embedded spin-`S` operators -/

/-- The site-`i` spin-`S` operator `Ŝ_i^{(1)}` on the many-body
Hilbert space `(Λ → Fin (N + 1)) → ℂ`. -/
noncomputable def spinSSiteOp1 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp1 N)

/-- The site-`i` spin-`S` operator `Ŝ_i^{(2)}`. -/
noncomputable def spinSSiteOp2 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp2 N)

/-- The site-`i` spin-`S` operator `Ŝ_i^{(3)}`. -/
noncomputable def spinSSiteOp3 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp3 N)

/-- The site-`i` spin-`S` raising operator `Ŝ_i^+`. -/
noncomputable def spinSSiteOpPlus (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOpPlus N)

/-- The site-`i` spin-`S` lowering operator `Ŝ_i^-`. -/
noncomputable def spinSSiteOpMinus (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOpMinus N)

/-! ## Definitional unfoldings for site operators -/

/-- Definitional unfolding of `spinSSiteOp1`. -/
theorem spinSSiteOp1_def (i : Λ) (N : ℕ) :
    spinSSiteOp1 (Λ := Λ) i N = onSiteS i (spinSOp1 N) := rfl

/-- Definitional unfolding of `spinSSiteOp2`. -/
theorem spinSSiteOp2_def (i : Λ) (N : ℕ) :
    spinSSiteOp2 (Λ := Λ) i N = onSiteS i (spinSOp2 N) := rfl

/-- Definitional unfolding of `spinSSiteOp3`. -/
theorem spinSSiteOp3_def (i : Λ) (N : ℕ) :
    spinSSiteOp3 (Λ := Λ) i N = onSiteS i (spinSOp3 N) := rfl

/-- Definitional unfolding of `spinSSiteOpPlus`. -/
theorem spinSSiteOpPlus_def (i : Λ) (N : ℕ) :
    spinSSiteOpPlus (Λ := Λ) i N = onSiteS i (spinSOpPlus N) := rfl

/-- Definitional unfolding of `spinSSiteOpMinus`. -/
theorem spinSSiteOpMinus_def (i : Λ) (N : ℕ) :
    spinSSiteOpMinus (Λ := Λ) i N = onSiteS i (spinSOpMinus N) := rfl

/-! ## Computational basis vectors -/

/-- The standard basis vector at configuration `σ : Λ → Fin (N + 1)`:
the function that is `1` at `σ` and `0` elsewhere. Multi-site spin-`S`
generalisation of `basisVec` (`Quantum/ManyBody.lean`). -/
def basisVecS (σ : Λ → Fin (N + 1)) : (Λ → Fin (N + 1)) → ℂ :=
  fun τ => if τ = σ then 1 else 0

omit [DecidableEq Λ] in
/-- Definitional unfolding of `basisVecS`. -/
theorem basisVecS_def (σ : Λ → Fin (N + 1)) :
    basisVecS σ = (fun τ => if τ = σ then (1 : ℂ) else 0) := rfl

omit [DecidableEq Λ] in
/-- Explicit `if`-form of `basisVecS σ τ`. -/
theorem basisVecS_apply (σ τ : Λ → Fin (N + 1)) :
    basisVecS σ τ = if τ = σ then 1 else 0 := rfl

omit [DecidableEq Λ] in
/-- Diagonal value: `basisVecS σ σ = 1`. -/
@[simp]
theorem basisVecS_self (σ : Λ → Fin (N + 1)) : basisVecS σ σ = 1 := by
  unfold basisVecS; rw [if_pos rfl]

omit [DecidableEq Λ] in
/-- Off-diagonal: `basisVecS σ τ = 0` for `τ ≠ σ`. -/
theorem basisVecS_of_ne {σ τ : Λ → Fin (N + 1)} (hne : τ ≠ σ) :
    basisVecS σ τ = 0 := by
  unfold basisVecS; rw [if_neg hne]

/-- Same-site square: `(onSiteS i A) · (onSiteS i A) = onSiteS i (A * A)`. -/
theorem onSiteS_sq (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) * onSiteS i A = onSiteS i (A * A) :=
  onSiteS_mul_onSiteS_same i A A

/-- Negation distributes over `onSiteS`: `onSiteS i (-A) = -(onSiteS i A)`. -/
theorem onSiteS_neg (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (-A) : ManyBodyOpS Λ N) = -(onSiteS i A) := by
  rw [show (-A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-1 : ℂ) • A from by rw [neg_smul, one_smul]]
  rw [onSiteS_smul]
  rw [show ((-1 : ℂ) • onSiteS (N := N) i A : ManyBodyOpS Λ N) =
        -onSiteS i A from by rw [neg_smul, one_smul]]

/-- Triple-product same-site identity:
`(onSiteS i A) · (onSiteS i A) · (onSiteS i A) = onSiteS i (A * A * A)`. -/
theorem onSiteS_cube (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) * onSiteS i A * onSiteS i A =
      onSiteS i (A * A * A) := by
  rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same]

/-- Power identity: `(onSiteS i A)^k = onSiteS i (A^k)`. -/
theorem onSiteS_pow (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (k : ℕ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ k = onSiteS i (A ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact (onSiteS_one i).symm
  | succ k ih =>
    rw [pow_succ, ih, onSiteS_mul_onSiteS_same]
    rw [pow_succ]

/-- `onSiteS i 0 ^ k = 0` for `k > 0` (zero embedding stays zero
under repeated multiplication). Specialisation of `onSiteS_pow`. -/
theorem onSiteS_zero_pow (i : Λ) {k : ℕ} (hk : 0 < k) :
    (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        : ManyBodyOpS Λ N) ^ k = 0 := by
  rw [onSiteS_pow]
  rw [show (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) ^ k = 0 from
    zero_pow (Nat.pos_iff_ne_zero.mp hk)]
  exact onSiteS_zero i

/-- The site-embedded sum: `onSiteS i (∑ k, A k) = ∑ k, onSiteS i (A k)`. -/
theorem onSiteS_finset_sum {ι : Type*} (i : Λ) (s : Finset ι)
    (f : ι → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (∑ k ∈ s, f k) : ManyBodyOpS Λ N) =
      ∑ k ∈ s, onSiteS i (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [onSiteS_zero]
  | @insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat,
      onSiteS_add, ih]

/-- Convenience: `onSiteS i A = onSiteS i (A + 0)`. -/
theorem onSiteS_add_zero (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (A + 0) : ManyBodyOpS Λ N) = onSiteS i A := by
  rw [add_zero]

/-- `onSiteS i A^0 = 1` (zero power gives the identity). -/
theorem onSiteS_pow_zero (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 0 = 1 := by
  rw [onSiteS_pow]
  rw [pow_zero]
  exact onSiteS_one i

/-- `onSiteS i A ^ 1 = onSiteS i A`. -/
theorem onSiteS_pow_one (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 1 = onSiteS i A := by
  rw [pow_one]

/-- `onSiteS i A ^ 2 = onSiteS i (A^2)`. -/
theorem onSiteS_pow_two (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 2 = onSiteS i (A ^ 2) :=
  onSiteS_pow i A 2

/-- `onSiteS i A ^ 3 = onSiteS i (A^3)`. -/
theorem onSiteS_pow_three (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 3 = onSiteS i (A ^ 3) :=
  onSiteS_pow i A 3

/-- `onSiteS i A ^ 4 = onSiteS i (A^4)`. -/
theorem onSiteS_pow_four (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 4 = onSiteS i (A ^ 4) :=
  onSiteS_pow i A 4

/-- `onSiteS i A ^ 5 = onSiteS i (A^5)`. -/
theorem onSiteS_pow_five (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 5 = onSiteS i (A ^ 5) :=
  onSiteS_pow i A 5

/-- `onSiteS i A` commutes with itself trivially. -/
theorem onSiteS_self_commute (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (onSiteS i A : ManyBodyOpS Λ N) (onSiteS i A) :=
  Commute.refl _

/-- Commute version of distinct-site commutativity. -/
theorem onSiteS_commute_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (onSiteS i A : ManyBodyOpS Λ N) (onSiteS j B) :=
  onSiteS_mul_onSiteS_of_ne hij A B

/-- The site-`i` zero embedding has every product with anything equal to zero. -/
theorem onSiteS_zero_mul (i : Λ) (B : ManyBodyOpS Λ N) :
    (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : ManyBodyOpS Λ N) * B = 0 := by
  rw [onSiteS_zero, zero_mul]

/-- The site-`i` smul embedding: `onSiteS i (c • A) = c • onSiteS i A`,
restated in matrix form (already proved in `onSiteS_smul`). -/
theorem onSiteS_smul_apply (i : Λ) (c : ℂ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i (c • A) : ManyBodyOpS Λ N) σ' σ =
      c * (onSiteS i A : ManyBodyOpS Λ N) σ' σ := by
  rw [onSiteS_smul, Matrix.smul_apply, smul_eq_mul]

/-- The site-`i` add embedding entry-wise:
`(onSiteS i (A + B)) σ' σ = (onSiteS i A) σ' σ + (onSiteS i B) σ' σ`. -/
theorem onSiteS_add_apply (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i (A + B) : ManyBodyOpS Λ N) σ' σ =
      (onSiteS i A : ManyBodyOpS Λ N) σ' σ +
      (onSiteS i B : ManyBodyOpS Λ N) σ' σ := by
  rw [onSiteS_add, Matrix.add_apply]

/-- The site-`i` sub embedding entry-wise. -/
theorem onSiteS_sub_apply (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i (A - B) : ManyBodyOpS Λ N) σ' σ =
      (onSiteS i A : ManyBodyOpS Λ N) σ' σ -
      (onSiteS i B : ManyBodyOpS Λ N) σ' σ := by
  rw [onSiteS_sub, Matrix.sub_apply]

/-- The right multiplicative version: `B * onSiteS i 0 = 0`. -/
theorem mul_onSiteS_zero (i : Λ) (B : ManyBodyOpS Λ N) :
    B * (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
        ManyBodyOpS Λ N) = 0 := by
  rw [onSiteS_zero, mul_zero]

/-- Applying `onSiteS i A` to a basis vector and reading the result
at configuration `τ` yields the matrix element `(onSiteS i A) τ σ`:
the basis-vector mulVec collapses to a single matrix entry. -/
theorem onSiteS_mulVec_basisVecS_apply
    (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ τ : Λ → Fin (N + 1)) :
    (onSiteS i A : ManyBodyOpS Λ N).mulVec (basisVecS σ) τ =
      (onSiteS i A : ManyBodyOpS Λ N) τ σ := by
  classical
  change ∑ σ' : Λ → Fin (N + 1), (onSiteS i A) τ σ' * basisVecS σ σ' =
        (onSiteS i A) τ σ
  simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ σ (fun σ' => (onSiteS i A) τ σ')]
  simp

/-- For distinct sites `x ≠ y`, the product
`onSiteS x (Ŝ^+) * onSiteS y (Ŝ^-)` has non-negative real-part
matrix element on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    exact spinSOpPlus_mul_spinSOpMinus_re_nonneg N (σ' x) (σ x) (σ' y) (σ y)
  · rw [if_neg h]; simp

/-- Symmetric: `onSiteS x (Ŝ^-) * onSiteS y (Ŝ^+)` has non-negative
real-part matrix element on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    exact spinSOpMinus_mul_spinSOpPlus_re_nonneg N (σ' x) (σ x) (σ' y) (σ y)
  · rw [if_neg h]; simp

/-- For distinct sites `x ≠ y`, the product
`onSiteS x (Ŝ^+) * onSiteS y (Ŝ^-)` has zero imaginary part on every
`(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero]
    ring
  · rw [if_neg h]; simp

/-- Symmetric: `onSiteS x (Ŝ^-) * onSiteS y (Ŝ^+)` has zero imaginary
part on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOpMinus_apply_im_zero, spinSOpPlus_apply_im_zero]
    ring
  · rw [if_neg h]; simp


/-- For distinct sites `x ≠ y`, the **sum** `(S+_x S-_y) + (S-_x S+_y)`
matrix element has non-negative real part on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_Minus_plus_Minus_Plus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [Matrix.add_apply, Complex.add_re]
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg hxy σ' σ
  linarith


end LatticeSystem.Quantum
