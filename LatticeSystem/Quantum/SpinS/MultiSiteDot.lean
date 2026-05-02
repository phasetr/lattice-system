import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Casimir
import LatticeSystem.Quantum.SpinS.PMAsOneTwo
import LatticeSystem.Quantum.SpinS.Hermitian
import LatticeSystem.Quantum.ManyBody

/-!
# Two-site spin-`S` inner product `Ŝ_x · Ŝ_y`
(Tasaki §2.5 Phase B-β β-3c)

For lattice sites `x, y : Λ` and spin parameter `N : ℕ` (with `N = 2S`),
the two-site inner product on the multi-site spin-`S` Hilbert space is

  `Ŝ_x · Ŝ_y := Σ_{α=1,2,3} onSiteS x Ŝ^{(α)} · onSiteS y Ŝ^{(α)}`.

This is the spin-`S` analogue of `spinHalfDot` (`Quantum/SpinDot/Core.lean`).

We record the basic symmetry `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x`, which for `x = y`
is trivial, and for `x ≠ y` follows from `onSiteS_mul_onSiteS_of_ne`
(β-3b). The Tasaki §2.2 (2.2.16)-style raising/lowering decomposition,
the same-site identity `Ŝ_x · Ŝ_x = (N(N+2)/4) · 1`, and Hermiticity
will follow in subsequent PRs.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Two-site spin-`S` inner product
`Ŝ_x · Ŝ_y := Σ_{α=1,2,3} onSiteS x Ŝ^{(α)} · onSiteS y Ŝ^{(α)}`. -/
noncomputable def spinSDot (x y : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
    onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) +
    onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)

/-- Definitional unfolding of `spinSDot`. -/
theorem spinSDot_def (x y : Λ) (N : ℕ) :
    spinSDot x y N =
      onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
        onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := rfl

/-- Symmetry of the two-site dot product: `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x`. -/
theorem spinSDot_comm (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) = spinSDot y x N := by
  unfold spinSDot
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [onSiteS_mul_onSiteS_of_ne hxy (spinSOp1 N) (spinSOp1 N),
        onSiteS_mul_onSiteS_of_ne hxy (spinSOp2 N) (spinSOp2 N),
        onSiteS_mul_onSiteS_of_ne hxy (spinSOp3 N) (spinSOp3 N)]

/-- **Same-site Casimir**: `Ŝ_x · Ŝ_x = (N(N+2)/4) · 1` on the
multi-site space, the lift of the single-site Casimir identity
`(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1` (β-14 of
Issue #458) to the many-body Hilbert space via `onSiteS`. -/
theorem spinSDot_self (x : Λ) (N : ℕ) :
    (spinSDot x x N : ManyBodyOpS Λ N) =
      ((N : ℂ) * (N + 2) / 4) • 1 := by
  unfold spinSDot
  rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same]
  rw [← onSiteS_add, ← onSiteS_add, spinSOp_total_squared,
      onSiteS_smul, onSiteS_one]

/-- `Ŝ_x · Ŝ_y` is Hermitian on the multi-site spin-`S` Hilbert space.
For `x = y`, it reduces to the scalar `(N(N+2)/4) · 1` (β-3e). For
`x ≠ y`, each of the three axis terms is a product of commuting site
embeddings of Hermitian single-site operators (β-3 of Issue #458 +
β-3a). -/
theorem spinSDot_isHermitian (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N).IsHermitian := by
  by_cases hxy : x = y
  · subst hxy
    rw [spinSDot_self]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul,
      show star (((N : ℂ) * (N + 2) / 4)) = ((N : ℂ) * (N + 2) / 4)
        from by simp,
      Matrix.conjTranspose_one]
  · unfold spinSDot
    refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
    · exact Matrix.IsHermitian.mul_of_commute
        (onSiteS_isHermitian x (spinSOp1_isHermitian N))
        (onSiteS_isHermitian y (spinSOp1_isHermitian N))
        (onSiteS_mul_onSiteS_of_ne hxy _ _)
    · exact Matrix.IsHermitian.mul_of_commute
        (onSiteS_isHermitian x (spinSOp2_isHermitian N))
        (onSiteS_isHermitian y (spinSOp2_isHermitian N))
        (onSiteS_mul_onSiteS_of_ne hxy _ _)
    · exact Matrix.IsHermitian.mul_of_commute
        (onSiteS_isHermitian x (spinSOp3_isHermitian N))
        (onSiteS_isHermitian y (spinSOp3_isHermitian N))
        (onSiteS_mul_onSiteS_of_ne hxy _ _)

/-- Sum of same-site Casimirs:
`Σ_{x : Λ} (Ŝ_x · Ŝ_x) = |Λ| · (N(N+2)/4) • 1`. -/
theorem sum_spinSDot_self {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    (∑ x : Λ, spinSDot x x N : ManyBodyOpS Λ N) =
      ((Fintype.card Λ : ℂ) * ((N : ℂ) * (N + 2) / 4)) • 1 := by
  simp_rw [spinSDot_self]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ (Fintype.card Λ)]
  rw [smul_smul]

/-- Symmetry of the spin-`S` two-site dot product (alternative form):
`spinSDot x y N = spinSDot y x N` for any `x, y` (no `≠` required). -/
theorem spinSDot_swap {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x y : Λ) (N : ℕ) :
    spinSDot x y N = spinSDot y x N :=
  spinSDot_comm x y N

/-- The two-site spin-`S` dot product is Hermitian (`Matrix.IsHermitian`)
specifically: `(spinSDot x y N).IsHermitian`. Restated form of β-3g
for direct use. -/
theorem spinSDot_isHermitian_restated {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N).IsHermitian :=
  spinSDot_isHermitian x y N

/-- `spinSDot x y N` and `spinSDot y x N` are the same Hermitian
operator (combining `spinSDot_comm` with Hermiticity). -/
theorem spinSDot_swap_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (x y : Λ) (N : ℕ) :
    (spinSDot y x N : ManyBodyOpS Λ N).IsHermitian := by
  rw [← spinSDot_comm x y N]
  exact spinSDot_isHermitian x y N

/-- For `x = y`, the same-site dot product equals `(N(N+2)/4) • 1`
(restated for emphasis). -/
theorem spinSDot_self_eq {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x : Λ) (N : ℕ) :
    (spinSDot x x N : ManyBodyOpS Λ N) =
      ((N : ℂ) * (N + 2) / 4) • 1 :=
  spinSDot_self x N

/-- `spinSDot x x 0` (trivial spin) equals zero. -/
theorem spinSDot_self_N_zero {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x : Λ) :
    (spinSDot x x 0 : ManyBodyOpS Λ 0) = 0 := by
  rw [spinSDot_self]
  simp


/-- `spinSDot x x N` is a scalar multiple of the identity, hence
commutes with every operator. -/
theorem spinSDot_self_commute (x : Λ) (N : ℕ) (B : ManyBodyOpS Λ N) :
    Commute (spinSDot x x N) B := by
  rw [spinSDot_self]
  unfold Commute SemiconjBy
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- The same-site dot product matrix element on basis configurations:
`(spinSDot x x N) σ τ = (N(N+2)/4) δ_{σ,τ}` (delta-diagonal). -/
theorem spinSDot_self_apply (x : Λ) (N : ℕ) (σ τ : Λ → Fin (N + 1)) :
    (spinSDot x x N : ManyBodyOpS Λ N) σ τ =
      ((N : ℂ) * (N + 2) / 4) * (if σ = τ then 1 else 0) := by
  rw [spinSDot_self]
  rw [Matrix.smul_apply]
  rw [Matrix.one_apply]
  rw [smul_eq_mul]

/-- For `σ ≠ τ`, the same-site dot product matrix element vanishes. -/
theorem spinSDot_self_apply_eq_zero_of_ne (x : Λ) (N : ℕ)
    {σ τ : Λ → Fin (N + 1)} (hne : σ ≠ τ) :
    (spinSDot x x N : ManyBodyOpS Λ N) σ τ = 0 := by
  rw [spinSDot_self_apply, if_neg hne, mul_zero]

/-- The diagonal same-site dot product matrix element. -/
theorem spinSDot_self_apply_diag (x : Λ) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    (spinSDot x x N : ManyBodyOpS Λ N) σ σ = (N : ℂ) * (N + 2) / 4 := by
  rw [spinSDot_self_apply, if_pos rfl, mul_one]

/-- The same-site dot product diagonal value `N(N+2)/4` is non-negative. -/
theorem spinSDot_self_apply_diag_re_nonneg (x : Λ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) :
    0 ≤ ((spinSDot x x N : ManyBodyOpS Λ N) σ σ).re := by
  rw [spinSDot_self_apply_diag]
  rw [show (((N : ℂ) * (N + 2) / 4)).re = ((N : ℝ) * (N + 2) / 4) from by simp]
  positivity

/-- For `σ' ≠ σ`, the same-site dot product real-part vanishes. -/
theorem spinSDot_self_apply_re_eq_zero_of_ne (x : Λ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    ((spinSDot x x N : ManyBodyOpS Λ N) σ' σ).re = 0 := by
  rw [spinSDot_self_apply_eq_zero_of_ne x N hne]
  simp

/-- For `x ≠ y`, the matrix element of `Ŝ_x · Ŝ_y` between
configurations differing off the two-site set `{x, y}` is zero
(the operator only acts on `x` and `y`). -/
theorem spinSDot_apply_eq_zero_of_off_two_site_diff
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  unfold spinSDot
  simp only [Matrix.add_apply]
  rw [onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
      onSiteS_mul_onSiteS_apply_eq hxy]
  rw [if_neg h, if_neg h, if_neg h]
  ring

/-- For `x ≠ y`, if there is some site `z ∉ {x, y}` where `σ' z ≠ σ z`,
the matrix element of `Ŝ_x · Ŝ_y` vanishes. (Equivalent reformulation
parameterized by a witness difference site.) -/
theorem spinSDot_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  apply spinSDot_apply_eq_zero_of_off_two_site_diff hxy N
  intro hagree
  exact hz (hagree z hzx hzy)

/-- Same-site dot product: if `σ' z ≠ σ z` at some witness site `z`,
the matrix element vanishes (since the same-site dot product is
proportional to `Matrix.diagonal` and `σ' ≠ σ`). -/
theorem spinSDot_self_apply_eq_zero_of_diff_at
    (x : Λ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} {z : Λ} (hz : σ' z ≠ σ z) :
    (spinSDot x x N : ManyBodyOpS Λ N) σ' σ = 0 :=
  spinSDot_self_apply_eq_zero_of_ne x N (fun heq => hz (by rw [heq]))


/-- For `x ≠ y`, the diagonal matrix element of `Ŝ_x · Ŝ_y` reduces
to the product of the two `Ŝ^{(3)}` eigenvalues:
`(Ŝ_x · Ŝ_y) σ σ = (N/2 - σ_x.val)(N/2 - σ_y.val)`.

The `Ŝ^{(1)} ⊗ Ŝ^{(1)}` and `Ŝ^{(2)} ⊗ Ŝ^{(2)}` parts vanish on the
diagonal (their factors are off-diagonal). -/
theorem spinSDot_apply_diag_of_ne
    {x y : Λ} (hxy : x ≠ y) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ σ =
      ((N : ℂ) / 2 - (σ x).val) * ((N : ℂ) / 2 - (σ y).val) := by
  unfold spinSDot
  simp only [Matrix.add_apply]
  rw [onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
      onSiteS_mul_onSiteS_apply_eq hxy]
  have hagree : ∀ k : Λ, k ≠ x → k ≠ y → σ k = σ k := fun _ _ _ => rfl
  rw [if_pos hagree, if_pos hagree, if_pos hagree]
  rw [spinSOp1_apply_diag, spinSOp2_apply_diag,
      spinSOp3_apply_diag, spinSOp3_apply_diag]
  ring

/-- The same-site dot product matrix element has zero imaginary part:
the matrix is a real scalar multiple of the identity. -/
theorem spinSDot_self_apply_im_zero (x : Λ) (N : ℕ)
    (σ' σ : Λ → Fin (N + 1)) :
    ((spinSDot x x N : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [spinSDot_self_apply]
  by_cases h : σ' = σ
  · rw [if_pos h]; simp
  · rw [if_neg h]; simp

/-- For `x ≠ y`, the matrix element of `Ŝ_x · Ŝ_y` always has zero
imaginary part. The three axis contributions are `real × real`,
`pure imag × pure imag`, and `real × real` respectively. -/
theorem spinSDot_apply_im_zero_of_ne
    {x y : Λ} (hxy : x ≠ y) (N : ℕ) (σ' σ : Λ → Fin (N + 1)) :
    ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  unfold spinSDot
  simp only [Matrix.add_apply]
  rw [onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
      onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h, if_pos h, if_pos h]
    -- Sum of three terms, each has im = 0.
    have h1 : ((spinSOp1 N (σ' x) (σ x)) * (spinSOp1 N (σ' y) (σ y))).im = 0 := by
      rw [Complex.mul_im]
      rw [spinSOp1_apply_im_zero, spinSOp1_apply_im_zero]
      ring
    have h2 : ((spinSOp2 N (σ' x) (σ x)) * (spinSOp2 N (σ' y) (σ y))).im = 0 := by
      rw [Complex.mul_im]
      rw [spinSOp2_apply_re_zero, spinSOp2_apply_re_zero]
      ring
    have h3 : ((spinSOp3 N (σ' x) (σ x)) * (spinSOp3 N (σ' y) (σ y))).im = 0 := by
      rw [Complex.mul_im]
      rw [spinSOp3_apply_im_zero, spinSOp3_apply_im_zero]
      ring
    rw [Complex.add_im, Complex.add_im, h1, h2, h3]
    ring
  · rw [if_neg h, if_neg h, if_neg h]; simp

/-- **Raising/lowering decomposition** of the two-site spin-`S` dot
product (Tasaki §2.2 eq. (2.2.16) for arbitrary spin):

  `Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^{(3)} Ŝ_y^{(3)}`.

Generalises the spin-1/2 statement `spinHalfDot_eq_plus_minus`. -/
theorem spinSDot_eq_plus_minus (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) =
      (1 / 2 : ℂ) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := by
  unfold spinSDot
  rw [spinSOpPlus_eq_one_add_I_smul_two,
      spinSOpMinus_eq_one_sub_I_smul_two]
  simp only [onSiteS_add, onSiteS_sub, onSiteS_smul]
  set a1 := (onSiteS x (spinSOp1 N) : ManyBodyOpS Λ N)
  set a2 := (onSiteS x (spinSOp2 N) : ManyBodyOpS Λ N)
  set b1 := (onSiteS y (spinSOp1 N) : ManyBodyOpS Λ N)
  set b2 := (onSiteS y (spinSOp2 N) : ManyBodyOpS Λ N)
  have e1 : (a1 + Complex.I • a2) * (b1 - Complex.I • b2) =
      a1 * b1 + a2 * b2 +
        (Complex.I • (a2 * b1) - Complex.I • (a1 * b2)) := by
    rw [add_mul, mul_sub, mul_sub]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel
  have e2 : (a1 - Complex.I • a2) * (b1 + Complex.I • b2) =
      a1 * b1 + a2 * b2 -
        (Complex.I • (a2 * b1) - Complex.I • (a1 * b2)) := by
    rw [sub_mul, mul_add, mul_add]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel
  rw [e1, e2]
  have key : ∀ (p r : ManyBodyOpS Λ N),
      (p + r) + (p - r) = (2 : ℂ) • p := by
    intros p r
    rw [two_smul]; abel
  set p : ManyBodyOpS Λ N := a1 * b1 + a2 * b2 with hp
  set r : ManyBodyOpS Λ N := Complex.I • (a2 * b1) - Complex.I • (a1 * b2)
    with hr
  rw [key p r, smul_smul]
  norm_num

/-- The matrix element of `Ŝ_x · Ŝ_y` always has zero imaginary part
(unified version, no `x ≠ y` assumption). -/
theorem spinSDot_apply_im_zero (x y : Λ) (N : ℕ)
    (σ' σ : Λ → Fin (N + 1)) :
    ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  by_cases hxy : x = y
  · subst hxy; exact spinSDot_self_apply_im_zero x N σ' σ
  · exact spinSDot_apply_im_zero_of_ne hxy N σ' σ

/-- For real coupling, the matrix element of `Ŝ_x · Ŝ_y` always
equals its own real-part embedding. -/
theorem spinSDot_apply_eq_ofReal_re (x y : Λ) (N : ℕ)
    (σ' σ : Λ → Fin (N + 1)) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact spinSDot_apply_im_zero x y N σ' σ

/-- For `x ≠ y`, when `σ' = σ` the spinSDot value is its own
real-part embedding (matches the diagonal formula). -/
theorem spinSDot_apply_diag_eq_ofReal_re_of_ne
    {x y : Λ} (hxy : x ≠ y) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ σ =
      ((((spinSDot x y N : ManyBodyOpS Λ N) σ σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact spinSDot_apply_im_zero_of_ne hxy N σ σ

/-- For `x ≠ y`, the diagonal real part of `spinSDot` equals
`(N/2 - σ_x.val)(N/2 - σ_y.val)` (a real number). -/
theorem spinSDot_apply_diag_re_of_ne
    {x y : Λ} (hxy : x ≠ y) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    ((spinSDot x y N : ManyBodyOpS Λ N) σ σ).re =
      ((N : ℝ) / 2 - (σ x).val) * ((N : ℝ) / 2 - (σ y).val) := by
  rw [spinSDot_apply_diag_of_ne hxy]
  rw [Complex.mul_re]
  push_cast
  simp

/-- For the same-site case, the diagonal real part is `N(N+2)/4`. -/
theorem spinSDot_self_apply_diag_re (x : Λ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) :
    ((spinSDot x x N : ManyBodyOpS Λ N) σ σ).re =
      (N : ℝ) * (N + 2) / 4 := by
  rw [spinSDot_self_apply_diag]
  simp

/-- The same-site `spinSDot x x N σ σ` equals its real-part embedding. -/
theorem spinSDot_self_apply_diag_eq_ofReal_re (x : Λ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) :
    (spinSDot x x N : ManyBodyOpS Λ N) σ σ =
      (((((spinSDot x x N : ManyBodyOpS Λ N) σ σ).re : ℝ) : ℂ)) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact spinSDot_self_apply_im_zero x N σ σ


/-- The matrix-element form of the raising/lowering decomposition of
`spinSDot`: combines the `(1/2)(S+S- + S-S+)` ladder part with the
`S^3 ⊗ S^3` diagonal part. -/
theorem spinSDot_apply_eq_pm_3 (x y : Λ) (N : ℕ)
    (σ' σ : Λ → Fin (N + 1)) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      ((1 / 2 : ℂ) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ := by
  rw [spinSDot_eq_plus_minus]

/-- For `x ≠ y` and configurations differing off the two-site set
`{x, y}`, the matrix element of `Ŝ_x · Ŝ_y` is zero (already
established as `spinSDot_apply_eq_zero_of_off_two_site_diff`). The
real part trivially has zero. -/
theorem spinSDot_apply_re_eq_zero_of_off_two_site_diff
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).re = 0 := by
  rw [spinSDot_apply_eq_zero_of_off_two_site_diff hxy N h]
  simp

/-- For `x ≠ y` and `σ', σ` agreeing off `{x, y}`, the dot-product
matrix element factors via the per-site spinSOp_α matrix elements:
`(Ŝ_x · Ŝ_y) σ' σ = Σ_α S^α(σ'_x)(σ_x) * S^α(σ'_y)(σ_y)`. -/
theorem spinSDot_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      spinSOp1 N (σ' x) (σ x) * spinSOp1 N (σ' y) (σ y) +
      spinSOp2 N (σ' x) (σ x) * spinSOp2 N (σ' y) (σ y) +
      spinSOp3 N (σ' x) (σ x) * spinSOp3 N (σ' y) (σ y) := by
  unfold spinSDot
  simp only [Matrix.add_apply]
  rw [onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
      onSiteS_mul_onSiteS_apply_eq hxy]
  rw [if_pos h, if_pos h, if_pos h]

/-- `spinSDot x y 0` (trivial spin, distinct sites) equals zero. -/
theorem spinSDot_N_zero_of_ne {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {x y : Λ} (hxy : x ≠ y) :
    (spinSDot x y 0 : ManyBodyOpS Λ 0) = 0 := by
  ext σ' σ
  rw [Matrix.zero_apply]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · have hσ'x : σ' x = 0 := by apply Fin.ext; have := (σ' x).isLt; omega
    have hσx : σ x = 0 := by apply Fin.ext; have := (σ x).isLt; omega
    have hσ'y : σ' y = 0 := by apply Fin.ext; have := (σ' y).isLt; omega
    have hσy : σ y = 0 := by apply Fin.ext; have := (σ y).isLt; omega
    unfold spinSDot
    simp only [Matrix.add_apply]
    rw [onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
        onSiteS_mul_onSiteS_apply_eq hxy]
    rw [if_pos h, if_pos h, if_pos h]
    rw [hσ'x, hσx, hσ'y, hσy, spinSOp1_apply_diag, spinSOp2_apply_diag]
    simp
  · exact spinSDot_apply_eq_zero_of_off_two_site_diff hxy 0 h

/-- Unified `spinSDot x y 0 = 0` (any sites). -/
theorem spinSDot_N_zero_total {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x y : Λ) :
    (spinSDot x y 0 : ManyBodyOpS Λ 0) = 0 := by
  by_cases hxy : x = y
  · subst hxy; exact spinSDot_self_N_zero x
  · exact spinSDot_N_zero_of_ne hxy

/-! ## Off-diagonal `Ŝ_x · Ŝ_y` matrix elements on raising/lowering pairs -/

/-- For `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}`,
the matrix element of `Ŝ_x · Ŝ_y` has non-negative real part on the
raising/lowering pair `σ_x = σ'_x + 1, σ_y + 1 = σ'_y`.

The `S^+_x ⊗ S^-_y` term contributes a positive `√(...) × √(...)`,
the `S^-_x ⊗ S^+_y` term vanishes (wrong direction), and the
`S^3_x ⊗ S^3_y` term vanishes (off-diagonal in `S^3`). -/
theorem spinSDot_apply_re_nonneg_of_raising_lowering_x
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val) :
    0 ≤ ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).re := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Complex.add_re]
  rw [Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  rw [Matrix.add_apply, Complex.add_re]
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h12re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have h12im : ((1 / 2 : ℂ)).im = 0 := by norm_num
  rw [h12re, h12im, zero_mul, sub_zero]
  have hσ'x : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  have h3eq : (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
      : ManyBodyOpS Λ N) σ' σ = 0 := by
    rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
    rw [show spinSOp3 N (σ' x) (σ x) = 0 from
      Matrix.diagonal_apply_ne _ hσ'x]
    ring
  rw [h3eq]
  simp
  positivity

/-- For `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}` with
`σ' x ≠ σ x`, the `S^3 ⊗ S^3` part of `Ŝ_x · Ŝ_y` vanishes, so the
matrix element collapses to the `(1/2)(S+ S- + S- S+)` part. -/
theorem spinSDot_apply_eq_pm_only_of_off_diag_at_x
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσx : σ' x ≠ σ x) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
            : ManyBodyOpS Λ N) σ' σ +
          (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
            : ManyBodyOpS Λ N) σ' σ) := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_x
    hxy h hσx]
  ring

/-- Symmetric (vanishes by `σ' y ≠ σ y`). -/
theorem spinSDot_apply_eq_pm_only_of_off_diag_at_y
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσy : σ' y ≠ σ y) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
            : ManyBodyOpS Λ N) σ' σ +
          (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
            : ManyBodyOpS Λ N) σ' σ) := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_y
    hxy h hσy]
  ring

/-- **Explicit off-diagonal `Ŝ_x · Ŝ_y` matrix element** on a two-site
raising/lowering pair. For `x ≠ y` and `σ', σ` agreeing off `{x, y}`
with the raising shift at `x` (`σ_x = σ'_x + 1`) and lowering shift at
`y` (`σ_y + 1 = σ'_y`), the matrix element equals
`(1/2) · √(σ_x · (N - σ_x + 1)) · √((N - σ_y) · (σ_y + 1))`,
a positive real number.

The `S^3 ⊗ S^3` part vanishes (off-diagonal in `S^3`); the
`S^-_x ⊗ S^+_y` part vanishes (wrong direction at `x`); only the
`S^+_x ⊗ S^-_y` term contributes. -/
theorem spinSDot_apply_eq_raising_lowering_explicit
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((Real.sqrt (((σ x).val : ℝ) *
            ((N : ℝ) - (σ x).val + 1)) : ℝ) *
          (Real.sqrt (((N : ℝ) - (σ y).val) *
            ((σ y).val + 1)) : ℝ)) := by
  have hσx : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_x hxy N h hσx]
  -- Now we have (1/2) * ((S+_x S-_y) σ' σ + (S-_x S+_y) σ' σ).
  -- (S-_x S+_y) σ' σ = 0 from raising at x.
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_raising_x
    hxy h hx]
  -- (S+_x S-_y) σ' σ = (S+)(σ'x σx) * (S-)(σ'y σy).
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpPlus_apply_raise N hx, spinSOpMinus_apply_lower N hy]
  push_cast
  ring

/-- Symmetric: lowering at `x` and raising at `y`. -/
theorem spinSDot_apply_eq_lowering_raising_explicit
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (hy : (σ' y).val + 1 = (σ y).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (1 / 2 : ℂ) *
        ((Real.sqrt (((N : ℝ) - (σ x).val) *
            ((σ x).val + 1)) : ℝ) *
          (Real.sqrt (((σ y).val : ℝ) *
            ((N : ℝ) - (σ y).val + 1)) : ℝ)) := by
  have hσx : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_x hxy N h hσx]
  -- (S+_x S-_y) σ' σ = 0 from lowering at x (S+ wrong direction).
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_lowering_x
    hxy h hx]
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpMinus_apply_lower N hx, spinSOpPlus_apply_raise N hy]
  push_cast
  ring


/-- Symmetric: for `x ≠ y` and configurations `σ', σ` agreeing off
`{x, y}`, the matrix element of `Ŝ_x · Ŝ_y` has non-negative real
part on the lowering/raising pair `(σ x).val + 1 = (σ' x).val`. -/
theorem spinSDot_apply_re_nonneg_of_raising_lowering_y
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    0 ≤ ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).re := by
  rw [spinSDot_apply_eq_pm_3]
  rw [Matrix.add_apply, Complex.add_re]
  rw [Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  rw [Matrix.add_apply, Complex.add_re]
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    (Λ := Λ) hxy σ' σ
  have h12re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have h12im : ((1 / 2 : ℂ)).im = 0 := by norm_num
  rw [h12re, h12im, zero_mul, sub_zero]
  have hσ'x : σ' x ≠ σ x := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  have h3eq : (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
      : ManyBodyOpS Λ N) σ' σ = 0 := by
    rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
    rw [show spinSOp3 N (σ' x) (σ x) = 0 from
      Matrix.diagonal_apply_ne _ hσ'x]
    ring
  rw [h3eq]
  simp
  positivity


/-- **One-site difference vanishing**: for `x ≠ y` and configurations
`σ', σ` agreeing off a single site `z`, the matrix element of
`Ŝ_x · Ŝ_y` vanishes. (Two-site operators cannot connect
single-site differences — magnetization conservation at the
matrix-element level.)

Cases:
- `z ∉ {x, y}`: the off-pair difference site forces vanishing.
- `z ∈ {x, y}`: σ' σ agree at the *other* site of `{x, y}`, but
  S^- and S^+ have no diagonal entries, and S^3_z has off-diagonal
  zero, so all three axis terms vanish. -/
theorem spinSDot_apply_eq_zero_of_one_site_diff
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  by_cases hzx : z = x
  · subst hzx
    have hy : σ' y = σ y := hagree y (Ne.symm hxy)
    have h2agree : ∀ k, k ≠ z → k ≠ y → σ' k = σ k := fun k hkz _ => hagree k hkz
    rw [spinSDot_apply_of_off_two_site_agree hxy N h2agree]
    rw [show spinSOp1 N (σ' z) (σ z) * spinSOp1 N (σ' y) (σ y) =
        spinSOp1 N (σ' z) (σ z) * 0 from by
      rw [hy, spinSOp1_apply_diag]]
    rw [show spinSOp2 N (σ' z) (σ z) * spinSOp2 N (σ' y) (σ y) =
        spinSOp2 N (σ' z) (σ z) * 0 from by
      rw [hy, spinSOp2_apply_diag]]
    rw [show spinSOp3 N (σ' z) (σ z) * spinSOp3 N (σ' y) (σ y) =
        0 * spinSOp3 N (σ' y) (σ y) from by
      rw [show spinSOp3 N (σ' z) (σ z) = 0 from
        Matrix.diagonal_apply_ne _ hz]]
    ring
  · by_cases hzy : z = y
    · subst hzy
      have hx : σ' x = σ x := hagree x hxy
      have h2agree : ∀ k, k ≠ x → k ≠ z → σ' k = σ k := fun k _ hkz => hagree k hkz
      rw [spinSDot_apply_of_off_two_site_agree hxy N h2agree]
      rw [show spinSOp1 N (σ' x) (σ x) * spinSOp1 N (σ' z) (σ z) =
          0 * spinSOp1 N (σ' z) (σ z) from by
        rw [hx, spinSOp1_apply_diag]]
      rw [show spinSOp2 N (σ' x) (σ x) * spinSOp2 N (σ' z) (σ z) =
          0 * spinSOp2 N (σ' z) (σ z) from by
        rw [hx, spinSOp2_apply_diag]]
      rw [show spinSOp3 N (σ' x) (σ x) * spinSOp3 N (σ' z) (σ z) =
          spinSOp3 N (σ' x) (σ x) * 0 from by
        rw [show spinSOp3 N (σ' z) (σ z) = 0 from
          Matrix.diagonal_apply_ne _ hz]]
      ring
    · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy N hzx hzy hz

/-- For `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}` with
`σ' ≠ σ`, the spinSDot matrix element of any pair `(x', y')` with
`x' ≠ y'` and `x'` outside `{x, y}` vanishes. (The non-zero
off-diagonal entries of `Ŝ_x · Ŝ_y` are confined to the supporting
two-site set.) -/
theorem spinSDot_apply_eq_zero_of_x_outside_pair
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    {x' y' : Λ} (hxy' : x' ≠ y')
    (hxx' : x' ≠ x) (hyx' : x' ≠ y) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  by_cases hxd : σ' x = σ x
  · by_cases hyd : σ' y = σ y
    · exfalso
      apply hne
      funext k
      by_cases hkx : k = x
      · subst hkx; exact hxd
      · by_cases hky : k = y
        · subst hky; exact hyd
        · exact h k hkx hky
    · by_cases hyy' : y = y'
      · have hagree : ∀ k, k ≠ y' → σ' k = σ k := fun k hk => by
          subst hyy'
          by_cases hkx : k = x
          · subst hkx; exact hxd
          · exact h k hkx hk
        exact spinSDot_apply_eq_zero_of_one_site_diff hxy' N hagree
          (hyy' ▸ hyd)
      · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N
          (Ne.symm hyx') hyy' hyd
  · by_cases hxy2 : x = y'
    · by_cases hyd : σ' y = σ y
      · have hagree : ∀ k, k ≠ y' → σ' k = σ k := fun k hk => by
          subst hxy2
          by_cases hky : k = y
          · subst hky; exact hyd
          · exact h k hk hky
        exact spinSDot_apply_eq_zero_of_one_site_diff hxy' N hagree
          (hxy2 ▸ hxd)
      · have hyy' : y ≠ y' := fun heq => hxy.symm (heq.trans hxy2.symm)
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N
          (Ne.symm hyx') hyy' hyd
    · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N
        (Ne.symm hxx') (Ne.symm fun heq => hxy2 heq.symm) hxd

/-- Symmetric: `y'` outside `{x, y}` also vanishes (using `spinSDot_comm`). -/
theorem spinSDot_apply_eq_zero_of_y_outside_pair
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    {x' y' : Λ} (hxy' : x' ≠ y')
    (hxy'' : y' ≠ x) (hyy' : y' ≠ y) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [show (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ =
      (spinSDot y' x' N : ManyBodyOpS Λ N) σ' σ from by
    rw [spinSDot_comm]]
  exact spinSDot_apply_eq_zero_of_x_outside_pair hxy N hne h
    (Ne.symm hxy') hxy'' hyy'

/-- For `x' ≠ y'`, if there are three pairwise-distinct sites
`z₁, z₂, z₃` where `σ', σ` differ, the spinSDot matrix element
vanishes (pigeonhole: at least one of the three is outside `{x', y'}`). -/
theorem spinSDot_apply_eq_zero_of_three_diff
    {x' y' : Λ} (hxy' : x' ≠ y') (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z₁ z₂ z₃ : Λ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  -- Find a zᵢ outside {x', y'}; pigeonhole on the 2-element set.
  by_cases h1x : z₁ = x'
  · by_cases h1y : z₁ = y'
    · -- z₁ = x' and z₁ = y' contradicts hxy'.
      exact (hxy' (h1x.symm.trans h1y)).elim
    · -- z₁ = x' but z₁ ≠ y'. So if z₂ = x', then z₂ = z₁, contradicting h12.
      -- So z₂ ≠ x'. Now case on z₂ = y'.
      have h2x : z₂ ≠ x' := fun heq => h12 (h1x.trans heq.symm)
      by_cases h2y : z₂ = y'
      · -- z₁ = x' and z₂ = y'. Now z₃ ∉ {x', y'} (else z₃ = z₁ or z₂).
        have h3x : z₃ ≠ x' := fun heq => h13 (h1x.trans heq.symm)
        have h3y : z₃ ≠ y' := fun heq => h23 (h2y.trans heq.symm)
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h3x h3y hz3
      · -- z₂ ∉ {x', y'}.
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h2x h2y hz2
  · by_cases h1y : z₁ = y'
    · -- z₁ = y'.
      have h2y : z₂ ≠ y' := fun heq => h12 (h1y.trans heq.symm)
      by_cases h2x : z₂ = x'
      · -- z₁ = y' and z₂ = x'. z₃ ∉ {x', y'}.
        have h3x : z₃ ≠ x' := fun heq => h23 (h2x.trans heq.symm)
        have h3y : z₃ ≠ y' := fun heq => h13 (h1y.trans heq.symm)
        exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h3x h3y hz3
      · exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h2x h2y hz2
    · -- z₁ ∉ {x', y'}.
      exact spinSDot_apply_eq_zero_of_diff_outside_pair hxy' N h1x h1y hz1

/-- **Combined off-pair vanishing**: for `x ≠ y`, `σ', σ` agreeing
off `{x, y}` with `σ' ≠ σ`, and `(x', y')` not equal to `(x, y)` or
`(y, x)`, the spinSDot matrix element vanishes.

Cases: `x' = y'` gives the same-site Casimir vanishing on `σ' ≠ σ`;
otherwise at least one of `x', y'` is outside `{x, y}` (since
`{x', y'} ⊆ {x, y}` and `x' ≠ y'` would force `(x', y') ∈
{(x, y), (y, x)}`), so the corresponding outside-pair lemma applies. -/
theorem spinSDot_apply_eq_zero_of_pair_not_xy_or_yx
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (x' y' : Λ)
    (hpair : ¬ ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x))) :
    (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 := by
  by_cases hxy' : x' = y'
  · subst hxy'
    have ⟨z, hz⟩ : ∃ z, σ' z ≠ σ z := Function.ne_iff.mp hne
    exact spinSDot_self_apply_eq_zero_of_diff_at x' N hz
  · -- x' ≠ y'. At least one of x', y' is outside {x, y} (else (x',y') would
    -- be (x,y) or (y,x), which is excluded).
    by_cases hxx' : x' = x
    · -- x' = x; then y' ≠ y (else hpair would be Or.inl). And y' ≠ x' = x (hxy').
      have hyy : y' ≠ y := fun heq => hpair (Or.inl ⟨hxx', heq⟩)
      have hyx : y' ≠ x := fun heq => hxy' (hxx'.trans heq.symm)
      exact spinSDot_apply_eq_zero_of_y_outside_pair hxy N hne h hxy' hyx hyy
    · by_cases hxy2 : x' = y
      · -- x' = y; then y' ≠ x (else hpair would be Or.inr). And y' ≠ y (hxy').
        have hyx : y' ≠ x := fun heq => hpair (Or.inr ⟨hxy2, heq⟩)
        have hyy : y' ≠ y := fun heq => hxy' (hxy2.trans heq.symm)
        exact spinSDot_apply_eq_zero_of_y_outside_pair hxy N hne h hxy' hyx hyy
      · -- x' ∉ {x, y}; use x_outside.
        exact spinSDot_apply_eq_zero_of_x_outside_pair hxy N hne h hxy' hxx' hxy2

/-- **spinSDot vanishing on non-`±1` differences at `x`**: for `x ≠ y`
and configurations `σ', σ` agreeing off `{x, y}` such that `σ', σ`
differ at `x` by an amount other than `±1` (i.e., neither raising nor
lowering by one step), the matrix element vanishes.

The `S^+_x ⊗ S^-_y` term vanishes (since `S^+(σ' x, σ x) = 0` requires
`(σ' x).val + 1 = (σ x).val`); the `S^-_x ⊗ S^+_y` term vanishes
(since `S^-(σ' x, σ x) = 0` requires `(σ x).val + 1 = (σ' x).val`);
the `S^3_x ⊗ S^3_y` term vanishes (since `σ' x ≠ σ x` forces
`S^3(σ' x, σ x) = 0`). -/
theorem spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hne : σ' x ≠ σ x)
    (hp : (σ' x).val + 1 ≠ (σ x).val)
    (hm : (σ x).val + 1 ≠ (σ' x).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_x hxy N h hne]
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    hxy h]
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpPlus_apply_other N hp]
  rw [spinSOpMinus_apply_other N hm]
  ring

/-- Symmetric: spinSDot vanishes when the difference at `y` is not
`±1`. -/
theorem spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
    {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hne : σ' y ≠ σ y)
    (hp : (σ' y).val + 1 ≠ (σ y).val)
    (hm : (σ y).val + 1 ≠ (σ' y).val) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [spinSDot_apply_eq_pm_only_of_off_diag_at_y hxy N h hne]
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    hxy h]
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    hxy h]
  rw [spinSOpMinus_apply_other N hm]
  rw [spinSOpPlus_apply_other N hp]
  ring

end LatticeSystem.Quantum
