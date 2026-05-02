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

end LatticeSystem.Quantum
