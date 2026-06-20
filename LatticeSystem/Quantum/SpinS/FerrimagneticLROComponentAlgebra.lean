import LatticeSystem.Quantum.SpinS.FerrimagneticLRO
import LatticeSystem.Quantum.SpinS.DysonLiebSimon
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Math.PosSemidef.Basics

/-!
# Tasaki §4.1 (Theorem 4.4): the operator-algebra core of the proof chain (4.1.16)

This file collects the self-contained operator-algebra steps of Tasaki's finite-volume proof of
Theorem 4.4 (Shen–Qiu–Tian ferrimagnetic long-range order) that do **not** depend on the
total-spin value (Theorem 2.3 / Lieb–Mattis) nor on ground-state minimality.  These are the
manifestly `SU(2)`-invariant rewrites and positivity facts feeding the chain (4.1.16); the
value-dependent steps (Lieb–Mattis total spin, `⟨(Ŝ_tot)²⟩ = S_tot(S_tot+1) ≥ S_tot²`) are
assembled later in the capstone PR that discharges the axiom `shenQiuTian_ferrimagnetic_lro`.

The squared staggered order operator `(Ô_Λ)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y`
(`staggeredCasimirOpS`, eq. (4.1.12)) splits into a *transverse* `(1,2)`-component part and the
square of the longitudinal staggered order operator `Ô_Λ^{(3)}` (`staggeredOrderOpS`):

  `(Ô_Λ)² = staggeredTransverseCasimirOpS + (Ô_Λ^{(3)})²`.

Since `(Ô_Λ^{(3)})²` is a Hermitian square it is positive semidefinite, so the transverse part is
a lower bound for `(Ô_Λ)²` in expectation.  In parallel, the Casimir invariant `(Ŝ_tot)²` minus
its longitudinal square `(Ŝ_tot^{(3)})²` equals the transverse total double sum, and on a vector
annihilated by `Ŝ_tot^{(3)}` the expectation of `(Ŝ_tot)²` reduces to that transverse part.
These are the `SU(2)`-invariance manipulations that let Tasaki replace component sums by
total-spin expectations.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78.
-/

namespace LatticeSystem.Quantum

open Matrix

open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **transverse part** of the squared staggered order operator,
`Σ_{x,y} ε_x ε_y (Ŝ_x^{(1)} Ŝ_y^{(1)} + Ŝ_x^{(2)} Ŝ_y^{(2)})` — i.e. the `(1,2)`-component
portion of `(Ô_Λ)²` (eq. (4.1.12)), obtained by dropping the longitudinal `(3,3)` term
`Ŝ_x^{(3)} Ŝ_y^{(3)}` from each spin–spin dot product. -/
noncomputable def staggeredTransverseCasimirOpS (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, ∑ y : Λ,
    ((if A x then (1 : ℂ) else (-1 : ℂ)) * (if A y then (1 : ℂ) else (-1 : ℂ))) •
      (spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N)

/-- **Transverse / longitudinal split of `(Ô_Λ)²`** (eq. (4.1.12)):
`staggeredCasimirOpS = staggeredTransverseCasimirOpS + (Ô_Λ^{(3)})²`,
where `Ô_Λ^{(3)} = staggeredOrderOpS`.  Expanding each `Ŝ_x · Ŝ_y` into its three components
and distributing the staggered scalar `ε_x ε_y`, the `(3,3)`-component double sum
`Σ_{x,y} ε_x ε_y Ŝ_x^{(3)} Ŝ_y^{(3)}` factors as `(Σ_x ε_x Ŝ_x^{(3)})(Σ_y ε_y Ŝ_y^{(3)})`, the
square of the longitudinal staggered order operator. -/
theorem staggeredCasimirOpS_eq_transverse_add_staggeredOrderOp_sq (A : Λ → Bool) (N : ℕ) :
    staggeredCasimirOpS A N =
      staggeredTransverseCasimirOpS A N + staggeredOrderOpS A N * staggeredOrderOpS A N := by
  classical
  -- Abbreviate the staggered sign `ε_x`.
  set ε : Λ → ℂ := fun x => if A x then (1 : ℂ) else (-1 : ℂ) with hε
  -- Step 1: split each scaled dot product into the transverse part plus the `(3,3)` term.
  have hsplit : staggeredCasimirOpS A N =
      staggeredTransverseCasimirOpS A N +
        ∑ x : Λ, ∑ y : Λ, (ε x * ε y) • (spinSSiteOp3 x N * spinSSiteOp3 y N) := by
    unfold staggeredCasimirOpS staggeredTransverseCasimirOpS
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [spinSDot_def, ← smul_add]
    -- `spinSDot` uses `onSiteS`; `spinSSiteOpα` is definitionally `onSiteS`, so this is `rfl`.
    rfl
  rw [hsplit]
  congr 1
  -- Step 2: the `(3,3)` double sum is the square of the longitudinal staggered order operator.
  unfold staggeredOrderOpS
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact (smul_mul_smul_comm (ε x) (spinSSiteOp3 x N) (ε y) (spinSSiteOp3 y N)).symm

/-- **Hermitian square positivity for the transverse bound.**  Since `Ô_Λ^{(3)}` is Hermitian,
its square is positive semidefinite, so `0 ≤ ⟨Φ, (Ô_Λ^{(3)})² Φ⟩.re` for every vector `Φ`. -/
theorem staggeredOrderOp_sq_expectation_nonneg (A : Λ → Bool) (N : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    0 ≤ (star Φ ⬝ᵥ (staggeredOrderOpS A N * staggeredOrderOpS A N).mulVec Φ).re := by
  have hps : (staggeredOrderOpS A N * staggeredOrderOpS A N).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (staggeredOrderOpS (Λ := Λ) A N)
    rwa [(staggeredOrderOpS_isHermitian A N).eq] at this
  exact (Complex.le_def.mp (hps.dotProduct_mulVec_nonneg Φ)).1

/-- **Transverse expectation lower bound for `(Ô_Λ)²`** (the positivity step feeding (4.1.16)).
The expectation of the transverse part is bounded above by the full squared staggered order
parameter, because the dropped longitudinal piece `(Ô_Λ^{(3)})²` is a positive-semidefinite
Hermitian square:
`⟨Φ, staggeredTransverseCasimirOpS Φ⟩.re ≤ ⟨Φ, (Ô_Λ)² Φ⟩.re`. -/
theorem staggeredTransverse_expectation_le_staggeredCasimir_expectation (A : Λ → Bool) (N : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (star Φ ⬝ᵥ (staggeredTransverseCasimirOpS A N).mulVec Φ).re ≤
      (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re := by
  rw [staggeredCasimirOpS_eq_transverse_add_staggeredOrderOp_sq, Matrix.add_mulVec,
    dotProduct_add, Complex.add_re]
  have h := staggeredOrderOp_sq_expectation_nonneg A N Φ
  linarith

/-- **Square of a total spin component as a double sum** (used in the Casimir expansion).
For each axis `α ∈ {1,2,3}`, `(Ŝ_tot^{(α)})² = Σ_{x,y} Ŝ_x^{(α)} Ŝ_y^{(α)}`, obtained by
expanding the product of the two single-site sums. -/
theorem totalSpinSOp1_sq_eq_double_sum (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    totalSpinSOp1 Λ N * totalSpinSOp1 Λ N =
      ∑ x : Λ, ∑ y : Λ, spinSSiteOp1 x N * spinSSiteOp1 y N := by
  unfold totalSpinSOp1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  rfl

/-- Square of `Ŝ_tot^{(2)}` as a double sum: `(Ŝ_tot^{(2)})² = Σ_{x,y} Ŝ_x^{(2)} Ŝ_y^{(2)}`. -/
theorem totalSpinSOp2_sq_eq_double_sum (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    totalSpinSOp2 Λ N * totalSpinSOp2 Λ N =
      ∑ x : Λ, ∑ y : Λ, spinSSiteOp2 x N * spinSSiteOp2 y N := by
  unfold totalSpinSOp2
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  rfl

/-- Square of `Ŝ_tot^{(3)}` as a double sum: `(Ŝ_tot^{(3)})² = Σ_{x,y} Ŝ_x^{(3)} Ŝ_y^{(3)}`. -/
theorem totalSpinSOp3_sq_eq_double_sum (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    totalSpinSOp3 Λ N * totalSpinSOp3 Λ N =
      ∑ x : Λ, ∑ y : Λ, spinSSiteOp3 x N * spinSSiteOp3 y N := by
  unfold totalSpinSOp3
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  rfl

/-- **Transverse total double sum as `(Ŝ_tot)² − (Ŝ_tot^{(3)})²`.**  Summing the three squared
component double sums gives the Casimir invariant `(Ŝ_tot)²`; subtracting the longitudinal `(3,3)`
double sum leaves the transverse `(1,1) + (2,2)` part:
`Σ_{x,y} (Ŝ_x^{(1)} Ŝ_y^{(1)} + Ŝ_x^{(2)} Ŝ_y^{(2)}) = (Ŝ_tot)² − (Ŝ_tot^{(3)})²`. -/
theorem noStaggeringTransverseSum_eq_totalSpinSSquared_sub_op3_sq (Λ : Type*) [Fintype Λ]
    [DecidableEq Λ] (N : ℕ) :
    (∑ x : Λ, ∑ y : Λ,
        (spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N)) =
      totalSpinSSquared Λ N - totalSpinSOp3 Λ N * totalSpinSOp3 Λ N := by
  rw [totalSpinSSquared_def, totalSpinSOp1_sq_eq_double_sum, totalSpinSOp2_sq_eq_double_sum,
    totalSpinSOp3_sq_eq_double_sum]
  rw [add_sub_cancel_right]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]

/-- **Vanishing of `(Ŝ_tot^{(3)})²` expectation on the kernel of `Ŝ_tot^{(3)}`.**  If
`Ŝ_tot^{(3)}` annihilates `Φ`, then `⟨Φ, (Ŝ_tot^{(3)})² Φ⟩.re = 0`, because the inner `mulVec`
already vanishes. -/
theorem totalSpinSOp3_sq_expectation_eq_zero_of_mulVec_eq_zero (Λ : Type*) [Fintype Λ]
    [DecidableEq Λ] (N : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (star Φ ⬝ᵥ ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec Φ)).re = 0 := by
  rw [← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re]

/-- **Reduction of the `(Ŝ_tot)²` expectation to its transverse part on the kernel of
`Ŝ_tot^{(3)}`.**  If `Ŝ_tot^{(3)}` annihilates `Φ`, then the expectation of the Casimir invariant
`(Ŝ_tot)²` equals the expectation of `(Ŝ_tot)² − (Ŝ_tot^{(3)})²`, since the subtracted
longitudinal square contributes nothing.  This is the `SU(2)`-invariance step that converts the
staggered transverse sum into a total-spin expectation in the chain (4.1.16). -/
theorem totalSpinSSquared_expectation_eq_transverse_of_op3_mulVec_eq_zero (Λ : Type*) [Fintype Λ]
    [DecidableEq Λ] (N : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (star Φ ⬝ᵥ (totalSpinSSquared Λ N).mulVec Φ).re =
      (star Φ ⬝ᵥ
        ((totalSpinSSquared Λ N - totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec Φ)).re := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    totalSpinSOp3_sq_expectation_eq_zero_of_mulVec_eq_zero Λ N Φ hΦ, sub_zero]

end LatticeSystem.Quantum
