import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSq

/-!
# Tasaki §4.2: factor-3 diagonal isotropy of the squared order operator `ô²`

This module records the **factor-3 diagonal isotropy** of the rotationally invariant squared order
operator `ô² = Σ_α (ô^{(α)})²` (`orderSqOp`) on a total-spin singlet state.  If `Φ` is annihilated
by the `3`-axis and `1`-axis total-spin generators (`Ŝ³_tot Φ = 0`, `Ŝ¹_tot Φ = 0`), the three
diagonal axis expectations coincide,

`⟨Φ, (ô^{(1)})² Φ⟩ = ⟨Φ, (ô^{(2)})² Φ⟩ = ⟨Φ, (ô^{(3)})² Φ⟩`,

so the full squared-order expectation collapses to three times the longitudinal one,

`⟨Φ, ô² Φ⟩ = 3 · ⟨Φ, (ô^{(3)})² Φ⟩`.

This is a pure wrapper: the two transverse/longitudinal singlet equalities
`staggeredOrder_sq_expectation_eq_12` (`⟨(ô¹)²⟩ = ⟨(ô²)²⟩`, from the `Ŝ³`-singlet) and
`staggeredOrder_sq_expectation_eq_23` (`⟨(ô²)²⟩ = ⟨(ô³)²⟩`, from the `Ŝ¹`-singlet) supply the
Lie-algebra mechanism; here they are merely chained through the `Fin 3` expansion of `orderSqOp`.
The factor `3` is load-bearing for the later collapse identification `⟨ô²⟩/(‖Φ‖²V²) → q₀ = (mStar)²`
(the conjectural `mStar = √(3qStar)` combined with Theorem 4.9 `mStar = √q₀`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.57)–(4.2.61), p.108–109.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Factor-3 diagonal isotropy of `ô²`** (Prop 4.10, eqs. (4.2.57)–(4.2.58)).  For a state `Φ`
annihilated by the `3`-axis and `1`-axis total-spin generators (`Ŝ³_tot Φ = 0`, `Ŝ¹_tot Φ = 0`),
the squared-order expectation equals three times the longitudinal expectation,

`⟨Φ, ô² Φ⟩ = 3 · ⟨Φ, (ô^{(3)})² Φ⟩`.

Expanding `ô² = (ô^{(1)})² + (ô^{(2)})² + (ô^{(3)})²` (`orderSqOp` over `Fin 3`) and using the
singlet component equalities `staggeredOrder_sq_expectation_eq_12` and
`staggeredOrder_sq_expectation_eq_23` to rewrite the transverse expectations into the longitudinal
one collapses the three diagonal terms to `3 ×` the `3`-axis term. -/
theorem orderSqOp_expectation_eq_three_mul_axis3
    (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    star Φ ⬝ᵥ (orderSqOp A N).mulVec Φ
      = 3 * (star Φ ⬝ᵥ (staggeredOrderOpS A N * staggeredOrderOpS A N).mulVec Φ) := by
  have hexpand : orderSqOp A N
      = staggeredOrderOp1S A N * staggeredOrderOp1S A N
        + staggeredOrderOp2S A N * staggeredOrderOp2S A N
        + staggeredOrderOpS A N * staggeredOrderOpS A N := by
    simp only [orderSqOp, Fin.sum_univ_three, stagOpVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, pow_two]
  rw [hexpand, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    staggeredOrder_sq_expectation_eq_12 A Φ h3, staggeredOrder_sq_expectation_eq_23 A Φ h1]
  ring

end LatticeSystem.Quantum
