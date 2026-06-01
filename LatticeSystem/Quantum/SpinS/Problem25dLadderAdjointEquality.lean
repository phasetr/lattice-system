import LatticeSystem.Quantum.SpinS.Problem25dLadderDotReduction

/-!
# Tasaki Problem 2.5.d: ladder adjoint equality

This module discharges the first component equality left by
`Problem25dLadderDotReduction.lean`.  The two ladder orientations are adjoints,
so their expectations have equal real parts after multiplication by the real
bipartite gauge sign.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 43, and solution pp. 498--499.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} {N : ℕ}

/-! ## Generic adjoint expectation bridge -/

/-- The expectation of the adjoint matrix is the complex conjugate of the
expectation. -/
theorem dotProduct_star_conjTranspose_mulVec_eq_star
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    dotProduct (star v) (M.conjTranspose.mulVec v) =
      star (dotProduct (star v) (M.mulVec v)) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.star_dotProduct]

/-! ## Two-site ladder adjoints -/

/-- The `S_x^+ S_y^-` two-site ladder operator has adjoint `S_x^- S_y^+`
on distinct sites. -/
theorem twoSpinPlusMinus_ladder_conjTranspose
    [Fintype V] [DecidableEq V] {x y : V} (hxy : x ≠ y) :
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) :
        ManyBodyOpS V N).conjTranspose =
      onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N) := by
  rw [Matrix.conjTranspose_mul, onSiteS_conjTranspose, onSiteS_conjTranspose,
    spinSOpMinus_conjTranspose, spinSOpPlus_conjTranspose,
    onSiteS_mul_onSiteS_of_ne hxy.symm]

/-- The `S_x^- S_y^+` expectation is the complex conjugate of the
`S_x^+ S_y^-` expectation on distinct sites. -/
theorem twoSpinMinusPlusCorrelationS_eq_star_twoSpinPlusMinusCorrelationS
    [Fintype V] [DecidableEq V] {x y : V} (hxy : x ≠ y)
    (Φ : (V → Fin (N + 1)) → ℂ) :
    twoSpinMinusPlusCorrelationS x y Φ =
      star (twoSpinPlusMinusCorrelationS x y Φ) := by
  unfold twoSpinMinusPlusCorrelationS twoSpinPlusMinusCorrelationS
  rw [← twoSpinPlusMinus_ladder_conjTranspose (N := N) hxy,
    dotProduct_star_conjTranspose_mulVec_eq_star]

/-- Multiplication by the cross-sublattice bipartite gauge sign preserves the
real-part equality between adjoint ladder expectations. -/
theorem bipartite_signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    (Φ : (V → Fin (N + 1)) → ℂ) :
    ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinMinusPlusCorrelationS x y Φ).re =
    ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y Φ).re := by
  rw [bipartiteGaugeSign_mul_eq_neg_one_of_ne A hAxy,
    twoSpinMinusPlusCorrelationS_eq_star_twoSpinPlusMinusCorrelationS hxy]
  simp

/-! ## Problem 2.5.d wrapper -/

/-- Conditional Problem 2.5.d package after the ladder-adjoint equality: for
cross-sublattice pairs, strictly positive Marshall coefficients and the
remaining longitudinal SU(2) component equality transfer the PR #4071 signed
ladder positivity to signed dot-product positivity. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_ladderAdjoint
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (c : (V → Fin (N + 1)) → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (hzz_eq :
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinZZCorrelationS x y
          (fun σ => marshallSignS A σ * (c σ : ℂ))).re =
      (1 / 2 : ℝ) * ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinPlusMinusCorrelationS x y
          (fun σ => marshallSignS A σ * (c σ : ℂ))).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (fun σ => marshallSignS A σ * (c σ : ℂ))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_components
    A hxy hAxy hN c hc_pos
    (bipartite_signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus
      A hxy hAxy (fun σ => marshallSignS A σ * (c σ : ℂ)))
    hzz_eq

end LatticeSystem.Quantum
