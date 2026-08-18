import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Negative control: the cofactor (quotient) lemma genuinely needs `q ≠ 0`

`LatticeSystem.Math.isWeightedHomogeneous_cofactor_weight` reads

  `hq : q.IsWeightedHomogeneous w k`, `hq0 : q ≠ 0`, `hqr : (q * r).IsWeightedHomogeneous w n` ⊢
  `∀ d ∈ r.support, k + Finsupp.weight w d = n`.

This file is a standalone counterexample (it deliberately does not import that lemma) showing the
conclusion genuinely fails when `hq0` is dropped: `q = 0` makes both homogeneity hypotheses hold
vacuously for *any* `k` and `n` (`isWeightedHomogeneous_zero`), so `hq0` is not a decorative
hypothesis but one the proof must actually consume.
-/

open MvPolynomial

namespace LatticeSystem.Tests.GradedPolynomialLayerNegativeControl

/-- The standard total-degree weight on a single variable. -/
def w : Fin 1 → ℕ := fun _ => 1

/-- Without `hq0 : q ≠ 0`, the would-be cofactor conclusion `k + weight w d = n` can fail even
though both homogeneity hypotheses hold: take `q = 0`, `k = 5`, `r = X 0`, `n = 100`. Then
`q` is (vacuously) weighted-homogeneous of degree `5`, `q * r = 0` is (vacuously)
weighted-homogeneous of degree `100`, `d := single 0 1 ∈ r.support`, but
`5 + weight w d = 6 ≠ 100`. -/
example :
    (0 : MvPolynomial (Fin 1) ℂ).IsWeightedHomogeneous w 5 ∧
      ((0 : MvPolynomial (Fin 1) ℂ) * X 0).IsWeightedHomogeneous w 100 ∧
      Finsupp.single (0 : Fin 1) 1 ∈ (X 0 : MvPolynomial (Fin 1) ℂ).support ∧
      ¬ (5 + Finsupp.weight w (Finsupp.single (0 : Fin 1) 1) = 100) := by
  refine ⟨isWeightedHomogeneous_zero ℂ w 5, ?_, ?_, ?_⟩
  · simpa using isWeightedHomogeneous_zero ℂ w 100
  · simp
  · simp [Finsupp.weight_single, w]

end LatticeSystem.Tests.GradedPolynomialLayerNegativeControl
