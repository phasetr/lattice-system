import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapAdjointInput

/-!
# Tasaki Problem 2.5.c: axis-swap equal-axis wrapper

This module combines the algebraic Problem 2.5.c bridge from
`Problem25cSingleSiteSquared.lean` with the lifted axis-swap equality from
`Problem25cAxisSwapAdjointInput.lean`.  If a normalized state is fixed by the
inverse lifted axis swap and the remaining axis-1/axis-2 equality is supplied,
then all three squared single-site expectations have the value `N(N+2)/12`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Axis-swap plus one remaining equality -/

/-- Problem 2.5.c reduction using lifted axis-swap invariance: normalization,
axis-swap invariance, and the remaining axis-1/axis-2 equality imply the
`N(N+2)/12` value for all three squared single-site axes. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_axis1_eq_axis2
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ)
    (h12 : singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  have h32 :
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
    singleSiteSpinSquareExpectationS_axis3_eq_axis2_of_axisSwapInvariant x Φ hΦswap
  have h13 : singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ := by
    rw [h12, h32]
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_axes_equal_normalized
    (x := x) hΦnorm h12 h13

end LatticeSystem.Quantum
