import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapEqualAxes

/-!
# Tasaki Problem 2.5.c: two-symmetry axis input

This module combines the lifted axis-swap input from
`Problem25cAxisSwapEqualAxes.lean` with a second abstract unitary-symmetry input
for the remaining axis-1/axis-2 equality.  The concrete SU(2) or ground-state
symmetry theorem remains an explicit hypothesis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Remaining axis equality from a unitary input -/

/-- A second abstract unitary symmetry gives the remaining axis-1/axis-2
squared single-site expectation equality. -/
theorem singleSiteSpinSquareExpectationS_axis1_eq_axis2_of_unitaryInvariant
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (T Tinv : ManyBodyOpS V N)
    (hTadj : T.conjTranspose = Tinv)
    (hTinvT : Tinv * T = 1)
    (hΦ : Tinv.mulVec Φ = Φ)
    (hconj : T * onSiteS x (spinSOp2 N) * Tinv = onSiteS x (spinSOp1 N)) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
  singleSiteSpinSquareExpectationS_eq_of_conj_invariant
    (x := x) (A := spinSOp2 N) (B := spinSOp1 N)
    (T := T) (Tinv := Tinv) (Φ := Φ) hTadj hTinvT hΦ hconj

/-! ## Axis-swap plus the second unitary input -/

/-- Problem 2.5.c reduction with two explicit symmetry inputs: lifted axis-swap
invariance supplies the axis-2/axis-3 equality, while a second abstract unitary
symmetry supplies the remaining axis-1/axis-2 equality. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_unitary_axis12
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (T Tinv : ManyBodyOpS V N)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ)
    (hTadj : T.conjTranspose = Tinv)
    (hTinvT : Tinv * T = 1)
    (hΦT : Tinv.mulVec Φ = Φ)
    (hconj : T * onSiteS x (spinSOp2 N) * Tinv = onSiteS x (spinSOp1 N)) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  have h12 :
      singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
    singleSiteSpinSquareExpectationS_axis1_eq_axis2_of_unitaryInvariant
      x T Tinv hTadj hTinvT hΦT hconj
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_axis1_eq_axis2
    (x := x) hΦnorm hΦswap h12

end LatticeSystem.Quantum
