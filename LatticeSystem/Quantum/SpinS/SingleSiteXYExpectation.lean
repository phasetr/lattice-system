import LatticeSystem.Quantum.SpinS.Problem25cSingleSiteSquared
import LatticeSystem.Quantum.SpinS.SingleSiteZExpectation

/-!
# Single-site xy-plane squared expectation on all-aligned states

This module records the xy-plane part of the single-site Casimir on the
all-aligned state `|c..c⟩`.  It is a direct subtraction of the explicit
z-axis square expectation from the universal single-site Casimir value.

This is background for Tasaki Problem 2.5.c: non-SU(2)-symmetric saturated
states split the single-site Casimir unevenly across axes, whereas the AFM
ground-state symmetry input will force equal axis values.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- On an all-aligned state, the xy-plane squared single-site expectation is
the universal single-site Casimir value minus the z-axis square expectation:
`N(N+2)/4 - (N/2 - c)^2`. -/
theorem allAlignedStateS_expectation_onSiteS_spinSOp1_sq_add_spinSOp2_sq
    (x : V) (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      ((((onSiteS x (spinSOp1 N) : ManyBodyOpS V N) * onSiteS x (spinSOp1 N)) +
        ((onSiteS x (spinSOp2 N) : ManyBodyOpS V N) * onSiteS x (spinSOp2 N))).mulVec
          (allAlignedStateS V N c)) =
      (N : ℂ) * (N + 2) / 4 -
        (((N : ℂ) / 2 - (c.val : ℂ)) * ((N : ℂ) / 2 - (c.val : ℂ))) := by
  let Φ : (V → Fin (N + 1)) → ℂ := allAlignedStateS V N c
  let e1 := singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ
  let e2 := singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ
  let e3 := singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ
  have hleft :
      dotProduct (star Φ)
        ((((onSiteS x (spinSOp1 N) : ManyBodyOpS V N) * onSiteS x (spinSOp1 N)) +
          ((onSiteS x (spinSOp2 N) : ManyBodyOpS V N) * onSiteS x (spinSOp2 N))).mulVec Φ) =
        e1 + e2 := by
    unfold e1 e2 singleSiteSpinSquareExpectationS
    rw [Matrix.add_mulVec, dotProduct_add]
  have hsum : e1 + e2 + e3 = (N : ℂ) * (N + 2) / 4 := by
    exact singleSiteSpinSquareExpectationS_axis_sum_normalized x
      (allAlignedStateS_inner_self c)
  have hz :
      e3 = ((N : ℂ) / 2 - (c.val : ℂ)) * ((N : ℂ) / 2 - (c.val : ℂ)) := by
    simpa [e3, singleSiteSpinSquareExpectationS, Φ]
      using allAlignedStateS_expectation_onSiteS_spinSOp3_sq (x := x) (c := c)
  calc
    dotProduct (star (allAlignedStateS V N c))
        ((((onSiteS x (spinSOp1 N) : ManyBodyOpS V N) * onSiteS x (spinSOp1 N)) +
          ((onSiteS x (spinSOp2 N) : ManyBodyOpS V N) * onSiteS x (spinSOp2 N))).mulVec
            (allAlignedStateS V N c)) =
        e1 + e2 := by simpa [Φ] using hleft
    _ = (e1 + e2 + e3) - e3 := by ring
    _ = (N : ℂ) * (N + 2) / 4 -
        (((N : ℂ) / 2 - (c.val : ℂ)) * ((N : ℂ) / 2 - (c.val : ℂ))) := by
      rw [hsum, hz]

end LatticeSystem.Quantum
