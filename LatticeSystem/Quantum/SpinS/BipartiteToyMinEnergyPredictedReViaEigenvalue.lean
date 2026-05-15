import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalEqSquareAdd

/-!
# `(bipartiteToyMinEnergyPredicted A N).re = canonical_eigenvalue.re − s_A(s_A+1) − s_B(s_B+1)`

The predicted minimum energy decomposes as:

  `predicted_min_energy.re = canonical_eigenvalue.re
     − Re(s_A·(s_A+1)) − Re(s_B·(s_B+1))`.

Direct from the definition `bipartiteToyMinEnergyPredicted = (s_A − s_B)·((s_A − s_B) + 1)
− s_A·(s_A+1) − s_B·(s_B+1)` and the fact that `s_A, s_B` are real.

This makes explicit the relationship between the predicted minimum energy
of `H_toy` and the canonical predicted `(Ŝ_tot)²` eigenvalue.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Predicted min energy via canonical eigenvalue**:
`(predicted_min_energy).re = canonical_eigenvalue.re
   − Re(s_A·(s_A+1)) − Re(s_B·(s_B+1))`. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_canonical_eigenvalue_re_sub_sublattice_casimir
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re -
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re := by
  unfold bipartiteToyMinEnergyPredicted
  simp only [Complex.sub_re]

end LatticeSystem.Quantum
