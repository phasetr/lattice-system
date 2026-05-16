import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReViaEigenvalue
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxEqCanonical

/-!
# Predicted min energy at proper orientation: via max eigenvalue

PR #2994: `(predicted_min_energy).re = canonical_eigenvalue.re
  − Re(s_A·(s_A+1)) − Re(s_B·(s_B+1))`.

At proper orientation `|¬A| ≤ |A|`, `canonical = max` (PR #2981).
Substituting:

  `(predicted_min_energy).re = max(canonical, complement)
     − Re(s_A·(s_A+1)) − Re(s_B·(s_B+1))`
  at `|¬A| ≤ |A|`.

The predicted min energy uses the **physical** (max) `(Ŝ_tot)²`
eigenvalue at proper orientation. The energy decomposition is the
universal Casimir-difference formula `H = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`
evaluated at the predicted joint spectrum.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Predicted min energy via max eigenvalue at proper orientation**:
`(predicted_min_energy).re = max(canonical, complement) − Re(s_A·(s_A+1))
  − Re(s_B·(s_B+1))` at `|¬A| ≤ |A|`. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_max_eigenvalue_re_sub_sublattice_casimir_of_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      max
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
              ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2)) + 1)).re
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
              ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2)) + 1)).re -
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyMinEnergyPredicted_re_eq_canonical_eigenvalue_re_sub_sublattice_casimir A N]
  congr 1
  congr 1
  exact (bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_canonical_of_cardNotA_le_cardA
    A N horient).symm

end LatticeSystem.Quantum
