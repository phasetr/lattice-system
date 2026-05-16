import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReViaEigenvalue
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMinEqCanonical

/-!
# Predicted min energy at complement orientation: via min eigenvalue

PR #2994: `(predicted_min_energy).re = canonical_eigenvalue.re
  − Re(s_A·(s_A+1)) − Re(s_B·(s_B+1))`.

At complement orientation `|A| ≤ |¬A|`, `canonical = min` (PR #2986).
Substituting:

  `(predicted_min_energy).re = min(canonical, complement)
     − Re(s_A·(s_A+1)) − Re(s_B·(s_B+1))`
  at `|A| ≤ |¬A|`.

At complement orientation, the canonical-formula `bipartiteToyMinEnergyPredicted A N`
uses the **`min`** (smaller) eigenvalue, giving an underestimate of the
"true" predicted min energy. The complement-orientation `bipartiteToyMinEnergyPredicted (¬A) N`
gives the correct physical value.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Predicted min energy via min eigenvalue at complement orientation**:
`(predicted_min_energy).re = min(canonical, complement) − Re(s_A·(s_A+1))
  − Re(s_B·(s_B+1))` at `|A| ≤ |¬A|`. Companion of PR #2995. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_min_eigenvalue_re_sub_sublattice_casimir_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      min
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
  exact (bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_canonical_of_cardA_le_cardNotA
    A N horient).symm

end LatticeSystem.Quantum
