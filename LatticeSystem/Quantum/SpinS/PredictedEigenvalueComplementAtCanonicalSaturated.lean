import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceReComplement
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Complement predicted `(Ŝ_tot)²` eigenvalue value at canonical-saturated `|¬A| = 0`

PR #2955 gave the signed complement form
`complement_eigenvalue.re = biw.re·(biw.re − 1)`. At canonical-saturated
`|¬A| = 0`, `biw.re = (|Λ| − 0)·N/2 = m_max`, so

  `complement_eigenvalue.re = m_max·(m_max − 1)`
  at `|¬A| = 0`.

This is the **alternative** eigenvalue (NOT the ferromagnetic
`m_max·(m_max+1)`). The complement orientation `(s_B − s_A)` at the
canonical-saturated edge gives a "wrong-sign" effective `S_tot`
interpretation: at `|¬A| = 0`, `s_B − s_A = −m_max < 0` is unphysical
as `S_tot`. The canonical form (PR #2938) gives the correct
ferromagnetic value `m_max·(m_max+1)`.

Mirror of PR #2958 (canonical at complement-saturated). Useful for
showing the complement predicted GS at canonical-saturated has Casimir
strictly below the fully-polarised ferromagnetic value — wrong
orientation at this edge.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Complement predicted (Ŝ_tot)² eigenvalue at canonical-saturated `|¬A| = 0`**:
`complement_eigenvalue.re = m_max·(m_max − 1)` (not the ferromagnetic
`m_max·(m_max+1)`). Mirror of PR #2958 in the "wrong" orientation. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_pred_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 - 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
        A N, bipartiteImbalanceWeight_re_eq]
  -- At |¬A| = 0: biw.re = (|Λ| - 0)·N/2 = |Λ|·N/2 = m_max.
  have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hA_eq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    have : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
      exact_mod_cast h
    linarith
  rw [hA_eq]
  push_cast [h]
  ring

end LatticeSystem.Quantum
