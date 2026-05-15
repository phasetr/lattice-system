import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Canonical predicted `(Ŝ_tot)²` eigenvalue value at complement-saturated `|A| = 0`

PR #2932 gave the signed canonical form `eigenvalue.re = biw.re·(biw.re + 1)`.
At complement-saturated `|A| = 0`, `biw.re = (0 − |Λ|)·N/2 = −m_max`, so

  `canonical_eigenvalue.re = (−m_max)·(−m_max + 1) = m_max·(m_max − 1)`
  at `|A| = 0`.

This is the **alternative** eigenvalue (NOT the ferromagnetic
`m_max·(m_max+1)`). The canonical orientation `(s_A − s_B)` at the
complement-saturated edge gives a "wrong-sign" effective `S_tot`
interpretation: at `|A| = 0`, `s_A − s_B = −m_max < 0` is unphysical
as `S_tot`. The complement form (PR #2941) gives the correct
ferromagnetic value `m_max·(m_max+1)`.

Mirror of PR #2938 in the "wrong" orientation. Useful for showing
that the canonical predicted GS at complement-saturated has Casimir
strictly below the fully-polarised ferromagnetic value (i.e., the
canonical orientation is wrong at this edge).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Canonical predicted (Ŝ_tot)² eigenvalue at complement-saturated `|A| = 0`**:
`eigenvalue.re = m_max·(m_max − 1)` (not the ferromagnetic
`m_max·(m_max+1)`). Mirror of PR #2938 in the "wrong" orientation. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_pred_of_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 - 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N, bipartiteImbalanceWeight_re_eq]
  -- At |A| = 0: biw.re = (0 - |Λ|)·N/2 = -|Λ|·N/2 = -m_max.
  have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hAc_eq : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
      exact_mod_cast h
    linarith
  rw [hAc_eq]
  push_cast [h]
  ring

end LatticeSystem.Quantum
