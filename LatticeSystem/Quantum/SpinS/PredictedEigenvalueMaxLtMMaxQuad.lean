import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxEqMMaxQuadIff
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxMemIcc

/-!
# Unified strict max bound: `max(canonical, complement) < m_max·(m_max+1)` at non-saturated

PR #2970: `max(canonical, complement) = m_max·(m_max+1) ↔ saturated edge`
at `N ≥ 1`. Taking contrapositive, at non-saturated (`|A| ≥ 1` AND
`|¬A| ≥ 1`) and `N ≥ 1`,

  `max(canonical, complement) < m_max·(m_max+1)`.

Combined with the unconditional upper bound (PR #2972).

The physical predicted (Ŝ_tot)² eigenvalue is strictly below the
fully-polarised ferromagnetic value at non-saturated edges — the
predicted GS is not the maximum-spin multiplet. Unifies PR #2945 /
PR #2946 (orientation-specialised strict bounds at non-degenerate) via
the physical max quantity.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified strict max bound**: `max(canonical, complement) <
m_max·(m_max+1)` at non-saturated (`|A| ≥ 1`, `|¬A| ≥ 1`), `N ≥ 1`.
Contrapositive of PR #2970 combined with PR #2972. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_lt_mMax_quad_of_non_saturated
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
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
                  ((N : ℂ) / 2)) + 1)).re <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  have hle :=
    (bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_mem_Icc
      A N).2
  by_contra hge
  push Not at hge
  have heq : _ = _ := le_antisymm hle hge
  have hsat :=
    (bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_mMax_quad_iff_saturated
      A N hN).mp heq
  rcases hsat with hA0 | hAc0
  · exact (Nat.pos_iff_ne_zero.mp hA) hA0
  · exact (Nat.pos_iff_ne_zero.mp hAc) hAc0

end LatticeSystem.Quantum
