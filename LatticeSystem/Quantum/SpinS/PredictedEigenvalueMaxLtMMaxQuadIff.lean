import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxEqMMaxQuadIff
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxMemIcc

/-!
# Iff: `max(canonical, complement) < m_max·(m_max+1) ↔ non-saturated` at `N ≥ 1`

PR #2970: `max = m_max·(m_max+1) ↔ saturated edge` at `N ≥ 1`.
PR #2972: `max ∈ [0, m_max·(m_max+1)]` unconditionally.

Combining: at `N ≥ 1`, since `max ≤ m_max·(m_max+1)` always,
`max < m_max·(m_max+1) ↔ max ≠ m_max·(m_max+1) ↔ ¬ saturated edge`,
i.e.,

  `max(canonical, complement) < m_max·(m_max+1) ↔ |A| ≠ 0 ∧ |¬A| ≠ 0`
  at `N ≥ 1`.

The iff form of PR #2975's contrapositive.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff**: `max(canonical, complement) < m_max·(m_max+1) ↔
non-saturated** at `N ≥ 1`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_lt_mMax_quad_iff_non_saturated
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
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
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠ 0 ∧
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≠ 0 := by
  have hle :=
    (bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_mem_Icc
      A N).2
  have hiff_eq :=
    bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_mMax_quad_iff_saturated
      A N hN
  constructor
  · intro hlt
    by_contra hne
    rw [not_and_or] at hne
    rcases hne with hA0 | hAc0
    · have hA0' : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 :=
        not_not.mp hA0
      have heq : _ = _ := hiff_eq.mpr (Or.inl hA0')
      linarith
    · have hAc0' : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 :=
        not_not.mp hAc0
      have heq : _ = _ := hiff_eq.mpr (Or.inr hAc0')
      linarith
  · intro hns
    -- non-saturated ⟹ max < m_max(m_max+1) (combine ≤ with ≠).
    by_contra hge
    push Not at hge
    have heq : _ = _ := le_antisymm hle hge
    have := hiff_eq.mp heq
    rcases this with hA0 | hAc0
    · exact hns.1 hA0
    · exact hns.2 hAc0

end LatticeSystem.Quantum
