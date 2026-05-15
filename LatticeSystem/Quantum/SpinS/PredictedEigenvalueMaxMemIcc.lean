import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxCanonicalComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax

/-!
# Range Icc: `max(canonical, complement) ∈ [0, m_max·(m_max+1)]` unconditionally

PR #2966: `max(canonical, complement) = ‖biw‖·(‖biw‖+1)`.

Since `0 ≤ ‖biw‖ ≤ m_max` unconditionally (norm + PR #2874), and
`x ↦ x·(x+1)` is monotonic increasing on `[0, ∞)`,

  `0 ≤ ‖biw‖·(‖biw‖+1) ≤ m_max·(m_max+1)`.

Hence

  `max(canonical, complement) ∈ Set.Icc 0 (m_max·(m_max+1))`
  unconditionally.

The **physical** predicted (max over orientations) `(Ŝ_tot)²` eigenvalue
lies in the closed interval `[0, m_max·(m_max+1)]` for any
configuration. Endpoints are attained: lower at balanced (PR #2855
gives ‖biw‖ = 0), upper at saturated edges (PR #2969 gives
‖biw‖ = m_max).

Unifies PR #2950 / PR #2952 (orientation-specialised range Icc) via the
physical max quantity.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Range Icc**: `max(canonical, complement) ∈ [0, m_max·(m_max+1)]`
unconditionally. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_mem_Icc
    (A : Λ → Bool) (N : ℕ) :
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
                  ((N : ℂ) / 2)) + 1)).re ∈
      Set.Icc (0 : ℝ)
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1)) := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
        A N]
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  have hbiw_le : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 :=
    bipartiteImbalanceWeight_norm_le_mMax A N
  refine ⟨?_, ?_⟩
  · nlinarith [hbiw_nn]
  · nlinarith [hbiw_nn, hbiw_le]

end LatticeSystem.Quantum
