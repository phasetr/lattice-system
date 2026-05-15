import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Unified upper bound: predicted `(Ŝ_tot)²` eigenvalue ≤ `m_max·(m_max + 1)`

PR #2932 gave the signed unified form (no orientation hypothesis):
`((s_A − s_B)·((s_A − s_B) + 1)).re = biw.re · (biw.re + 1)`.

The signed real value `biw.re = (|A| − |¬A|)·N/2` lies in
`[−m_max, m_max]` (PR #2874 gives `‖biw‖ ≤ m_max`, and biw has
imaginary part zero so `‖biw‖ = |biw.re|`). The parabola
`x ↦ x·(x+1)` is bounded above by `m_max·(m_max+1)` on
`[−m_max, m_max]`:

  `predicted (Ŝ_tot)² eigenvalue ≤ m_max·(m_max + 1)`
  unconditionally.

This unifies PR #2942 (at `|¬A| ≤ |A|`) and PR #2943 (at
`|A| ≤ |¬A|`, complement orientation) into a single orientation-free
statement on the `(s_A − s_B)` form, with PR #2932's signed bridge.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified upper bound on predicted (Ŝ_tot)² eigenvalue**:
≤ `m_max·(m_max + 1)` with no orientation hypothesis. Unifies PR #2942
and PR #2943 via PR #2932 (signed form) + `biw.re ∈ [−m_max, m_max]`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_le_mMax_quad
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N]
  -- ‖biw‖ ≤ m_max and biw.im = 0 ⟹ |biw.re| ≤ m_max.
  have hbiw_norm := bipartiteImbalanceWeight_norm_le_mMax (Λ := Λ) A N
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  have habs : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, him]
      simp [Real.sqrt_sq_eq_abs]
    rw [← hnorm_eq]
    exact hbiw_norm
  -- |biw.re| ≤ m_max ⟹ biw.re·(biw.re+1) ≤ m_max·(m_max+1).
  have hre_le := abs_le.mp habs
  obtain ⟨hre_ge, hre_le⟩ := hre_le
  nlinarith [hre_ge, hre_le, sq_nonneg ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
    (bipartiteImbalanceWeight (Λ := Λ) A N).re)]

end LatticeSystem.Quantum
