import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementReNegPosCard
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinLeAvg

/-!
# `min(...) < 0` at `|Λ| ≥ 1, N ≥ 1`

PR #3077: `avg < 0` at `|Λ| ≥ 1, N ≥ 1`. PR #3036: `min ≤ avg`.
Combining:

  `0 < |Λ|, 0 < N
    → min((predicted_min A).re, (predicted_min ¬A).re) < 0`.

Strengthens PR #3074 (min < 0 at non-degenerate) by dropping the
non-degeneracy hypothesis. The strict negativity holds at saturated
edges too via the linear `−|Λ|·N/2` term.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`min(...) < 0` at `|Λ| ≥ 1, N ≥ 1`** (no non-degeneracy needed).
Strengthens PR #3074. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_neg_of_card_pos
    (A : Λ → Bool) (N : ℕ)
    (hΛ : 0 < Fintype.card Λ)
    (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 := by
  have havg_neg := bipartiteToyMinEnergyPredicted_avg_complement_re_neg_of_card_pos
    (Λ := Λ) A N hΛ hN
  have hmin_le_avg := bipartiteToyMinEnergyPredicted_min_complement_re_le_avg
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
