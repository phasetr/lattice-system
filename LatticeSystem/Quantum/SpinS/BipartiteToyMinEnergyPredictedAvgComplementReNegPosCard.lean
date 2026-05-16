import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSumComplementReNegPosCard

/-!
# `avg < 0` at `|Λ| ≥ 1, N ≥ 1`

PR #3076: `(pmA).re + (pm¬A).re < 0` at `|Λ| ≥ 1, N ≥ 1`. Dividing by 2:

  `0 < |Λ|, 0 < N
    → ((predicted_min A).re + (predicted_min ¬A).re) / 2 < 0`.

Strengthens PR #3050 (avg < 0 at non-degenerate) by dropping the
non-degeneracy hypothesis — the linear `−|Λ|·N/2` term in the avg
formula keeps it strictly negative even at saturated edges.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`avg < 0` at `|Λ| ≥ 1, N ≥ 1`** (no non-degeneracy needed).
Strengthens PR #3050. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_neg_of_card_pos
    (A : Λ → Bool) (N : ℕ)
    (hΛ : 0 < Fintype.card Λ)
    (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 < 0 := by
  have hsum := bipartiteToyMinEnergyPredicted_sum_complement_re_neg_of_card_pos
    (Λ := Λ) A N hΛ hN
  linarith

end LatticeSystem.Quantum
