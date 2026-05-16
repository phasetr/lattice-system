import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinComplementReNegPosCard
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinComplementRe

/-!
# `min(...) < 0 ↔ |Λ| ≥ 1 ∧ N ≥ 1`

PR #3078: forward direction (`|Λ| ≥ 1 ∧ N ≥ 1 → min < 0`).
For the reverse: at `|Λ| = 0 ∨ N = 0`, `min = 0`.

Combining (and using PR #3011's explicit min formula):

  `min((predicted_min A).re, (predicted_min ¬A).re) < 0
   ↔ 0 < |Λ| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min iff strict negativity ↔ `|Λ| ≥ 1, N ≥ 1`**. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_neg_iff_card_pos
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 ↔
      0 < Fintype.card Λ ∧ 0 < N := by
  constructor
  · intro hlt
    by_contra hneg
    push Not at hneg
    -- hneg: 0 < |Λ| → ¬ 0 < N, i.e. (|Λ| = 0) ∨ (N = 0).
    rw [bipartiteToyMinEnergyPredicted_min_complement_re_eq] at hlt
    classical
    have hsum : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = Fintype.card Λ := by
      rw [← Finset.card_union_of_disjoint, ← Finset.card_univ]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases A x <;> simp
      · rw [Finset.disjoint_filter]
        intro x _ hx
        simp [hx]
    -- Two cases: either |Λ| = 0 or N = 0.
    by_cases hΛ : 0 < Fintype.card Λ
    · -- 0 < |Λ|, so by hneg, ¬ 0 < N, hence N = 0.
      have hN_zero : N = 0 := Nat.le_zero.mp (hneg hΛ)
      rw [hN_zero] at hlt
      simp at hlt
    · -- ¬ 0 < |Λ|, so |Λ| = 0, hence both |A| = 0 and |¬A| = 0.
      have hΛ_zero : Fintype.card Λ = 0 := Nat.le_zero.mp (not_lt.mp hΛ)
      have hcA_zero : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by omega
      have hcAc_zero : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by omega
      have hcA_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hcA_zero
      have hcAc_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hcAc_zero
      rw [hcA_re, hcAc_re] at hlt
      simp at hlt
  · intro ⟨hΛ, hN⟩
    exact bipartiteToyMinEnergyPredicted_min_complement_re_neg_of_card_pos (Λ := Λ) A N hΛ hN

end LatticeSystem.Quantum
