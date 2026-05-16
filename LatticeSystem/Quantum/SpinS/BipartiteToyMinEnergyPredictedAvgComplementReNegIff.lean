import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementReNegPosCard
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementRe

/-!
# `avg < 0 ↔ |Λ| ≥ 1 ∧ N ≥ 1`

PR #3077: forward direction.
PR #3033: explicit avg formula `−|A|·|¬A|·N²/2 − |Λ|·N/2`.

Combining:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2 < 0
   ↔ 0 < |Λ| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg iff strict negativity ↔ `|Λ| ≥ 1 ∧ N ≥ 1`**. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_neg_iff_card_pos
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 < 0 ↔
      0 < Fintype.card Λ ∧ 0 < N := by
  constructor
  · intro hlt
    by_contra hneg
    push Not at hneg
    rw [bipartiteToyMinEnergyPredicted_avg_complement_re_eq] at hlt
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
    by_cases hΛ : 0 < Fintype.card Λ
    · have hN_zero : N = 0 := Nat.le_zero.mp (hneg hΛ)
      rw [hN_zero] at hlt
      simp at hlt
    · have hΛ_zero : Fintype.card Λ = 0 := Nat.le_zero.mp (not_lt.mp hΛ)
      have hcA_zero : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by omega
      have hcAc_zero : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by omega
      have hcA_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hcA_zero
      have hcAc_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hcAc_zero
      have hΛ_re : (Fintype.card Λ : ℝ) = 0 := by exact_mod_cast hΛ_zero
      rw [hcA_re, hcAc_re, hΛ_re] at hlt
      simp at hlt
  · intro ⟨hΛ, hN⟩
    exact bipartiteToyMinEnergyPredicted_avg_complement_re_neg_of_card_pos (Λ := Λ) A N hΛ hN

end LatticeSystem.Quantum
