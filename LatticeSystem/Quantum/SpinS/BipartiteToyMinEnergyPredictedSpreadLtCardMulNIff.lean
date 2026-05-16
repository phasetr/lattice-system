import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadLeCardMulN
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadAtSaturated
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadAtComplementSaturated

/-!
# `spread < |Λ|·N ↔ ¬saturated` at `N ≥ 1`

PR #3028: `spread ≤ |Λ|·N` unconditionally.
PR #3026 / #3027: spread = `|Λ|·N` at saturated edges (`|¬A| = 0` or
`|A| = 0`).

At `N ≥ 1`, the strict version of #3028 holds iff non-saturated:

  `spread < |Λ|·N ↔ |A| ≥ 1 ∧ |¬A| ≥ 1`.

Non-degenerate bipartite configurations have strictly less than the
maximum orientation-spread.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **spread < `|Λ|·N` iff non-saturated** at `N ≥ 1`. Strict version
of PR #3028 + characterisation of the equality case via PRs #3026/#3027. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_lt_card_mul_N_iff_nondegenerate
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (Fintype.card Λ : ℝ) * (N : ℝ) ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hle := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_le_card_mul_N
    (Λ := Λ) A N
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro hlt
    by_contra hnotboth
    push Not at hnotboth
    -- hnotboth: ¬ (0 < |A| ∧ 0 < |¬A|)
    -- Hence one is 0: |A| = 0 ∨ |¬A| = 0.
    have hAB_zero : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
      by_cases hA : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0
      · exact Or.inl hA
      · right
        have hA_pos : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card :=
          Nat.pos_of_ne_zero hA
        exact Nat.le_zero.mp (hnotboth hA_pos)
    rcases hAB_zero with hA0 | hAc0
    · -- |A| = 0 → spread = |¬A|·N = |Λ|·N (since |Λ| = |¬A| here).
      have hsp := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_at_cardA_zero
        (Λ := Λ) A N hA0
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
      have hΛ_eq : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
          (Fintype.card Λ : ℝ) := by
        have : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
            Fintype.card Λ := by omega
        exact_mod_cast this
      rw [hΛ_eq] at hsp
      linarith
    · -- |¬A| = 0 → spread = |A|·N = |Λ|·N.
      have hsp := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_at_cardNotA_zero
        (Λ := Λ) A N hAc0
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
      have hΛ_eq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          (Fintype.card Λ : ℝ) := by
        have : (Finset.univ.filter (fun x : Λ => A x = true)).card =
            Fintype.card Λ := by omega
        exact_mod_cast this
      rw [hΛ_eq] at hsp
      linarith
  · intro ⟨hA, hAc⟩
    -- Both non-empty: spread = ||A|-|¬A||·N < (|A|+|¬A|)·N = |Λ|·N.
    -- We use the spread formula directly.
    rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq]
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
    have hsum_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by exact_mod_cast hsum
    have hA_re : (0 : ℝ) < ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      exact_mod_cast hA
    have hAc_re : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hAc
    have habs_lt : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| <
        (Fintype.card Λ : ℝ) := by
      rw [abs_sub_lt_iff]
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    exact (mul_lt_mul_iff_of_pos_right hN_re).mpr habs_lt

end LatticeSystem.Quantum
