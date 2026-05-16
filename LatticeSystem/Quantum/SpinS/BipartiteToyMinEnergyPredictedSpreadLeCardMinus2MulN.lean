import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# Refined spread bound at non-degenerate: `spread ≤ (|Λ| − 2)·N`

PR #3028 / #3071: `spread ≤ |Λ|·N` unconditionally, strict at non-degenerate.

This file packages a stronger bound at non-degenerate: when both
sublattices are non-empty,

  `0 < |A|, 0 < |¬A| → spread ≤ (|Λ| − 2)·N`

unconditionally in `N`. The bound is achieved at minimal non-degenerate
(one sublattice has 1 element, the other has `|Λ| − 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Refined spread bound at non-degenerate**: when `|A| ≥ 1, |¬A| ≥ 1`,
`spread ≤ (|Λ| − 2)·N`. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_le_card_minus_2_mul_N
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      ((Fintype.card Λ : ℝ) - 2) * (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
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
  have hA_re : (1 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    exact_mod_cast hA
  have hAc_re : (1 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast hAc
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| ≤
      (Fintype.card Λ : ℝ) - 2 := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  exact mul_le_mul_of_nonneg_right habs hNnn

end LatticeSystem.Quantum
