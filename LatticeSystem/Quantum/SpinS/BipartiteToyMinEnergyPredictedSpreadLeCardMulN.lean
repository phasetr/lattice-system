import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# Upper bound on the predicted spread: `spread ≤ |Λ|·N`

PR #3012: `spread = ||A| − |¬A||·N` unconditionally.

Since `|A| + |¬A| = |Λ|` (the cardinalities partition the universe),
we have `||A| − |¬A|| ≤ |A| + |¬A| = |Λ|`. Therefore:

  `spread ≤ |Λ|·N`

unconditionally. Equality is attained at saturated edges (`|A| = 0`
or `|¬A| = 0`); PRs #3026 / #3027 already characterise these
endpoints.

This bound complements PR #3012 by giving the maximum possible value
of the orientation-spread in terms of `|Λ|` and `N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread upper bound**: `spread ≤ |Λ|·N` unconditionally. Equality
attained at saturated edges (PRs #3026/#3027). -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_le_card_mul_N
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) := by
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
  have hcA : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    positivity
  have hcB : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    positivity
  have hsum_real : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    exact_mod_cast hsum
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| ≤
      (Fintype.card Λ : ℝ) := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  exact mul_le_mul_of_nonneg_right habs hNnn

end LatticeSystem.Quantum
