import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# `0 < spread ↔ |A| ≠ |¬A| ∧ N ≥ 1` unconditionally

PR #3012: `spread = ||A| − |¬A||·N` unconditionally.

This is positive iff both factors are positive (since both are ≥ 0):

  `0 < max((pmA).re, (pm¬A).re) − min((pmA).re, (pm¬A).re)
   ↔ |A| ≠ |¬A| ∧ N ≠ 0`.

Unconditional version of PR #3014 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **spread > 0 iff unbalanced and positive N** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_pos_iff_unbalanced_and_N_ne_zero
    (A : Λ → Bool) (N : ℕ) :
    0 < max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
          min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      N ≠ 0 := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  -- 0 < ||A|-|¬A||·N ↔ ||A|-|¬A|| > 0 ∧ N > 0 ↔ |A|≠|¬A| ∧ N ≠ 0.
  constructor
  · intro hpos
    have habs_nn : (0 : ℝ) ≤ |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| := abs_nonneg _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    refine ⟨?_, ?_⟩
    · -- |A| ≠ |¬A|: by_contra → spread = 0 contradiction.
      intro hcard_eq
      have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hcard_eq
      have hsub_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
      rw [hsub_zero, abs_zero, zero_mul] at hpos
      exact lt_irrefl 0 hpos
    · -- N ≠ 0.
      intro hN_zero
      have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN_zero
      rw [hN_re, mul_zero] at hpos
      exact lt_irrefl 0 hpos
  · intro ⟨hcard_ne, hN_ne⟩
    have hcard_re_ne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≠
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcard_ne
    have hsub_ne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≠ 0 :=
      sub_ne_zero.mpr hcard_re_ne
    have habs_pos : 0 < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| := abs_pos.mpr hsub_ne
    have hN_re_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
      exact lt_of_le_of_ne hN_nn (Ne.symm hN_re_ne)
    exact mul_pos habs_pos hN_pos

end LatticeSystem.Quantum
