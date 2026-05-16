import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# `spread = 0 ↔ balanced ∨ N = 0` unconditionally

PR #3012: `spread = ||A| − |¬A||·N` unconditionally.

This vanishes iff one of the factors is zero:

  `max((pmA).re, (pm¬A).re) − min((pmA).re, (pm¬A).re) = 0
   ↔ |A| = |¬A| ∨ N = 0`.

Unconditional version of PR #3013 (at `N ≥ 1`, the `N = 0` disjunct
is excluded).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **spread = 0 iff balanced or N = 0** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_zero_iff_balanced_or_N_zero
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  -- ||A| - |¬A||·N = 0 ↔ ||A| - |¬A|| = 0 ∨ N = 0 ↔ |A| = |¬A| ∨ N = 0.
  constructor
  · intro hprod_zero
    rcases mul_eq_zero.mp hprod_zero with habs_zero | hN_zero
    · left
      have hsub_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 :=
        abs_eq_zero.mp habs_zero
      have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
      exact_mod_cast heq_re
    · right
      exact_mod_cast hN_zero
  · intro hor
    rcases hor with hbal | hN_zero
    · have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hbal
      have hsub_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
      rw [hsub_zero, abs_zero, zero_mul]
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN_zero
      rw [hN_re]; ring

end LatticeSystem.Quantum
