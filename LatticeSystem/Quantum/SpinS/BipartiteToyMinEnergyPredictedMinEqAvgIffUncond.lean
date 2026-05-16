import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgSubMinEqHalfSpread

/-!
# `min(...) = avg ↔ |A| = |¬A| ∨ N = 0` unconditionally

PR #3039: `avg − min = ||A| − |¬A||·N / 2`.

This vanishes iff one of the factors is zero:

  `min((pmA).re, (pm¬A).re) = ((pmA).re + (pm¬A).re) / 2
   ↔ |A| = |¬A| ∨ N = 0`.

Unconditional version of PR #3040 (which required `N ≥ 1`).
Mirror of PR #3092 for the lower end of the orientation sandwich.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min = avg iff balanced or N = 0** unconditionally. Mirror of PR #3092. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  have hgap := bipartiteToyMinEnergyPredicted_avg_complement_re_sub_min_eq (Λ := Λ) A N
  constructor
  · intro heq
    have hgap_zero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) / 2 = 0 := by
      linarith
    have hprod_zero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) = 0 := by
      linarith
    rcases mul_eq_zero.mp hprod_zero with habs | hN
    · left
      have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := abs_eq_zero.mp habs
      have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
      exact_mod_cast heq_re
    · right; exact_mod_cast hN
  · intro hor
    rcases hor with hbal | hN_zero
    · have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hbal
      have hsub_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
      have habs_zero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| = 0 := by
        rw [hsub_zero, abs_zero]
      have hgap_zero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) / 2 = 0 := by
        rw [habs_zero]; ring
      linarith
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN_zero
      have hgap_zero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) / 2 = 0 := by
        rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
