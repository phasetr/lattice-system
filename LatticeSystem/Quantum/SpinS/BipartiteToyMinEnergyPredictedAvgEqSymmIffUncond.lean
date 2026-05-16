import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubAvgEqHalfSpread

/-!
# `avg = (predictedSymm A).re ↔ balanced ∨ N = 0` unconditionally

PR #3034: `predictedSymm.re − avg = ||A| − |¬A||·N / 2`.

This vanishes iff one of the factors is zero:

  `((pmA).re + (pm¬A).re) / 2 = (predictedSymm A).re
   ↔ |A| = |¬A| ∨ N = 0`.

Unconditional version of PR #3037 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg = predictedSymm iff balanced or N = 0** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_eq_predictedSymm_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  have hgap := bipartiteToyMinEnergyPredictedSymm_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
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
