import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# Spread iff balanced: `spread = 0 ↔ |A| = |¬A|` at `N ≥ 1`

PR #3012 gave the spread formula:

  `max((predicted_min A).re, (predicted_min ¬A).re)
    − min((predicted_min A).re, (predicted_min ¬A).re)
   = ||A| − |¬A||·N`.

This file packages the iff characterisation at `N ≥ 1`:

  `spread = 0 ↔ |A| = |¬A|`.

At balanced, both orientations give the same predicted min energy
(the symmetric Tasaki §2.5 Theorem 2.3 prediction). At unbalanced
(and `N ≥ 1`), the two orientations differ — measuring the
orientation-asymmetry of the toy Hamiltonian's signed-difference
formula.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread iff balanced** at `N ≥ 1`: the orientation-spread vanishes
exactly when `|A| = |¬A|`. Both orientations agree at balanced. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_zero_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNpos
  constructor
  · intro hprod
    have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd h hNne
    have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 :=
      abs_eq_zero.mp habs
    have heq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
    exact_mod_cast heq
  · intro hcard
    have heq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcard
    have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
    rw [hsub, abs_zero, zero_mul]

end LatticeSystem.Quantum
