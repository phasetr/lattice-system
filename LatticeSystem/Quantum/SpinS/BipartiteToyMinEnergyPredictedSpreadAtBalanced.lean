import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# Spread at balanced: `spread = 0` (unconditionally, without `N ≥ 1`)

PR #3013 gave the iff `spread = 0 ↔ |A| = |¬A|` at `N ≥ 1`.

This file extracts the **unconditional implication** at balanced:

  `|A| = |¬A| → spread = 0`.

Direct from PR #3012's spread formula `||A| − |¬A||·N`: at balanced
the cardinality gap is `0` so the product is `0` regardless of `N`.
Unlike PR #3013, this direction holds even at `N = 0` (where both
sides are trivially `0`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread at balanced**: `|A| = |¬A| → spread = 0`. Direct from
PR #3012's spread formula `||A| − |¬A||·N`. Unconditional in `N`. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_zero_of_balanced
    (A : Λ → Bool) (N : ℕ)
    (hbal : (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  have heq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast hbal
  have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
  rw [hsub, abs_zero, zero_mul]

end LatticeSystem.Quantum
