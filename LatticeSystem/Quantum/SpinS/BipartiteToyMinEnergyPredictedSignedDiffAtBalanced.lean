import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# Signed difference at balanced: `(pmA).re − (pm¬A).re = 0` (unconditional in `N`)

PR #3021: `(predicted_min A).re − (predicted_min ¬A).re = (|A| − |¬A|)·N`.

At balanced (`|A| = |¬A|`), the linear factor vanishes:

  `|A| = |¬A| → (predicted_min A).re − (predicted_min ¬A).re = 0`

unconditionally in `N`. Companion of PR #3024 (spread = 0 at
balanced). At balanced both orientation-specific predicted min
energies are equal.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Signed difference vanishes at balanced** (unconditional in `N`):
direct from PR #3021's signed-difference formula. -/
theorem bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq_zero_of_balanced
    (A : Λ → Bool) (N : ℕ)
    (hbal : (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 := by
  rw [bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq A N]
  have heq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast hbal
  have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
  rw [hsub, zero_mul]

end LatticeSystem.Quantum
