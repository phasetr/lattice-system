import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyStrictNeg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `min(...) < 0` at non-degenerate `|A| ≥ 1, |¬A| ≥ 1, N ≥ 1`

PR #2817: `(pmA).re < 0` at non-degenerate. Applying to both
orientations and taking the min:

  `0 < |A|, 0 < |¬A|, 0 < N
    → min((predicted_min A).re, (predicted_min ¬A).re) < 0`.

Strict version of PR #3029 (unconditional `min ≤ 0`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`min((pmA).re, (pm¬A).re) < 0` at non-degenerate**: strict version
of PR #3029. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_neg_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 := by
  have hA_neg := bipartiteToyMinEnergyPredicted_re_neg_of_nondegenerate
    (Λ := Λ) A N hA hAc hN
  exact lt_of_le_of_lt (min_le_left _ _) hA_neg

end LatticeSystem.Quantum
