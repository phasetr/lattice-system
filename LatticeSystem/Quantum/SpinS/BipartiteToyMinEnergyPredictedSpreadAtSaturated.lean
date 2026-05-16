import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# Spread at saturated edges: `spread = |A|·N` at `|¬A| = 0`

PR #3012: `spread = ||A| − |¬A||·N` unconditionally.

At canonical-saturated `|¬A| = 0`, we have `||A| − 0| = |A|`, so:

  `|¬A| = 0 → spread = |A|·N`.

Together with `|A| = |Λ|` at this edge (since `|A| + |¬A| = |Λ|`),
this gives `spread = |Λ|·N` — the **maximum possible spread**
(at fixed `|Λ|` and `N`), since `||A| − |¬A|| ≤ |Λ|` always.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread at canonical-saturated `|¬A| = 0`**: `spread = |A|·N`.
Direct from PR #3012's spread formula. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_at_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  have hB_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
    exact_mod_cast h
  rw [hB_zero, sub_zero, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ))]

end LatticeSystem.Quantum
