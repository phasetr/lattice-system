import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# Spread at complement-saturated edges: `spread = |¬A|·N` at `|A| = 0`

Mirror of PR #3026. At complement-saturated `|A| = 0`:

  `|A| = 0 → spread = |¬A|·N`

unconditionally in `N`. Since `|¬A| = |Λ|` at this edge, this gives
`spread = |Λ|·N` — the maximum possible spread (matching PR #3026).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread at complement-saturated `|A| = 0`**: `spread = |¬A|·N`.
Mirror of PR #3026. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_at_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  have hA_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
    exact_mod_cast h
  rw [hA_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ))]

end LatticeSystem.Quantum
