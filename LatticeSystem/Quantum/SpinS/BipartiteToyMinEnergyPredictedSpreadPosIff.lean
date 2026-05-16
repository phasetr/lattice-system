import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadZeroIff

/-!
# Spread strictly positive iff unbalanced: `0 < spread ↔ |A| ≠ |¬A|` at `N ≥ 1`

PR #3012 gave the spread formula `||A| − |¬A||·N`.
PR #3013 gave the equality iff `spread = 0 ↔ balanced`.

This file packages the strict positivity iff at `N ≥ 1`:

  `0 < max((predicted_min A).re, (predicted_min ¬A).re)
       − min((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |A| ≠ |¬A|`.

Since the spread is non-negative (it equals `||A| − |¬A||·N ≥ 0`)
and zero exactly at balanced (PR #3013), strict positivity is
exactly the unbalanced case. Together with PR #3013, this gives
the full sign trichotomy of the orientation-spread of the
predicted min energy.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread strict iff unbalanced** at `N ≥ 1`: the orientation-spread
is strictly positive exactly at unbalanced (`|A| ≠ |¬A|`). Companion
of PR #3013 (equality iff). -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_pos_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    0 < max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
          min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro hpos hcardeq
    have heq : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcardeq
    have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
    rw [hsub, abs_zero, zero_mul] at hpos
    exact absurd hpos (lt_irrefl 0)
  · intro hcardne
    have hne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≠
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcardne
    have hsubne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≠ 0 :=
      sub_ne_zero.mpr hne
    have habspos : 0 < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| :=
      abs_pos.mpr hsubne
    exact mul_pos habspos hNpos

end LatticeSystem.Quantum
