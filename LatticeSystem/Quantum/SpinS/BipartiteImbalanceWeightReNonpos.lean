import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `biw.re ≤ 0` at complement orientation `|A| ≤ |¬A|`

Mirror of `bipartiteImbalanceWeight_re_nonneg_of_cardA_ge_cardNotA`.

At complement orientation `|A| ≤ |¬A|`,
`biw.re = (|A| − |¬A|)·N/2 ≤ 0`. Direct from `biw.re_eq` + orientation
+ `N ≥ 0`.

  `biw.re ≤ 0`   at `|A| ≤ |¬A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **`biw.re ≤ 0` at complement orientation `|A| ≤ |¬A|`**. Mirror of
`bipartiteImbalanceWeight_re_nonneg_of_cardA_ge_cardNotA`. -/
theorem bipartiteImbalanceWeight_re_nonpos_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 := by
  rw [bipartiteImbalanceWeight_re_eq]
  have horient_real : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast horient
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  nlinarith [horient_real, hN_nn]

end LatticeSystem.Quantum
