import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# `bipartiteImbalanceWeight` is real

The bipartite imbalance weight defined in
`NeelBipartiteWeight.lean` (PR #2773) is

  `bipartiteImbalanceWeight A N = (|A| − |¬A|) · N / 2`

cast through `ℂ`. Its imaginary part is therefore identically `0`,
and the real part is the literal signed imbalance times `N/2`.

This file pins down both facts as standalone lemmas:

- `bipartiteImbalanceWeight_im_zero`
- `bipartiteImbalanceWeight_re_eq`

Useful for downstream real-axis reasoning about
`bipartiteToyMinEnergyPredicted` and the matching against Tasaki
§2.5 Theorem 2.3's `||A| − |¬A|| · S` predicted ground-state
energy magnitude.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- Real-valued form of `bipartiteImbalanceWeight` as the lift of
the real-axis imbalance times `N/2`. -/
theorem bipartiteImbalanceWeight_eq_ofReal :
    bipartiteImbalanceWeight (Λ := Λ) A N =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        ((N : ℝ) / 2) : ℝ) := by
  unfold bipartiteImbalanceWeight
  push_cast
  ring

/-- **`bipartiteImbalanceWeight` is purely real**:
`(bipartiteImbalanceWeight A N).im = 0`. -/
theorem bipartiteImbalanceWeight_im_zero :
    (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 := by
  rw [bipartiteImbalanceWeight_eq_ofReal]
  exact Complex.ofReal_im _

/-- **Real part of `bipartiteImbalanceWeight`**:
`(bipartiteImbalanceWeight A N).re = (|A| − |¬A|) · N / 2`
as a real number. -/
theorem bipartiteImbalanceWeight_re_eq :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        ((N : ℝ) / 2) := by
  rw [bipartiteImbalanceWeight_eq_ofReal]
  exact Complex.ofReal_re _

end LatticeSystem.Quantum
