import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# `bipartiteToyMinEnergyPredictedSymm` vanishes at the saturated edge

At the saturated edge `|¬A| = 0`, the symmetric-form predicted
minimum energy collapses to `0`:

  `|¬A| = 0 → bipartiteToyMinEnergyPredictedSymm A N = 0`.

Both contributions vanish: the cross term `|A|·|¬A|·N²/2` because
`|¬A| = 0`, and `min(|A|, |¬A|)·N = 0·N = 0`. Symmetric-form
mirror of PR #2779 (`eq_zero_of_cardNotA_zero`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Symmetric predicted min energy vanishes at the saturated
edge `|¬A| = 0`**:
`bipartiteToyMinEnergyPredictedSymm A N = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N = 0 := by
  unfold bipartiteToyMinEnergyPredictedSymm
  rw [h]
  simp

/-- Mirror at the opposite saturated edge `|A| = 0`:
`bipartiteToyMinEnergyPredictedSymm A N = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N = 0 := by
  unfold bipartiteToyMinEnergyPredictedSymm
  rw [h]
  simp

end LatticeSystem.Quantum
