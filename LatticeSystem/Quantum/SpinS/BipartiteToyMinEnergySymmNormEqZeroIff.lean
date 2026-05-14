import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmEqZeroIff

/-!
# `‖bipartiteToyMinEnergyPredictedSymm A N‖ = 0` characterisation at `N ≥ 1`

Combining `norm_eq_zero` with PR #2864:

  `(N ≥ 1) → (‖bipartiteToyMinEnergyPredictedSymm A N‖ = 0
              ↔ |A| = 0 ∨ |¬A| = 0)`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **`‖symm-energy‖ = 0 ↔ |A| = 0 ∨ |¬A| = 0`** at `N ≥ 1`.
Direct from `norm_eq_zero` and PR #2864. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq_zero_iff_card_zero
    (hN : 1 ≤ N) :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  rw [norm_eq_zero]
  exact bipartiteToyMinEnergyPredictedSymm_eq_zero_iff_card_zero A hN

end LatticeSystem.Quantum
