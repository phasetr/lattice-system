import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmSaturated

/-!
# Symm-energy norm at saturated edges = 0

PR #2849 proved
`|¬A| = 0 → bipartiteToyMinEnergyPredictedSymm A N = 0`
(and the mirror at `|A| = 0`).

Corollary: at saturated edges, the norm also vanishes:

  `|¬A| = 0 → ‖bipartiteToyMinEnergyPredictedSymm A N‖ = 0`,
  `|A| = 0 → ‖bipartiteToyMinEnergyPredictedSymm A N‖ = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Symm-energy norm vanishes at `|¬A| = 0` saturated edge**:
`‖bipartiteToyMinEnergyPredictedSymm A N‖ = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq_zero_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ = 0 := by
  rw [bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardNotA_zero A N h]
  exact norm_zero

/-- **Symm-energy norm vanishes at `|A| = 0` opposite saturated
edge**: `‖bipartiteToyMinEnergyPredictedSymm A N‖ = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq_zero_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ = 0 := by
  rw [bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardA_zero A N h]
  exact norm_zero

end LatticeSystem.Quantum
