import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNormEqZeroIff

/-!
# Alternative form of symm-energy norm positivity at `N ≥ 1`

PR #2860 proved strict positivity via `_re_neg_of_nondegenerate`.
This file provides a slightly different but equivalent form:

  `(N ≥ 1) → (|A| ≠ 0) → (|¬A| ≠ 0)
    → 0 < ‖bipartiteToyMinEnergyPredictedSymm A N‖`,

obtained via the contrapositive of PR #2865 (norm = 0 iff one
sublattice is empty).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **Alternative form of strict positivity**: `0 <
‖bipartiteToyMinEnergyPredictedSymm A N‖` when `N ≥ 1`,
`|A| ≠ 0`, `|¬A| ≠ 0`. Contrapositive of PR #2865. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_pos_of_card_ne_zero
    (hN : 1 ≤ N)
    (hA : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠ 0)
    (hAc : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≠ 0) :
    0 < ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ := by
  rw [lt_iff_le_and_ne]
  refine ⟨norm_nonneg _, fun heq => ?_⟩
  have h := (bipartiteToyMinEnergyPredictedSymm_norm_eq_zero_iff_card_zero A hN).mp heq.symm
  rcases h with hA_eq | hAc_eq
  · exact hA hA_eq
  · exact hAc hAc_eq

end LatticeSystem.Quantum
