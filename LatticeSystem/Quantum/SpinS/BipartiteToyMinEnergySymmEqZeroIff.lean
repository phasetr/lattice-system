import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmSaturated
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmStrictNeg

/-!
# Characterisation of `bipartiteToyMinEnergyPredictedSymm A N = 0` at `N ≥ 1`

PR #2849 proved the forward directions: vanishing at either
saturated edge. This file adds the converse (contrapositive of
PR #2845's strict negativity in the non-degenerate case):

  `N ≥ 1` and `bipartiteToyMinEnergyPredictedSymm A N = 0`
   → `|A| = 0` or `|¬A| = 0`.

Combined we get the iff:

  `(N ≥ 1) → (bipartiteToyMinEnergyPredictedSymm A N = 0
              ↔ |A| = 0 ∨ |¬A| = 0)`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **Reverse direction**: at `N ≥ 1`, if the symm-predicted min
energy vanishes, one of the sublattices is empty. -/
theorem cardA_or_cardNotA_zero_of_bipartiteToyMinEnergyPredictedSymm_eq_zero
    (hN : 1 ≤ N)
    (h : bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N = 0) :
    (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  -- Contrapositive: if both are ≥ 1, then the value is strictly negative.
  by_contra hcon
  push_neg at hcon
  obtain ⟨hA_ne, hAc_ne⟩ := hcon
  have hA_pos : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card :=
    Nat.pos_of_ne_zero hA_ne
  have hAc_pos : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
    Nat.pos_of_ne_zero hAc_ne
  have hN_pos : 0 < N := hN
  have h_re_neg :=
    bipartiteToyMinEnergyPredictedSymm_re_neg_of_nondegenerate
      A N hA_pos hAc_pos hN_pos
  have h_re_zero : (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re = 0 := by
    rw [h]; simp
  linarith

/-- **Iff characterisation of vanishing symm-predicted min energy**
at `N ≥ 1`: `bipartiteToyMinEnergyPredictedSymm A N = 0 ↔
|A| = 0 ∨ |¬A| = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_eq_zero_iff_card_zero
    (hN : 1 ≤ N) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  refine ⟨cardA_or_cardNotA_zero_of_bipartiteToyMinEnergyPredictedSymm_eq_zero A hN, ?_⟩
  rintro (hA | hAc)
  · exact bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardA_zero A N hA
  · exact bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardNotA_zero A N hAc

end LatticeSystem.Quantum
