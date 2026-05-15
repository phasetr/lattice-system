import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmEqZeroIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmStrictNeg

/-!
# `(symm).re = 0 ↔ |A| = 0 ∨ |¬A| = 0` at `N ≥ 1`

PR #2864 gave the **complex** iff form
`bipartiteToyMinEnergyPredictedSymm A N = 0 ↔ |A| = 0 ∨ |¬A| = 0`
(at `N ≥ 1`).

The **real-part** mirror

  `(bipartiteToyMinEnergyPredictedSymm A N).re = 0
     ↔ |A| = 0 ∨ |¬A| = 0`   (at `N ≥ 1`)

follows from the complex iff via `Complex.ext` (using PR #2843
`_im_zero`) or directly from PR #2845 strict negativity
(contrapositive) + the saturated-edge zero (forward).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **`(symm).re = 0 ↔ saturated edge`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_eq_zero_iff_card_zero
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  refine ⟨?_, ?_⟩
  · -- `.re = 0 → saturated`: contrapositive of strict negativity.
    intro hre
    by_contra hbad
    push Not at hbad
    obtain ⟨hA_ne, hAc_ne⟩ := hbad
    have hA_pos :
        0 < (Finset.univ.filter (fun x : Λ => A x = true)).card :=
      Nat.pos_of_ne_zero hA_ne
    have hAc_pos :
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
      Nat.pos_of_ne_zero hAc_ne
    have hN_pos : 0 < N := hN
    have hstrict :=
      bipartiteToyMinEnergyPredictedSymm_re_neg_of_nondegenerate
        A N hA_pos hAc_pos hN_pos
    linarith
  · -- saturated → `.re = 0`.
    intro hsat
    rcases hsat with hA_zero | hAc_zero
    · have :=
        bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardA_zero A N hA_zero
      rw [this]
      exact Complex.zero_re
    · have :=
        bipartiteToyMinEnergyPredictedSymm_eq_zero_of_cardNotA_zero A N hAc_zero
      rw [this]
      exact Complex.zero_re

end LatticeSystem.Quantum
