import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmBalanced
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Balanced-case symm-energy real part in terms of `|Λ|`

When `|A| = |¬A|`, the symm-predicted minimum energy real part
takes the lattice-cardinality form

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = −|Λ|²·N²/8 − |Λ|·N/2`.

Proof: combine PR #2842's balanced complex form
`bipartiteToyMinEnergyPredictedSymm A N = −|A|²·N²/2 − |A|·N`
with the cardinality identity `2·|A| = |Λ|` (which follows from
PR #2870 `|A| + |¬A| = |Λ|` together with `|A| = |¬A|`).

This saturates the lower bound from PR #2880
(`(symm).re ≥ −|Λ|²·N²/8 − min·N`) at balanced sublattices, where
`min = |A| = |Λ|/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Balanced symm-energy real part in `|Λ|` form**:
when `|A| = |¬A|`,
`(bipartiteToyMinEnergyPredictedSymm A N).re = −|Λ|²·N²/8 − |Λ|·N/2`. -/
theorem bipartiteToyMinEnergyPredictedSymm_balanced_re_eq_cardinality
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      -((Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 8) -
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq]
  have hsum := cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hsum_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by exact_mod_cast hsum
  have h_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast h
  -- From h_real and hsum_real: 2·|A| = |Λ|.
  have h2A : 2 * ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by linarith
  -- min(|A|, |¬A|) = |A| when |A| = |¬A|.
  have hmin : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    rw [← h_real]; exact min_self _
  rw [hmin]
  rw [← h_real]
  -- Substitute |Λ| = 2·|A|.
  have hL : (Fintype.card Λ : ℝ) =
      2 * ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    linarith
  rw [hL]
  ring

end LatticeSystem.Quantum
