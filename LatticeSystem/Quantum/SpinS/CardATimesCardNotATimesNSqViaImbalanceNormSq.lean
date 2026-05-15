import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormSq

/-!
# Identity: `|A|·|¬A|·N² = |Λ|²·N²/4 − ‖biw‖²`

The AFM cross-term magnitude `|A|·|¬A|·N²` is bridged to the
imbalance norm squared and the lattice cardinality:

  `|A|·|¬A|·N² = |Λ|²·N²/4 − ‖bipartiteImbalanceWeight A N‖²`.

Proof: from `4·|A|·|¬A| = (|A|+|¬A|)² − (|A|−|¬A|)² = |Λ|² −
(|A|−|¬A|)²` (PR #2870) and `‖biw‖² = (|A|−|¬A|)²·N²/4` (PR #2877
helper applied to PR #2826). Multiplying the first by `N²/4` and
substituting gives the identity.

This is the natural Tasaki §2.5 Theorem 2.3 reformulation: the
Néel expectation `<Φ_Néel|Ĥ_toy_S|Φ_Néel> = −|A|·|¬A|·N²/2` (PR
#1178) becomes
`= −|Λ|²·N²/8 + ‖biw‖²/2`, i.e., the form already proven in
PR #2886.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **AFM cross-term bridge**:
`|A|·|¬A|·N² = |Λ|²·N²/4 − ‖bipartiteImbalanceWeight A N‖²`. -/
theorem cardA_times_cardNotA_times_N_sq_eq_quarter_card_sq_times_N_sq_sub_imbalance_norm_sq :
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      ((N : ℝ) * (N : ℝ)) =
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 4 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have hbridge :=
    bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_sq (Λ := Λ) A N
  rw [bipartiteImbalanceWeight_norm_mul_self_eq_re_mul_self]
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq] at hbridge
  linarith

end LatticeSystem.Quantum
