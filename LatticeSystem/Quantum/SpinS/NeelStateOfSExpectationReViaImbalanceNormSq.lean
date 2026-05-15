import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReEqHalfImbalanceNormSq

/-!
# Néel-state expectation real part via `‖bipartiteImbalanceWeight‖²`

PR #2884 established the Néel-vs-predicted-min gap

  `<Φ_Néel|Ĥ_toy_S|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm A N
     = min(|A|, |¬A|)·N`.

PR #2878 gives the closed form for the predicted minimum

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = ‖biw‖²/2 − |Λ|²·N²/8 − min(|A|, |¬A|)·N`.

Combining the two, the `min·N` contributions cancel, leaving the
**Néel-state expectation real part in `‖biw‖²` form**:

  `(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = ‖biw‖²/2 − |Λ|²·N²/8`.

This is the natural Tasaki §2.5 Theorem 2.3 form: the Néel state's
energy expectation depends only on the predicted spin magnitude
squared `‖biw‖²` and the lattice cardinality `|Λ|`, with no
explicit `min(|A|, |¬A|)` dependence.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel-state toy-Hamiltonian expectation real part in
`‖biw‖²` form**:
`(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = ‖biw‖²/2 − |Λ|²·N²/8`.

The `min(|A|, |¬A|)·N` term cancels between the Néel-vs-predicted
gap (PR #2884) and the predicted-symm closed form (PR #2878). -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_via_imbalance_norm_sq :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ / 2 -
        (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
            ((N : ℝ) * (N : ℝ)) / 8 := by
  have hgap :=
    neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
      (Λ := Λ) A N
  -- From hgap (complex): Néel = predictedSymm + min·N.
  have heq :
      dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N)) =
        bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N +
          ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
              (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            (N : ℂ)) := by
    linear_combination hgap
  rw [heq]
  rw [Complex.add_re,
      bipartiteToyMinEnergyPredictedSymm_re_eq_half_imbalance_norm_sq_sub]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Nat.cast_min]
  ring

end LatticeSystem.Quantum
