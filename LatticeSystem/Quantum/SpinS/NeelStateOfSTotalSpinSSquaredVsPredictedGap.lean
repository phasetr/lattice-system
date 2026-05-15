import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.MinNEqHalfCardTimesNMinusImbalanceNorm

/-!
# Néel-vs-predicted-(Ŝ_tot)² gap = `min·N`

PR #2896 gave the Néel-state Casimir form:

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = ‖biw‖² + |Λ|·N/2`.

Tasaki §2.5 Theorem 2.3 (γ-4) predicts at the ground state
`S_tot = ‖biw‖ = ||A|−|¬A||·N/2`, hence `(Ŝ_tot)²` eigenvalue
`= ‖biw‖·(‖biw‖+1) = ‖biw‖² + ‖biw‖`.

Their difference is

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖)
     = |Λ|·N/2 − ‖biw‖ = min(|A|, |¬A|)·N`

by PR #2887. Hence the Néel state's `(Ŝ_tot)²` expectation is
**`min·N` above the predicted GS `(Ŝ_tot)²` eigenvalue** — a
direct parallel to the energy gap of PR #2884.

This shows the Néel state spans multiple `S_tot` sectors (it is
not the predicted ground state, except at saturated edges where
the gap collapses to 0).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel-vs-predicted (Ŝ_tot)² gap = `min·N`**:
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖) = min(|A|, |¬A|)·N`.

The Néel state's `(Ŝ_tot)²` expectation is exactly `min·N` above
the predicted `S_tot·(S_tot+1) = ‖biw‖·(‖biw‖+1)` eigenvalue. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_sub_predicted_eq_min_N :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re -
      (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) =
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        (N : ℝ) := by
  rw [neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq]
  rw [min_cardA_cardNotA_mul_N_eq_half_card_times_N_sub_imbalance_norm]
  ring

end LatticeSystem.Quantum
