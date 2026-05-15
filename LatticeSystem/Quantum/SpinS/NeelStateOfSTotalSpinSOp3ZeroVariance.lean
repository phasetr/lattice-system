import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSOp3SqReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSOp3ReEqBiwRe

/-!
# Zero variance of `Ŝ_tot^(3)` on the Néel state

PR #2904 gave `(<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel>).re = ‖biw‖²`.
PR #2905 gave `(<Φ_Néel|Ŝ_tot^(3)|Φ_Néel>).re = biw.re`.

Since `(biw.re)² = ‖biw‖²` (PR #2877 helper, since `biw` is real),
we get

  `<(Ŝ_tot^(3))²>_Néel.re = (<Ŝ_tot^(3)>_Néel.re)²`,

i.e., the **variance of `Ŝ_tot^(3)` vanishes on the Néel state**:

  `Var(Ŝ_tot^(3))_Néel.re = <(Ŝ_tot^(3))²>_Néel.re − (<Ŝ_tot^(3)>_Néel.re)² = 0`.

This formally confirms that the Néel state is an exact
`Ŝ_tot^(3)` eigenvector at eigenvalue `biw.re = (|A|−|¬A|)·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Zero `Ŝ_tot^(3)` variance on the Néel state**:
`<(Ŝ_tot^(3))²>_Néel.re = (<Ŝ_tot^(3)>_Néel.re)²`.

The Néel state is a definite-`M` eigenstate of `Ŝ_tot^(3)`. -/
theorem neelStateOfS_totalSpinSOp3_zero_variance :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec
          (neelStateOfS A N))).re =
      (dotProduct (star (neelStateOfS A N))
          ((totalSpinSOp3 Λ N).mulVec (neelStateOfS A N))).re *
        (dotProduct (star (neelStateOfS A N))
            ((totalSpinSOp3 Λ N).mulVec (neelStateOfS A N))).re := by
  rw [neelStateOfS_totalSpinSOp3_sq_expectation_re_via_imbalance_norm_sq,
      neelStateOfS_totalSpinSOp3_expectation_re_eq_imbalance_re]
  -- Goal: ‖biw‖ * ‖biw‖ = biw.re * biw.re
  exact bipartiteImbalanceWeight_norm_mul_self_eq_re_mul_self (Λ := Λ) A N

end LatticeSystem.Quantum
