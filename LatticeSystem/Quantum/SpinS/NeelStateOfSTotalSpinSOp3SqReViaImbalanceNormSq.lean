import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormSq

/-!
# `<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel>.re = ‖biw‖²`

The Néel-state z-axis Casimir expectation
`neelStateOfS_totalSpinSOp3_sq_expectation` reads

  `<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel> = ((|A|−|¬A|)·N/2)²`.

Since `(|A|−|¬A|)·N/2 = biw.re` (PR #2825) and `(biw.re)² = ‖biw‖²`
(PR #2877 helper), the real part simplifies to

  `(<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel>).re = ‖biw‖²`.

This identifies the z-axis Casimir expectation with the **predicted
S_tot squared** `‖biw‖² = (||A|−|¬A||·N/2)²`. Combined with PR #2896
(`(Ŝ_tot)² expectation = ‖biw‖² + |Λ|·N/2`), the transverse Casimir
expectation is `(Ŝ_tot^(1))² + (Ŝ_tot^(2))² = |Λ|·N/2` (independent
of bipartition).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel-state `(Ŝ_tot^(3))²` expectation real part in `‖biw‖²` form**:
`(<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel>).re = ‖biw‖²`. -/
theorem neelStateOfS_totalSpinSOp3_sq_expectation_re_via_imbalance_norm_sq :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec
          (neelStateOfS A N))).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [neelStateOfS_totalSpinSOp3_sq_expectation]
  have hbiw_norm_sq :=
    bipartiteImbalanceWeight_norm_mul_self_eq_re_mul_self (Λ := Λ) A N
  rw [bipartiteImbalanceWeight_re_eq] at hbiw_norm_sq
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.natCast_re, Complex.natCast_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  linarith [hbiw_norm_sq]

end LatticeSystem.Quantum
