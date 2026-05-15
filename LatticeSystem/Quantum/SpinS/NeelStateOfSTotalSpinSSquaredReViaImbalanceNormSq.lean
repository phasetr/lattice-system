import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelBasisVecS
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormSq

/-!
# `<Φ_Néel|(Ŝ_tot)²|Φ_Néel>.re = ‖biw‖² + |Λ|·N/2`

The Néel-state Casimir expectation
(`neelStateOfS_totalSpinSSquared_expectation_via_general`) reads

  `<Φ_Néel(A, N) | (Ŝ_tot)² | Φ_Néel(A, N)>
     = ((|A|−|¬A|)·N/2)² + |Λ|·N/2`.

Since `(|A|−|¬A|)·N/2 = (bipartiteImbalanceWeight A N).re`
(PR #2825) and `(biw.re)² = ‖biw‖²` (PR #2877 helper, since `biw`
is real), the real part of the Casimir expectation simplifies to

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = ‖biw‖² + |Λ|·N/2`.

This is the natural Tasaki §2.5 Theorem 2.3 (γ-4) form for the
Néel-state's total-spin Casimir eigenvalue expectation:
`‖biw‖² = (predicted S_tot)²` and `|Λ|·N/2 = m_max` is a constant
offset (independent of the bipartition).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel-state `(Ŝ_tot)²` expectation real part in `‖biw‖²` form**:
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = ‖biw‖² + |Λ|·N/2`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [neelStateOfS_totalSpinSSquared_expectation_via_general]
  have hbiw_norm_sq :=
    bipartiteImbalanceWeight_norm_mul_self_eq_re_mul_self (Λ := Λ) A N
  rw [bipartiteImbalanceWeight_re_eq] at hbiw_norm_sq
  simp only [Complex.add_re, sq, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.natCast_re,
    Complex.natCast_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  linarith [hbiw_norm_sq]

end LatticeSystem.Quantum
