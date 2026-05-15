import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `(<Φ_Néel|Ŝ_tot^(3)|Φ_Néel>).re = (bipartiteImbalanceWeight A N).re`

The linear z-axis total-spin expectation on the Néel state
(`neelStateOfS_totalSpinSOp3_expectation`) reads

  `<Φ_Néel|Ŝ_tot^(3)|Φ_Néel> = (|A| − |¬A|)·N/2`.

Since `(bipartiteImbalanceWeight A N).re = (|A| − |¬A|)·N/2`
(PR #2825 `bipartiteImbalanceWeight_re_eq`), the real part of the
expectation is literally `biw.re`:

  `(<Φ_Néel|Ŝ_tot^(3)|Φ_Néel>).re = (bipartiteImbalanceWeight A N).re`.

This identifies the Néel-state linear z-magnetization with the
imbalance weight's real part — the signed analog of `‖biw‖`
appearing in the squared form `(<Ŝ_tot^(3))²>_Néel = ‖biw‖²`
(PR #2904).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel-state linear `Ŝ_tot^(3)` expectation real part = `biw.re`**:
`(<Φ_Néel|Ŝ_tot^(3)|Φ_Néel>).re = (bipartiteImbalanceWeight A N).re`.

Direct identification: both equal `(|A| − |¬A|)·N/2`. -/
theorem neelStateOfS_totalSpinSOp3_expectation_re_eq_imbalance_re :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N).mulVec (neelStateOfS A N))).re =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [neelStateOfS_totalSpinSOp3_expectation, bipartiteImbalanceWeight_re_eq]
  simp only [Complex.sub_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im]
  ring

end LatticeSystem.Quantum
