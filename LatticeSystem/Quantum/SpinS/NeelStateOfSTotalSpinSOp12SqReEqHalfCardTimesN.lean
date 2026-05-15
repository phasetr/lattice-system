import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelHeisenbergExpectation

/-!
# Néel-state transverse Casimir expectation real part = `|Λ|·N/2`

The transverse total-spin Casimir expectation on the Néel state is
already complex-equal to `|Λ|·N/2`:

  `neelStateOfS_totalSpinSOp12_sq_expectation`:
  `<Φ_Néel | (Ŝ_tot^(1))² + (Ŝ_tot^(2))² | Φ_Néel> = |Λ|·N/2`.

Its real part is `|Λ|·N/2` (a real number). Combined with
- `<(Ŝ_tot)²>_Néel.re = ‖biw‖² + |Λ|·N/2` (PR #2896),
- `<(Ŝ_tot^(3))²>_Néel.re = ‖biw‖²` (PR #2904),

we get the **operator-level Casimir decomposition** on the Néel
state: the transverse contribution is bipartition-independent
(`|Λ|·N/2`), and the z-axis contribution carries the full
`‖biw‖²` dependence.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Transverse total-spin Casimir expectation real part on Néel**:
`(<Φ_Néel | (Ŝ_tot^(1))² + (Ŝ_tot^(2))² | Φ_Néel>).re = |Λ|·N/2`.

Bipartition-independent. The remaining bipartition dependence of
`<(Ŝ_tot)²>_Néel` is fully concentrated in the z-axis `(Ŝ_tot^(3))²`
component (PR #2904). -/
theorem neelStateOfS_totalSpinSOp12_sq_expectation_re_eq_half_card_times_N :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
          totalSpinSOp2 Λ N * totalSpinSOp2 Λ N).mulVec
          (neelStateOfS A N))).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [neelStateOfS_totalSpinSOp12_sq_expectation]
  simp only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.natCast_re, Complex.natCast_im]
  ring

end LatticeSystem.Quantum
