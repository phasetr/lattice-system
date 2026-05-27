import LatticeSystem.Quantum.SpinS.ShiftedDressedAxisSwapParityBlock

/-!
# Strict positivity of the shifted dressed `Ĥ'` diagonal

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a strict shift `c` (above every real-part diagonal entry), the shifted matrix
`c • 1 − ReMatrix` has **strictly positive diagonal** entries.  Combined with the entrywise
non-negativity (#3781/#3782), this is the input to the diagonal case of
`Matrix.isIrreducible_iff_exists_pow_pos` (`(M^1)_{σσ} = M_{σσ} > 0`), one of the two cases of the
parity-block irreducibility proof.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Strict positivity of the shifted matrix diagonal for a strict shift `c`. -/
theorem shiftedDressedAxisSwappedReMatrix_diag_pos
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ}
    {σ : Λ → Fin (N + 1)}
    (hc : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c σ σ := by
  rw [shiftedDressedAxisSwappedReMatrix_apply_diag]
  linarith

/-- Strict positivity of the parity-block shifted matrix diagonal for a strict shift `c`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_diag_pos
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ} (p : ℕ)
    {σ : parityConfigS Λ N p}
    (hc : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c) :
    0 < shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ σ := by
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_apply]
  exact shiftedDressedAxisSwappedReMatrix_diag_pos A J lam D N hc

end LatticeSystem.Quantum
