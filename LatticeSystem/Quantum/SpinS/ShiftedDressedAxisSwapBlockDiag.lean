import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.AxisSwapParityBlock

/-!
# Parity block-diagonality of the (shifted) dressed `Ĥ'` real-part matrix

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The dressed `Ĥ'` real-part matrix (and its shift `c • 1 − ReMatrix`) is **block-diagonal** with
respect to the magnetization parity: its entries vanish across parity classes (`magSumS` parities
differ), inheriting the block-diagonality of `Ĥ'` (#3772, requires no self-bonds).  Hence on each
parity block the matrix powers restrict cleanly — the input that lets the parity-block reachability
matrix-power positivity (#3787) descend to the parity-block submatrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The dressed `Ĥ'` real-part matrix vanishes across magnetization-parity classes. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_parity_ne
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hpar : magSumS σ' % 2 ≠ magSumS σ % 2) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_apply]
  have hne : σ' ≠ σ := fun h => hpar (by rw [h])
  rw [axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne hJself lam D hne
    (by rw [Nat.odd_iff]; omega)]
  simp

/-- The shifted dressed `Ĥ'` real-part matrix vanishes across magnetization-parity classes. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_eq_zero_of_parity_ne
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ) (c : ℝ)
    {σ' σ : Λ → Fin (N + 1)} (hpar : magSumS σ' % 2 ≠ magSumS σ % 2) :
    shiftedDressedAxisSwappedReMatrix A J lam D N c σ' σ = 0 := by
  have hne : σ' ≠ σ := fun h => hpar (by rw [h])
  rw [shiftedDressedAxisSwappedReMatrix_apply_off_diag A J lam D N c hne,
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_parity_ne A hJself lam D hpar,
    neg_zero]

end LatticeSystem.Quantum
