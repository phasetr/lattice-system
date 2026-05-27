import LatticeSystem.Quantum.SpinS.ParityConfig
import LatticeSystem.Quantum.SpinS.DressedAxisSwapHermitian

/-!
# The Marshall-dressed `Ĥ'` restricted to a magnetization-parity block

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The Marshall-dressed axis-swapped Hamiltonian, restricted to a magnetization-parity block
`parityConfigS Λ N p`, is the submatrix on that subtype.  Since `Ĥ'` is block-diagonal in parity
(#3772) these blocks capture its full action, and each block carries the Perron–Frobenius
structure (real symmetric, non-negative off-diagonal after dressing) on which the `≤ 1`
per-block degeneracy bound is proved (PR5).  This file records the block matrix and its Hermiticity.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The Marshall-dressed `Ĥ'` restricted to the magnetization-parity block `p`. -/
noncomputable def dressedAxisSwappedAnisotropicHeisenbergSOnParityBlock
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℂ :=
  (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding of the parity-block matrix. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSOnParityBlock_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (p : ℕ)
    (σ τ : parityConfigS Λ N p) :
    dressedAxisSwappedAnisotropicHeisenbergSOnParityBlock A J lam D N p σ τ =
      dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ.1 τ.1 := rfl

/-- The parity-block matrix is Hermitian for real couplings. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSOnParityBlock_isHermitian_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ) :
    (dressedAxisSwappedAnisotropicHeisenbergSOnParityBlock A J lam D N p).IsHermitian := by
  have hH := dressedAxisSwappedAnisotropicHeisenbergS_isHermitian_of_real (N := N) A hJ hlam hD
  ext σ τ
  rw [dressedAxisSwappedAnisotropicHeisenbergSOnParityBlock,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_apply, Matrix.submatrix_apply]
  exact congrFun (congrFun hH σ.1) τ.1

end LatticeSystem.Quantum
