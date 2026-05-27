import LatticeSystem.Quantum.SpinS.DressedAxisSwapHermitian
import LatticeSystem.Quantum.SpinS.DressedAxisSwapOffDiag

/-!
# The real-part matrix of the Marshall-dressed axis-swapped Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The real-part matrix `(Ĥ'_dressed)_{σσ'} ↦ Re(Ĥ'_dressed σ σ')` is the real symmetric matrix on
which the Perron–Frobenius argument runs.  For real couplings it is **symmetric** (the dressed
matrix is Hermitian, #3775) and, for a bipartite AFM coupling + case (i), has **non-positive
off-diagonal entries** (#3770).  So `c·1 − ReMatrix` (suitably shifted) is entrywise non-negative
— the Perron–Frobenius matrix whose top eigenvalue is the dressed ground energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The real-part matrix of the Marshall-dressed `Ĥ'`. -/
noncomputable def dressedAxisSwappedAnisotropicHeisenbergSReMatrix
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℝ :=
  fun σ σ' => (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ σ').re

/-- Component-wise unfolding. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (σ σ' : Λ → Fin (N + 1)) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ' =
      (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ σ').re := rfl

/-- The real-part matrix is symmetric for real couplings (the dressed matrix is Hermitian). -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) :
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).IsSymm := by
  have hH := dressedAxisSwappedAnisotropicHeisenbergS_isHermitian_of_real (N := N) A hJ hlam hD
  ext σ σ'
  rw [Matrix.transpose_apply, dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply]
  have h := congrFun (congrFun hH σ) σ'
  rw [Matrix.conjTranspose_apply] at h
  rw [← h, Complex.star_def, Complex.conj_re]

/-- The real-part matrix has non-positive off-diagonal entries (case (i), bipartite AFM). -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_offdiag_nonpos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 ≤ lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ ≤ 0 :=
  dressedAxisSwappedAnisotropicHeisenbergS_offdiag_re_nonpos A hJim hJnn hJself hJbip
    hlam hlb hub hDim hDnn hne

end LatticeSystem.Quantum
