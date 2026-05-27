import LatticeSystem.Quantum.SpinS.DressedAxisSwapHermitian
import LatticeSystem.Quantum.SpinS.DressedAxisSwapOffDiag
import LatticeSystem.Quantum.SpinS.ParityConfig

/-!
# The Perron–Frobenius real matrix of the Marshall-dressed axis-swapped Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

This file assembles the real symmetric Perron–Frobenius matrix of the dressed `Ĥ'` and its shift /
parity-block restriction:

* `dressedAxisSwappedAnisotropicHeisenbergSReMatrix` — the real-part matrix `Re(Ĥ'_dressed)`;
  symmetric for real couplings (`Ĥ'_dressed` Hermitian, #3775), non-positive off-diagonal entries
  for case (i) bipartite AFM (#3770);
* `shiftedDressedAxisSwappedReMatrix` `= c • 1 − ReMatrix` — entrywise **non-negative** (for `c`
  above the diagonal), symmetric, with strictly positive diagonal for a strict shift;
* `…OnParityBlock` — the restriction to a magnetization-parity block, the per-block
  Perron–Frobenius matrix (non-negative + symmetric + positive diagonal).

Combined with parity-block irreducibility and the simplicity bridge (#3779), the top eigenspace of
each parity block is one-dimensional, giving the `≤ 2` ground-state degeneracy of `Ĥ'`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Real-part matrix -/

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

/-! ## Shifted matrix `c • 1 − ReMatrix` -/

/-- The shifted dressed `Ĥ'` real-part matrix `c • 1 − ReMatrix`. -/
noncomputable def shiftedDressedAxisSwappedReMatrix
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) :
    Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℝ :=
  c • 1 - dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N

/-- Off-diagonal entry: `= −ReMatrix σ' σ`. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_off_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    shiftedDressedAxisSwappedReMatrix A J lam D N c σ' σ =
      -dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ := by
  unfold shiftedDressedAxisSwappedReMatrix
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- Diagonal entry: `= c − ReMatrix σ σ`. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (σ : Λ → Fin (N + 1)) :
    shiftedDressedAxisSwappedReMatrix A J lam D N c σ σ =
      c - dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ := by
  unfold shiftedDressedAxisSwappedReMatrix
  simp [Matrix.sub_apply, Matrix.smul_apply]

/-- The shifted matrix is symmetric for real couplings. -/
theorem shiftedDressedAxisSwappedReMatrix_isSymm_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (c : ℝ) :
    (shiftedDressedAxisSwappedReMatrix A J lam D N c).IsSymm := by
  unfold shiftedDressedAxisSwappedReMatrix
  exact (Matrix.isSymm_one.smul c).sub
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real A hJ hlam hD)

/-- **Entrywise non-negativity** of the shifted matrix for `c` above all diagonal entries. -/
theorem shiftedDressedAxisSwappedReMatrix_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 ≤ lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re) {c : ℝ}
    (hc : ∀ σ, dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c)
    (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ shiftedDressedAxisSwappedReMatrix A J lam D N c σ' σ := by
  by_cases hne : σ' = σ
  · subst hne
    rw [shiftedDressedAxisSwappedReMatrix_apply_diag]
    linarith [hc σ']
  · rw [shiftedDressedAxisSwappedReMatrix_apply_off_diag A J lam D N c hne]
    have := dressedAxisSwappedAnisotropicHeisenbergSReMatrix_offdiag_nonpos A hJim hJnn hJself
      hJbip hlam hlb hub hDim hDnn hne
    linarith

/-- Strict positivity of the shifted matrix diagonal for a strict shift `c`. -/
theorem shiftedDressedAxisSwappedReMatrix_diag_pos
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ}
    {σ : Λ → Fin (N + 1)}
    (hc : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c σ σ := by
  rw [shiftedDressedAxisSwappedReMatrix_apply_diag]
  linarith

/-! ## Parity-block restriction -/

/-- The shifted dressed `Ĥ'` real-part matrix restricted to the magnetization-parity block `p`. -/
noncomputable def shiftedDressedAxisSwappedReMatrixOnParityBlock
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
  (shiftedDressedAxisSwappedReMatrix A J lam D N c).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (p : ℕ)
    (σ τ : parityConfigS Λ N p) :
    shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ =
      shiftedDressedAxisSwappedReMatrix A J lam D N c σ.1 τ.1 := rfl

/-- The parity-block shifted matrix is entrywise non-negative. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 ≤ lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re) {c : ℝ}
    (hc : ∀ σ, dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c) (p : ℕ)
    (σ τ : parityConfigS Λ N p) :
    0 ≤ shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ := by
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_apply]
  exact shiftedDressedAxisSwappedReMatrix_nonneg A hJim hJnn hJself hJbip hlam hlb hub hDim hDnn
    hc σ.1 τ.1

/-- The parity-block shifted matrix is symmetric for real couplings. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (c : ℝ) (p : ℕ) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsSymm := by
  have hS := shiftedDressedAxisSwappedReMatrix_isSymm_of_real (N := N) A hJ hlam hD c
  ext σ τ
  rw [Matrix.transpose_apply, shiftedDressedAxisSwappedReMatrixOnParityBlock_apply,
    shiftedDressedAxisSwappedReMatrixOnParityBlock_apply]
  exact congrFun (congrFun hS σ.1) τ.1

/-- Strict positivity of the parity-block shifted matrix diagonal for a strict shift `c`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_diag_pos
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ} (p : ℕ)
    {σ : parityConfigS Λ N p}
    (hc : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c) :
    0 < shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ σ := by
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_apply]
  exact shiftedDressedAxisSwappedReMatrix_diag_pos A J lam D N hc

end LatticeSystem.Quantum
