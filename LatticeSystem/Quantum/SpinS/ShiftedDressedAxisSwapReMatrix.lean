import LatticeSystem.Quantum.SpinS.DressedAxisSwapReMatrix

/-!
# The shifted real-part matrix of the dressed axis-swapped Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

`shiftedDressedAxisSwappedReMatrix A J λ D N c := c • 1 − ReMatrix` turns the dressed `Ĥ'`
real-part matrix into the **entrywise non-negative** Perron–Frobenius matrix (for `c` above all
diagonal entries, case (i) bipartite AFM): off-diagonal `= −ReMatrix ≥ 0` (#3780), diagonal
`= c − ReMatrix σσ ≥ 0`.  Its top eigenvalue corresponds to the dressed ground energy, and (by
irreducibility on each parity block + the simplicity bridge #3779) its top eigenspace is
one-dimensional per parity block.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

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

/-- **Entrywise non-negativity** of the shifted matrix for `c` above all diagonal entries (case (i)
bipartite AFM). -/
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

end LatticeSystem.Quantum
