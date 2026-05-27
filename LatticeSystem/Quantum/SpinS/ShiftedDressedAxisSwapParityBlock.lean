import LatticeSystem.Quantum.SpinS.ShiftedDressedAxisSwapReMatrix
import LatticeSystem.Quantum.SpinS.ParityConfig

/-!
# The shifted dressed `Ĥ'` real-part matrix restricted to a magnetization-parity block

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Restricting the entrywise-non-negative shifted matrix `c • 1 − ReMatrix` (#3781) to a
magnetization-parity block `parityConfigS Λ N p` gives the Perron–Frobenius matrix of that block:
entrywise non-negative and symmetric (for real couplings, case (i) bipartite AFM).  Its top
eigenvalue is the dressed ground energy within the block; combined with parity-block
irreducibility and the simplicity bridge (#3779) it yields the `≤ 1` per-block degeneracy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

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

/-- The parity-block shifted matrix is entrywise non-negative (case (i) bipartite AFM, `c` above
all diagonal entries). -/
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

end LatticeSystem.Quantum
