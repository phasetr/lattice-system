import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.MarshallSign
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank

/-!
# Marshall-dressed axis-swapped anisotropic Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The Marshall gauge dresses the axis-swapped Hamiltonian `Ĥ'` (2.5.15) by the diagonal sign
unitary `Θ_A = diagonal (marshallSignS A)`: `Ĥ'_dressed = Θ_A Ĥ' Θ_A`.  Since each Marshall sign
is `±1`, `Θ_A` is its own inverse, so this is a **similarity** — `Ĥ'_dressed` and `Ĥ'` (hence
`Ĥ`, via #3753) have equal `μ`-eigenspace dimensions.  In this dressed basis the off-diagonal
entries become sign-definite (`≤ 0` for case (i)), which is what powers the parity-sector
Perron–Frobenius degeneracy bound.

This file records the definition, the diagonal invariance, the similarity to `Ĥ'`, and the
resulting equal-degeneracy statement.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The Marshall-dressed axis-swapped anisotropic Hamiltonian, entrywise:
`marshallSignS A σ * marshallSignS A σ' * Ĥ'_{σ σ'}`. -/
noncomputable def dressedAxisSwappedAnisotropicHeisenbergS
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) : ManyBodyOpS Λ N :=
  fun σ σ' => marshallSignS A σ * marshallSignS A σ' *
    (axisSwappedAnisotropicHeisenbergS J lam D N) σ σ'

/-- Definitional unfolding of `dressedAxisSwappedAnisotropicHeisenbergS`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (σ σ' : Λ → Fin (N + 1)) :
    dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ σ' =
      marshallSignS A σ * marshallSignS A σ' *
        (axisSwappedAnisotropicHeisenbergS J lam D N) σ σ' := rfl

/-- Diagonal Marshall-dressed matrix element equals the bare one (`marshallSignS² = 1`). -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ σ =
      (axisSwappedAnisotropicHeisenbergS J lam D N) σ σ := by
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply, marshallSignS_sq, one_mul]

/-- The Marshall diagonal sign matrix is its own inverse (`marshallSignS² = 1` pointwise). -/
theorem marshallDiagonal_mul_self (A : Λ → Bool) :
    (Matrix.diagonal (marshallSignS A) : ManyBodyOpS Λ N) *
      Matrix.diagonal (marshallSignS A) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : Λ → Fin (N + 1) => marshallSignS A σ * marshallSignS A σ) =
      (fun _ => (1 : ℂ)) from funext (fun σ => marshallSignS_sq A σ)]
  exact Matrix.diagonal_one

/-- The dressed Hamiltonian is the Marshall conjugation of `Ĥ'`:
`Ĥ'_dressed = Θ_A Ĥ' Θ_A`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_eq_diag_conj
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    dressedAxisSwappedAnisotropicHeisenbergS A J lam D N =
      Matrix.diagonal (marshallSignS A) * axisSwappedAnisotropicHeisenbergS J lam D N *
        Matrix.diagonal (marshallSignS A) := by
  ext σ σ'
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  ring

/-- **Equal degeneracy of the dressed and bare axis-swapped Hamiltonians**: as `Θ_A` is
invertible, every `μ`-eigenspace of `Ĥ'_dressed` and of `Ĥ'` has equal dimension. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_eq
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ) =
      finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) :=
  matrix_similar_eigenspace_finrank_eq (marshallDiagonal_mul_self A) (marshallDiagonal_mul_self A)
    (dressedAxisSwappedAnisotropicHeisenbergS_eq_diag_conj A J lam D N) μ

end LatticeSystem.Quantum
