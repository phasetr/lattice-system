import LatticeSystem.Quantum.SpinS.MagSectorLinearEquiv
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Sector finrank transfer

(PR #3909, Issue #3739): the LinearEquiv `magSectorLinearEquiv` (PR #3908)
lets us transfer finrank bounds between sector vectors and the corresponding
sector subspace of the full Hilbert space. The key application: a sector-matrix
`heisenbergHamiltonianSMatrixOnMagSector` eigenspace inequality transfers to a
full Hilbert space `⊓ sector subspace` inequality.

This is the building block for the within-admissible Perron–Frobenius `finrank ≤ 1`
input needed for the SU(2) symmetric Theorem 2.4 obligation (2.a) capstone.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Submodule

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Subspace from sector vectors**: the LinearEquiv `magSectorLinearEquiv`
identifies the sector subspace `magSubspaceS Λ N (|Λ|·N/2 - M)` (viewed as a
type via `↥`) with the sector-indexed vectors `magConfigS Λ N M → ℂ`. -/
theorem magSubspaceS_finrank_eq_sector
    (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) (M : ℕ) :
    finrank ℂ ↥(magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) =
      finrank ℂ (magConfigS Λ N M → ℂ) :=
  (LinearEquiv.finrank_eq (magSectorLinearEquiv Λ N M)).symm

end LatticeSystem.Quantum
