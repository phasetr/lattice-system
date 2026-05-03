import LatticeSystem.Quantum.SpinS.ShiftedDressedMatrix
import LatticeSystem.Quantum.SpinS.MagConfig

/-!
# Sector-restricted dressed Heisenberg matrix
(Tasaki §2.5 Phase B-γ γ-3 PF prep)

For the spin-S Marshall–Lieb–Mattis theorem via Perron–Frobenius, the
relevant matrix is the dressed Heisenberg matrix RESTRICTED to a single
magnetization-`M` sector (the subtype `magConfigS V N M`). On the full
configuration space the dressed matrix is not irreducible (different
magnetization sectors are disconnected), but each sector restriction is
irreducible (under the bipartite reachability hypothesis).

This module defines the sector-restricted matrix via `Matrix.submatrix`
and proves the basic properties needed for PF.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The shifted dressed Heisenberg matrix restricted to the
magnetization-`M` sector. -/
noncomputable def shiftedDressedSReMatrixOnMagSector
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℝ :=
  (shiftedDressedSReMatrix A J N c).submatrix Subtype.val Subtype.val

/-- Definitional unfolding of `shiftedDressedSReMatrixOnMagSector`. -/
theorem shiftedDressedSReMatrixOnMagSector_apply
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    shiftedDressedSReMatrixOnMagSector A J N c M σ τ =
      shiftedDressedSReMatrix A J N c σ.1 τ.1 := rfl

/-- Non-negativity of the sector-restricted matrix, lifted from the
non-negativity of `shiftedDressedSReMatrix` (PR #828). -/
theorem shiftedDressedSReMatrixOnMagSector_nonneg
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) (M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (σ τ : magConfigS V N M) :
    0 ≤ shiftedDressedSReMatrixOnMagSector A J N c M σ τ := by
  rw [shiftedDressedSReMatrixOnMagSector_apply]
  exact shiftedDressedSReMatrix_nonneg A N c hJ_real hJ_nn hJ_sym
    hJ_bipartite hc σ.1 τ.1

end LatticeSystem.Quantum
