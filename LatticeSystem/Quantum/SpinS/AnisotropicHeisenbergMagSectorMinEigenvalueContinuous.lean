import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorContinuousReal
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorIsHermitianReal

/-!
# Parametric continuity of `(λ, D) ↦ hermitianMinEigenvalue (Ĥ_M(λ, D))`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For real-coupling `J` and a non-empty magnetisation sector `M`, the per-sector
minimum eigenvalue of the anisotropic Hamiltonian `Ĥ_M(λ, D)` is continuous
as a function of the real parameters `(λ, D) ∈ ℝ × ℝ`. **This is the analytic
ingredient needed by the obligation (2) deformation argument.**

Combines:
- PR #3956 `continuous_anisotropicHeisenbergS_magSector_submatrix_real` (entry-wise continuity).
- PR #3954 `anisotropicHeisenbergS_magSector_submatrix_isHermitian_real` (Hermitian instance).
- PR #3953 `Continuous.hermitianMinEigenvalue_comp` (Lipschitz continuity).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Per-sector min eigenvalue continuity in real `(λ, D)`**: combines the entry-wise
matrix continuity (PR #3956), the Hermitian instance at real `(λ, D)` (PR #3954), and the
Lipschitz-based continuity composition lemma (PR #3953). -/
theorem continuous_anisotropicHeisenbergS_magSector_minEigenvalue_real
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) [Nonempty (magConfigS Λ N M)] :
    Continuous (fun p : ℝ × ℝ => hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ p.1 p.2)) :=
  Continuous.hermitianMinEigenvalue_comp
    (continuous_anisotropicHeisenbergS_magSector_submatrix_real J N M)
    (fun p => anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M) hJ p.1 p.2)

end LatticeSystem.Quantum
