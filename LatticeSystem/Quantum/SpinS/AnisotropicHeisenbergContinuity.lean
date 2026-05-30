import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the anisotropic Heisenberg Hamiltonian in `(λ, D)`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori) — obligation (2)
foundation.

The anisotropic Hamiltonian `anisotropicHeisenbergS J lam D N` is a polynomial
of degree 1 in `lam` and `D` (with fixed `J` and `N`). Hence its matrix-valued
function `(lam, D) ↦ anisotropicHeisenbergS J lam D N` is continuous on
`ℂ × ℂ`, and similarly each restriction to a fixed magnetisation sector is
continuous in `(lam, D)`.

This is the minimal prerequisite for the per-sector min-eigenvalue continuity
needed by the deformation argument of obligation (2): a 3-fold sector
degeneracy at some `(λ', D') ≠ (1, 0)` would contradict the obligation (1)
`≤ 2` bound established in PR #3938.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The two-site XXZ term `spinSDotXXZ x y · N` is continuous in the anisotropy
parameter `lam`. -/
theorem continuous_spinSDotXXZ (x y : Λ) (N : ℕ) :
    Continuous (fun lam : ℂ => spinSDotXXZ (Λ := Λ) x y lam N) := by
  unfold spinSDotXXZ
  exact continuous_const.add (Continuous.smul continuous_id continuous_const)

/-- The single-ion anisotropy term `singleIonAnisotropyS · N` is continuous in
the crystal-field parameter `D`. -/
theorem continuous_singleIonAnisotropyS (N : ℕ) :
    Continuous (fun D : ℂ => singleIonAnisotropyS (Λ := Λ) D N) := by
  unfold singleIonAnisotropyS
  exact Continuous.smul continuous_id continuous_const

/-- **The anisotropic Heisenberg Hamiltonian is jointly continuous in
`(lam, D)`**. The matrix-valued function `(lam, D) ↦ anisotropicHeisenbergS J lam D N`
is continuous on `ℂ × ℂ`, viewed in the elementwise topology on
`Matrix (Λ → Fin (N+1)) (Λ → Fin (N+1)) ℂ`. -/
theorem continuous_anisotropicHeisenbergS (J : Λ → Λ → ℂ) (N : ℕ) :
    Continuous (fun p : ℂ × ℂ => anisotropicHeisenbergS (Λ := Λ) J p.1 p.2 N) := by
  unfold anisotropicHeisenbergS
  refine Continuous.add ?_ ?_
  · refine continuous_finset_sum _ (fun x _ => continuous_finset_sum _ (fun y _ => ?_))
    exact Continuous.smul continuous_const
      ((continuous_spinSDotXXZ x y N).comp continuous_fst)
  · exact (continuous_singleIonAnisotropyS N).comp continuous_snd

end LatticeSystem.Quantum
