import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Néel state lies in the joint sublattice-Casimir eigenspace

The Néel state `Φ_Néel(A, N) = basisVecS (neelConfigOfS A N)` is
an exact eigenvector of both sublattice Casimirs at their
maximum-spin eigenvalues (PR #1283 spin-`S` mirror):

  `(Ŝ_A)² · |Φ_Néel⟩ = s_A·(s_A+1) · |Φ_Néel⟩` with `s_A = |A|·N/2`,
  `(Ŝ_¬A)² · |Φ_Néel⟩ = s_B·(s_B+1) · |Φ_Néel⟩` with `s_B = |¬A|·N/2`.

Hence the Néel state lies in the joint eigenspace

  `eigenspace((Ŝ_A)², s_A·(s_A+1)) ⊓ eigenspace((Ŝ_¬A)², s_B·(s_B+1))`.

This is **two-thirds of the predicted GS subspace conditions**
(the third being `(Ŝ_tot)²` at `(s_A−s_B)·((s_A−s_B)+1)`).
Néel is NOT in the full predicted GS subspace in general — its
`(Ŝ_tot)²` expectation `‖biw‖² + |Λ|·N/2` exceeds the predicted
`‖biw‖·(‖biw‖+1)` by `min·N` (PR #2901). This explains why the
GS is a non-trivial combination of `(Ŝ_tot)²`-eigenvectors within
the sublattice-Casimir joint eigenspace.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel state is in `(Ŝ_A)²` eigenspace at `s_A·(s_A+1)`**. -/
theorem neelStateOfS_mem_sublatticeSpinSquaredS_eigenspace :
    neelStateOfS A N ∈
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1)) := by
  rw [Module.End.mem_eigenspace_iff]
  rw [Matrix.mulVecLin_apply]
  exact sublatticeSpinSquaredS_mulVec_neelStateOfS A N

/-- **Néel state is in `(Ŝ_¬A)²` eigenspace at `s_B·(s_B+1)`**. -/
theorem neelStateOfS_mem_sublatticeSpinSquaredS_complement_eigenspace :
    neelStateOfS A N ∈
      Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1)) := by
  rw [Module.End.mem_eigenspace_iff]
  rw [Matrix.mulVecLin_apply]
  exact sublatticeSpinSquaredS_complement_mulVec_neelStateOfS A N

/-- **Néel state is in the joint sublattice-Casimir eigenspace**:
intersection of (Ŝ_A)² and (Ŝ_¬A)² eigenspaces at max-spin
eigenvalues. -/
theorem neelStateOfS_mem_joint_sublattice_casimir_eigenspace :
    neelStateOfS A N ∈
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) *
              (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) + 1))
        ⊓ Module.End.eigenspace
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) *
                (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2) + 1)) := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact neelStateOfS_mem_sublatticeSpinSquaredS_eigenspace A N
  · exact neelStateOfS_mem_sublatticeSpinSquaredS_complement_eigenspace A N

end LatticeSystem.Quantum
