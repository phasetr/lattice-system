import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEigenvalue

/-!
# Toy Hamiltonian eigenspace from joint Casimir eigenspaces

Sharpens PR #2774's pointwise eigenvalue identity to a subspace-
level inclusion: the joint `(Ŝ_tot)² ⊓ (Ŝ_A)² ⊓ (Ŝ_{¬A})²`-
eigenspace at eigenvalues `(α, β_A, β_B)` is contained in the
`Ĥ_toy_S`-eigenspace at eigenvalue `(α − β_A − β_B)`:

  `eigenspace(Ŝ_tot²)_α ⊓ eigenspace(Ŝ_A²)_β_A ⊓ eigenspace(Ŝ_¬A²)_β_B`
        `≤ eigenspace(Ĥ_toy_S)_{α−β_A−β_B}`.

This is the subspace-level form of Tasaki's energy formula for the
toy Hamiltonian on joint Casimir eigenvectors. Combined with the
upcoming triangle-inequality / angular-momentum-addition bounds on
admissible joint eigenvalues, it will give an explicit description
of the toy Hamiltonian spectrum and ground-state subspace, the
γ-4 / Theorem 2.3 program target.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Joint Casimir eigenspace lies inside the toy Hamiltonian
eigenspace**: at eigenvalues `(α, β_A, β_B)` for
`((Ŝ_tot)², (Ŝ_A)², (Ŝ_{¬A})²)`, every vector in the meet of
the three Casimir eigenspaces is a `Ĥ_toy_S`-eigenvector at
eigenvalue `(α − β_A − β_B)`.

This is the subspace-level lift of PR #2774's pointwise identity,
extracted via `Module.End.mem_eigenspace_iff` on the linear maps
`(totalSpinSSquared Λ N).mulVecLin`, `(sublatticeSpinSquaredS N A).mulVecLin`,
`(sublatticeSpinSquaredS N (!A)).mulVecLin`, and
`(heisenbergToyHamiltonianS A N).mulVecLin`. -/
theorem heisenbergToyHamiltonianS_jointCasimirEigenspace_le_eigenspace
    (A : Λ → Bool) (N : ℕ) (α β_A β_B : ℂ) :
    (Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin α
      ⊓ Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin β_A
      ⊓ Module.End.eigenspace
          (sublatticeSpinSquaredS N (fun x => !A x)).mulVecLin β_B)
        ≤ Module.End.eigenspace
            (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVecLin
            (α - β_A - β_B) := by
  intro v hv
  obtain ⟨⟨hα, hβ_A⟩, hβ_B⟩ := hv
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hα
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hβ_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hβ_B
  exact heisenbergToyHamiltonianS_mulVec_of_jointCasimirEigenvector
    A N v α β_A β_B hα hβ_A hβ_B

end LatticeSystem.Quantum
