import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEigenspace
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `Ĥ_toy_S`-invariance of the predicted toy-Hamiltonian GS subspace

The predicted toy-Hamiltonian ground-state subspace
`bipartiteToyGroundStateSubspacePredicted A N` (PR #2778) is
invariant under the toy Hamiltonian itself:

  `Submodule.map Ĥ_toy_S.mulVecLin (predicted GS) ≤ predicted GS`.

Proof: PR #2775 shows the predicted GS is contained in the
`Ĥ_toy_S`-eigenspace at the predicted minimum eigenvalue. On this
eigenspace, `Ĥ_toy_S` acts as the scalar
`bipartiteToyMinEnergyPredicted A N`, so its image of any
`v ∈ predicted GS` is a scalar multiple of `v`, which remains in
the predicted GS subspace by submodule scalar closure.

This is a structural sanity check confirming the predicted GS
subspace is a `Ĥ_toy_S`-invariant subspace (consistent with being
an eigenspace component).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **`Ĥ_toy_S`-invariance of the predicted GS subspace**:
`Submodule.map Ĥ_toy_S.mulVecLin (bipartiteToyGroundStateSubspacePredicted A N)
  ≤ bipartiteToyGroundStateSubspacePredicted A N`. -/
theorem bipartiteToyGroundStateSubspacePredicted_heisenbergToyHamiltonianS_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  -- Use PR #2775: v ∈ predicted GS → v ∈ eigenspace(Ĥ_toy_S)_{predicted_min}.
  have h_eigen :=
    bipartiteToyGroundStateSubspacePredicted_le_heisenbergToyHamiltonianS_eigenspace
      (Λ := Λ) A N hv
  rw [Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_eigen
  rw [Matrix.mulVecLin_apply, h_eigen]
  -- Goal: (predicted_min • v) ∈ predicted GS.
  exact Submodule.smul_mem _ _ hv

end LatticeSystem.Quantum
