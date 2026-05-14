import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Casimir invariance of the predicted toy-Hamiltonian GS subspace

The predicted GS subspace `bipartiteToyGroundStateSubspacePredicted A N`
is defined as the meet of three Casimir eigenspaces. Each of the
three Casimirs trivially preserves its own eigenspace component
(by scalar-multiplication closure), so the meet is invariant under
each:

* `Submodule.map (Ŝ_tot)².mulVecLin (predicted GS) ≤ predicted GS`.
* `Submodule.map (Ŝ_A)².mulVecLin (predicted GS) ≤ predicted GS`.
* `Submodule.map (Ŝ_¬A)².mulVecLin (predicted GS) ≤ predicted GS`.

Each follows from the eigenspace membership unpacking + scalar
closure, identical structure to PR #2794's `Ĥ_toy_S`-invariance.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **(Ŝ_tot)²-invariance of the predicted GS subspace**: trivial
from the (Ŝ_tot)² eigenspace membership component. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSSquared Λ N).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  have hv' := hv
  obtain ⟨⟨h_tot, _⟩, _⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_tot
  rw [Matrix.mulVecLin_apply, h_tot]
  exact Submodule.smul_mem _ _ hv'

set_option linter.style.longLine false in
/-- **(Ŝ_A)²-invariance of the predicted GS subspace**: trivial
from the (Ŝ_A)² eigenspace membership component. -/
theorem bipartiteToyGroundStateSubspacePredicted_sublatticeSpinSquaredS_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (sublatticeSpinSquaredS N A).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  have hv' := hv
  obtain ⟨⟨_, h_A⟩, _⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_A
  rw [Matrix.mulVecLin_apply, h_A]
  exact Submodule.smul_mem _ _ hv'

set_option linter.style.longLine false in
/-- **(Ŝ_¬A)²-invariance of the predicted GS subspace**: trivial
from the (Ŝ_¬A)² eigenspace membership component. -/
theorem bipartiteToyGroundStateSubspacePredicted_sublatticeSpinSquaredS_complement_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  have hv' := hv
  obtain ⟨_, h_B⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_B
  rw [Matrix.mulVecLin_apply, h_B]
  exact Submodule.smul_mem _ _ hv'

end LatticeSystem.Quantum
