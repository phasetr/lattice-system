import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# Saturated FM joint eigenspace at `J = 0` equals the `(Ŝ_tot)²`
eigenspace

When `J = 0`, the Heisenberg Hamiltonian is identically zero, so
its eigenspace at the saturated value `saturatedFerromagnetEigenvalueS 0 N = 0`
is the entire multi-site Hilbert space. The saturated FM joint
eigenspace (the meet of two eigenspaces) thus simplifies to just
the `(Ŝ_tot)²`-eigenspace component:

  `saturatedFerromagnetJointEigenspace 0 N
     = Module.End.eigenspace (Ŝ_tot)².mulVecLin
         (saturatedFerromagnetCasimirEigenvalueS V N)`.

Combined with PR #2796 (`predicted GS = saturatedFerromagnetJointEigenspace 0 N`
at the saturated case), this yields the cleaner identification

  `predicted GS at |¬A| = 0
     = (Ŝ_tot)² eigenspace at m_max(m_max+1)`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **Saturated FM joint at J=0 is the `(Ŝ_tot)²`-eigenspace**: with
J=0 the H-eigenspace component trivialises (every vector satisfies
0 · v = 0 • v), so the joint reduces to the Casimir eigenspace
alone. -/
theorem saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace :
    saturatedFerromagnetJointEigenspace (V := V) (0 : V → V → ℂ) N =
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) := by
  apply le_antisymm
  · -- saturated FM joint ⊆ (Ŝ_tot)² eigenspace: trivially, since
    -- the joint is the meet of two eigenspaces.
    intro v hv
    obtain ⟨_, hCas⟩ := hv
    exact hCas
  · -- (Ŝ_tot)² eigenspace ⊆ saturated FM joint: need to check the
    -- H_0 component holds for any v in the (Ŝ_tot)² eigenspace.
    intro v hv
    refine ⟨?_, ?_⟩
    · -- v ∈ H_0 eigenspace at saturatedFerromagnetEigenvalueS 0 N = 0:
      -- H_0 = 0 operator, so H_0 · v = 0 = 0 • v.
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
          Matrix.mulVecLin_apply]
      have hH_zero : heisenbergHamiltonianS (Λ := V) (0 : V → V → ℂ) N = 0 := by
        unfold heisenbergHamiltonianS
        simp
      have hEig_zero : saturatedFerromagnetEigenvalueS
          (V := V) (0 : V → V → ℂ) N = 0 := by
        unfold saturatedFerromagnetEigenvalueS
        rw [hH_zero]
        simp
      rw [hH_zero, hEig_zero, Matrix.zero_mulVec, zero_smul]
    · -- v ∈ (Ŝ_tot)² eigenspace, given by hv.
      exact hv

end LatticeSystem.Quantum
