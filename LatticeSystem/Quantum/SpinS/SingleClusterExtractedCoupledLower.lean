import LatticeSystem.Quantum.SpinS.SingleClusterJointCasimirWitness
import LatticeSystem.Quantum.SpinS.SingleClusterCoupledSectorEnergy

/-!
# Extracted coupled lower bound for the single-cluster Hamiltonian

This module closes the single-cluster lower-bound callback left by the
magnetization/joint-Casimir witness bridge.  A non-zero vector in the extracted
Hamiltonian/magnetization submodule has an attained magnetization value.  After
reindexing that value from the projector convention `m_max - r` to the coupled
sector convention `k - m_max`, the existing leaf/center coupled-sector lower
bound applies directly.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38, and §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- **Extracted joint-Casimir vectors satisfy the coupled leaf-sector lower
bound**: if `1 ≤ z`, any non-zero joint total/leaf Casimir eigenvector in a
single-cluster Hamiltonian/magnetization submodule satisfies the
single-cluster Casimir-energy lower bound.  The proof reindexes the attained
magnetization sector from `m_max - magSumS σ` to the convention
`k - m_max` used by the coupled leaf-sector theorem. -/
theorem singleCluster_mag_component_joint_lower_of_coupled_leaf_sector
    (N : ℕ) (hz : 1 ≤ z) :
    ∀ {μ M α β : ℂ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N μ M →
      w ≠ 0 →
      (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w →
      (leafSpinSSquared z N).mulVec w = β • w →
      (singleClusterGSEnergyS z N).re ≤
        ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re := by
  intro μ M α β w hw_mem hw_ne htot hR
  have hw_mag :
      w ∈ magSubspaceS (Fin (z + 1)) N M := hw_mem.2
  have hMspec : ∃ σ : Fin (z + 1) → Fin (N + 1), magEigenvalueS σ = M := by
    by_contra h
    exact hw_ne ((Submodule.eq_bot_iff _).mp
      (magSubspaceS_eq_bot_of_not_in_spectrum (not_exists.mp h)) w hw_mag)
  obtain ⟨σ, hσ⟩ := hMspec
  let k : ℕ := Fintype.card (Fin (z + 1)) * N - magSumS σ
  have hsum_le : magSumS σ ≤ Fintype.card (Fin (z + 1)) * N :=
    magSumS_le σ
  have hM_eq : M =
      ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) -
        ((magSumS σ : ℕ) : ℂ) := by
    rw [← hσ, magEigenvalueS_def]
  have hM_target : M =
      (k : ℂ) - ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) := by
    rw [hM_eq]
    dsimp [k]
    rw [Nat.cast_sub hsum_le]
    push_cast
    ring
  have hw_sector :
      w ∈ magSubspaceS (Fin (z + 1)) N
        ((k : ℂ) - ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2)) := by
    rwa [← hM_target]
  exact
    singleClusterGSEnergyS_re_le_casimir_energy_of_coupled_leaf_sector
      (z := z) N hz k hw_ne hw_sector htot hR

/-- **Single-cluster Hermitian-min lower bound from extracted coupled sectors**:
for `1 ≤ z`, the magnetization/joint-Casimir witness bridge and the coupled
leaf/center sector-energy theorem imply
`Re (singleClusterGSEnergyS z N) ≤ hermitianMinEigenvalue H`. -/
theorem
    singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_extracted_coupled_leaf_sector
    [IsAlgClosed ℂ] (N : ℕ) (hz : 1 ≤ z) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  exact
    singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_mag_component_joint_lower
      (z := z) N
      (singleCluster_mag_component_joint_lower_of_coupled_leaf_sector
        (z := z) N hz)

/-- **Single-cluster conditional equality from a GS-sector witness and extracted
coupled sectors**: a concrete predicted GS-sector vector gives the upper bound,
while the extracted coupled-sector lower bridge gives the reverse inequality. -/
theorem
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_extracted_coupled_leaf_sector
    [IsAlgClosed ℂ] (N : ℕ) (hz : 1 ≤ z)
    {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_mag_joint_lower
      (z := z) N hv_ne htot hR
      (singleCluster_mag_component_joint_lower_of_coupled_leaf_sector
        (z := z) N hz)

/-- **Existential conditional equality from predicted GS-sector existence and
extracted coupled sectors**: an existential predicted GS-sector package gives
the upper bound, while the extracted coupled-sector lower bridge gives the
reverse inequality. -/
theorem
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_extracted_coupled
    [IsAlgClosed ℂ] (N : ℕ) (hz : 1 ≤ z)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_mag_joint_lower
      (z := z) N hexists
      (singleCluster_mag_component_joint_lower_of_coupled_leaf_sector
        (z := z) N hz)

end LatticeSystem.Quantum
