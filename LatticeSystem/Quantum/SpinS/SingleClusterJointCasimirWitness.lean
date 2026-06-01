import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianMin
import LatticeSystem.Quantum.SpinS.SingleClusterCasimirInvariance
import LatticeSystem.Quantum.SpinS.SingleClusterMagnetizationProjection

/-!
# Single-cluster joint-Casimir witness bridge

This module composes the single-cluster magnetization projection bridge with
the invariant-submodule joint-Casimir bridge.  Starting from any non-zero
real-energy eigenvector of the single-cluster Hamiltonian, it extracts a
non-zero magnetization component with the same Hamiltonian eigenvalue, proves
that the corresponding Hamiltonian/magnetization submodule is non-zero, and
then obtains a non-zero same-energy simultaneous eigenvector of the total and
leaf Casimirs inside that submodule.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (z : ℕ)

/-- **Same-energy joint-Casimir witness from magnetization extraction**:
if every joint total/leaf Casimir eigenvector in every extracted non-zero
Hamiltonian/magnetization submodule satisfies the Casimir-energy lower bound,
then every non-zero real-energy Hamiltonian eigenvector admits the same-energy
joint-Casimir witness required by the lower-bound bridge.

The proof first extracts a non-zero magnetization component of the original
Hamiltonian eigenvector.  This component proves that the Hamiltonian eigenspace
intersected with the corresponding magnetization subspace is non-zero.  The
single-cluster invariant-submodule bridge then supplies a non-zero joint
total/leaf Casimir eigenvector in that same Hamiltonian eigenspace. -/
theorem singleCluster_exists_joint_casimir_energy_lower_of_mag_component_joint_lower
    [IsAlgClosed ℂ] (N : ℕ)
    (hlower : ∀ {μ M α β : ℂ}
      {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N μ M →
      w ≠ 0 →
      (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w →
      (leafSpinSSquared z N).mulVec w = β • w →
      (singleClusterGSEnergyS z N).re ≤
        ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ α β : ℂ, ∃ w : (Fin (z + 1) → Fin (N + 1)) → ℂ,
        w ≠ 0 ∧
        (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re := by
  intro μ v hv_ne hH
  rcases singleClusterHamiltonianS_eigenvec_exists_weight_component
      (z := z) N hv_ne hH with ⟨k, hk_ne, hkH, hkM⟩
  let M : ℂ :=
    ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)
  let vk : (Fin (z + 1) → Fin (N + 1)) → ℂ :=
    magProjFn (V := Fin (z + 1)) (N := N) M v
  have hvk_mem :
      vk ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N (μ : ℂ) M := by
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact hkH
    · exact hkM
  have hvk_ne : vk ≠ 0 := hk_ne
  have hne :
      singleClusterHamiltonianMagEigenspaceSubmodule z N (μ : ℂ) M ≠ ⊥ := by
    intro hbot
    have hvk_bot : vk ∈ (⊥ :
        Submodule ℂ ((Fin (z + 1) → Fin (N + 1)) → ℂ)) := by
      simpa [hbot] using hvk_mem
    exact hvk_ne ((Submodule.mem_bot _).mp hvk_bot)
  rcases exists_joint_casimir_eigenvector_in_singleClusterHamiltonianMagEigenspaceSubmodule
      (z := z) N (μ : ℂ) M hne with ⟨α, β, w, hw_mem, hw_ne, htot, hR⟩
  have hwH :
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w := by
    have hwH_mem := hw_mem.1
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hwH_mem
    exact hwH_mem
  exact ⟨α, β, w, hw_ne, hwH, htot, hR, hlower hw_mem hw_ne htot hR⟩

/-- **Single-cluster min-energy lower bound from extracted joint-Casimir
witnesses**: the magnetization/invariant-submodule witness bridge and a
Casimir-energy lower callback on the extracted joint vectors imply
`Re (singleClusterGSEnergyS z N) ≤ hermitianMinEigenvalue H`. -/
theorem singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_mag_component_joint_lower
    [IsAlgClosed ℂ] (N : ℕ)
    (hlower : ∀ {μ M α β : ℂ}
      {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N μ M →
      w ≠ 0 →
      (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w →
      (leafSpinSSquared z N).mulVec w = β • w →
      (singleClusterGSEnergyS z N).re ≤
        ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  exact
    singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_exists_joint_casimir_energy_lower
      (z := z) N
      (singleCluster_exists_joint_casimir_energy_lower_of_mag_component_joint_lower
        (z := z) N hlower)

/-- **Single-cluster conditional equality from a GS-sector witness and
extracted joint-Casimir lower data**: a concrete predicted GS-sector vector
gives the upper bound, while the magnetization/invariant-submodule witness
bridge gives the lower bound. -/
theorem
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_mag_joint_lower
    [IsAlgClosed ℂ] (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hlower : ∀ {μ M α β : ℂ}
      {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N μ M →
      w ≠ 0 →
      (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w →
      (leafSpinSSquared z N).mulVec w = β • w →
      (singleClusterGSEnergyS z N).re ≤
        ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact
    singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_exists_joint_lower
      (z := z) N hv_ne htot hR
      (singleCluster_exists_joint_casimir_energy_lower_of_mag_component_joint_lower
        (z := z) N hlower)

/-- **Existential conditional equality from predicted GS-sector existence and
extracted joint-Casimir lower data**: the Clebsch--Gordan witness package gives
the upper bound, while the magnetization/invariant-submodule witness bridge
gives the lower bound. -/
theorem
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_mag_joint_lower
    [IsAlgClosed ℂ] (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hlower : ∀ {μ M α β : ℂ}
      {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N μ M →
      w ≠ 0 →
      (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w →
      (leafSpinSSquared z N).mulVec w = β • w →
      (singleClusterGSEnergyS z N).re ≤
        ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_exists_joint_lower
      (z := z) N hexists
      (singleCluster_exists_joint_casimir_energy_lower_of_mag_component_joint_lower
        (z := z) N hlower)

end LatticeSystem.Quantum
