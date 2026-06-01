import LatticeSystem.Quantum.SpinS.SingleClusterLeafCasimirBound
import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir
import LatticeSystem.Math.InvariantSubmoduleEigenvector

/-!
# Single-cluster Casimir invariance

This module packages the concrete invariance inputs needed to apply the
abstract invariant-submodule eigenvector bridge to Tasaki §2.5 Problem 2.5.a.

For the single-cluster Hamiltonian `singleClusterHamiltonianS z N`, the existing
Casimir identity

`(2 : ℂ) • H = (Ŝ_tot)² - Ŝ_0² - (Ŝ_R)²`

shows that `H` commutes with both the total Casimir and the leaf Casimir.  These
commutation facts imply that the Hamiltonian eigenspace, intersected with a
fixed magnetization subspace, is invariant under both Casimir operators.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- The total Casimir commutes with the leaf Casimir in the single-cluster
star graph. -/
theorem singleCluster_totalSpinSSquared_commute_leafSpinSSquared (N : ℕ) :
    Commute (totalSpinSSquared (Fin (z + 1)) N)
      (leafSpinSSquared z N) := by
  rw [leafSpinSSquared_eq_sublatticeSpinSquaredS_leaf (z := z) N]
  exact (sublatticeSpinSquaredS_commute_totalSpinSSquared N
    (fun x : Fin (z + 1) => decide (x ≠ 0))).symm

/-- The single-cluster Hamiltonian commutes with the total Casimir. -/
theorem singleClusterHamiltonianS_commute_totalSpinSSquared (N : ℕ) :
    Commute (singleClusterHamiltonianS z N)
      (totalSpinSSquared (Fin (z + 1)) N) := by
  let H := singleClusterHamiltonianS z N
  let T := totalSpinSSquared (Fin (z + 1)) N
  let C0 := spinSDot (0 : Fin (z + 1)) 0 N
  let R := leafSpinSSquared z N
  have hR_T : Commute R T := by
    dsimp [R, T]
    exact (singleCluster_totalSpinSSquared_commute_leafSpinSSquared (z := z) N).symm
  have hC0_T : Commute C0 T := by
    dsimp [C0, T]
    exact spinSDot_self_commute (0 : Fin (z + 1)) N
      (totalSpinSSquared (Fin (z + 1)) N)
  have htwo : Commute ((2 : ℂ) • H) T := by
    dsimp [H, T, C0, R]
    rw [singleClusterHamiltonianS_two_smul_eq_casimir_diff (z := z) N]
    exact Commute.sub_left (Commute.sub_left (Commute.refl _) hC0_T) hR_T
  have hhalf := htwo.smul_left (1 / 2 : ℂ)
  dsimp [H] at hhalf ⊢
  simpa [smul_smul] using hhalf

/-- The single-cluster Hamiltonian commutes with the leaf Casimir. -/
theorem singleClusterHamiltonianS_commute_leafSpinSSquared (N : ℕ) :
    Commute (singleClusterHamiltonianS z N)
      (leafSpinSSquared z N) := by
  let H := singleClusterHamiltonianS z N
  let T := totalSpinSSquared (Fin (z + 1)) N
  let C0 := spinSDot (0 : Fin (z + 1)) 0 N
  let R := leafSpinSSquared z N
  have hT_R : Commute T R := by
    dsimp [T, R]
    exact singleCluster_totalSpinSSquared_commute_leafSpinSSquared (z := z) N
  have hC0_R : Commute C0 R := by
    dsimp [C0, R]
    exact spinSDot_self_commute (0 : Fin (z + 1)) N (leafSpinSSquared z N)
  have htwo : Commute ((2 : ℂ) • H) R := by
    dsimp [H, T, C0, R]
    rw [singleClusterHamiltonianS_two_smul_eq_casimir_diff (z := z) N]
    exact Commute.sub_left (Commute.sub_left hT_R hC0_R) (Commute.refl _)
  have hhalf := htwo.smul_left (1 / 2 : ℂ)
  dsimp [H] at hhalf ⊢
  simpa [smul_smul] using hhalf

/-- The Hamiltonian eigenspace intersected with a fixed magnetization subspace
for the single-cluster Hamiltonian. -/
noncomputable def singleClusterHamiltonianMagEigenspaceSubmodule
    (N : ℕ) (μ M : ℂ) :
    Submodule ℂ (((Fin (z + 1)) → Fin (N + 1)) → ℂ) :=
  Module.End.eigenspace (singleClusterHamiltonianS z N).mulVecLin μ ⊓
    magSubspaceS (Fin (z + 1)) N M

/-- The total-Casimir endomorphism commutes with the leaf-Casimir endomorphism
on the single-cluster Hilbert space. -/
theorem singleCluster_totalSpinSSquared_mulVecLin_commute_leafSpinSSquared_mulVecLin
    (N : ℕ) :
    Commute (totalSpinSSquared (Fin (z + 1)) N).mulVecLin
      (leafSpinSSquared z N).mulVecLin := by
  rw [Commute]
  apply LinearMap.ext
  intro v
  apply funext
  intro x
  change ((totalSpinSSquared (Fin (z + 1)) N).mulVec
      ((leafSpinSSquared z N).mulVec v)) x =
    ((leafSpinSSquared z N).mulVec
      ((totalSpinSSquared (Fin (z + 1)) N).mulVec v)) x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (singleCluster_totalSpinSSquared_commute_leafSpinSSquared (z := z) N).eq]

/-- The Hamiltonian/magnetization submodule is invariant under the total
Casimir. -/
theorem singleClusterHamiltonianMagEigenspaceSubmodule_totalSpinSSquared_invariant
    (N : ℕ) (μ M : ℂ) :
    singleClusterHamiltonianMagEigenspaceSubmodule z N μ M ≤
      (singleClusterHamiltonianMagEigenspaceSubmodule z N μ M).comap
        (totalSpinSSquared (Fin (z + 1)) N).mulVecLin := by
  intro v hv
  obtain ⟨hvH, hvM⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hvH ⊢
    change (singleClusterHamiltonianS z N).mulVec
        ((totalSpinSSquared (Fin (z + 1)) N).mulVec v) =
      μ • ((totalSpinSSquared (Fin (z + 1)) N).mulVec v)
    rw [Matrix.mulVec_mulVec,
      (singleClusterHamiltonianS_commute_totalSpinSSquared (z := z) N).eq,
      ← Matrix.mulVec_mulVec, hvH, Matrix.mulVec_smul]
  · exact totalSpinSSquared_mulVec_mem_magSubspaceS
      (Λ := Fin (z + 1)) (N := N) M hvM

/-- The Hamiltonian/magnetization submodule is invariant under the leaf
Casimir. -/
theorem singleClusterHamiltonianMagEigenspaceSubmodule_leafSpinSSquared_invariant
    (N : ℕ) (μ M : ℂ) :
    singleClusterHamiltonianMagEigenspaceSubmodule z N μ M ≤
      (singleClusterHamiltonianMagEigenspaceSubmodule z N μ M).comap
        (leafSpinSSquared z N).mulVecLin := by
  intro v hv
  obtain ⟨hvH, hvM⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hvH ⊢
    change (singleClusterHamiltonianS z N).mulVec
        ((leafSpinSSquared z N).mulVec v) =
      μ • ((leafSpinSSquared z N).mulVec v)
    rw [Matrix.mulVec_mulVec,
      (singleClusterHamiltonianS_commute_leafSpinSSquared (z := z) N).eq,
      ← Matrix.mulVec_mulVec, hvH, Matrix.mulVec_smul]
  · rw [leafSpinSSquared_eq_sublatticeSpinSquaredS_leaf (z := z) N]
    exact sublatticeSpinSquaredS_mulVec_mem_magSubspaceS
      (Λ := Fin (z + 1)) (N := N)
      (fun x : Fin (z + 1) => decide (x ≠ 0)) M hvM

/-- **Joint Casimir eigenvector in a non-zero single-cluster
Hamiltonian/magnetization submodule**: if the Hamiltonian eigenspace at `μ`,
intersected with the magnetization subspace at `M`, is non-zero, it contains a
non-zero simultaneous eigenvector of the total and leaf Casimirs. -/
theorem exists_joint_casimir_eigenvector_in_singleClusterHamiltonianMagEigenspaceSubmodule
    [IsAlgClosed ℂ] (N : ℕ) (μ M : ℂ)
    (hne : singleClusterHamiltonianMagEigenspaceSubmodule z N μ M ≠ ⊥) :
    ∃ α β : ℂ, ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ∈ singleClusterHamiltonianMagEigenspaceSubmodule z N μ M ∧ v ≠ 0 ∧
      (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
      (leafSpinSSquared z N).mulVec v = β • v := by
  simpa [Matrix.mulVecLin_apply] using
    LatticeSystem.Math.exists_joint_eigenvector_in_invariant_submodule
      (K := ℂ) (E := (Fin (z + 1) → Fin (N + 1)) → ℂ)
      (f := (totalSpinSSquared (Fin (z + 1)) N).mulVecLin)
      (g := (leafSpinSSquared z N).mulVecLin)
      (p := singleClusterHamiltonianMagEigenspaceSubmodule z N μ M)
      (singleClusterHamiltonianMagEigenspaceSubmodule_totalSpinSSquared_invariant
        (z := z) N μ M)
      (singleClusterHamiltonianMagEigenspaceSubmodule_leafSpinSSquared_invariant
        (z := z) N μ M)
      (singleCluster_totalSpinSSquared_mulVecLin_commute_leafSpinSSquared_mulVecLin
        (z := z) N)
      hne

end LatticeSystem.Quantum
