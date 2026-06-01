import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian
import LatticeSystem.Quantum.SpinS.CasimirWeightComponent

/-!
# Magnetization projection for the single-cluster Hamiltonian

This module proves that the single-cluster Hamiltonian preserves total
magnetization and commutes with the pointwise magnetization projections
`magProjFn`.  Consequently, every non-zero single-cluster eigenvector has a
non-zero magnetization component with the same energy.

This is one layer of the sector-decomposition route for Tasaki §2.5 Problem
2.5.a: after the coupled leaf/center sector-energy bridge, the remaining lower
bound needs magnetization and joint total/leaf Casimir sector data.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38, and §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Projection commutation from magnetization preservation on basis vectors**:
if an operator sends each computational basis vector into its own
magnetization eigenspace, then it commutes with the pointwise magnetization
projection `magProjFn`. -/
theorem mulVec_magProjFn_eq_of_mulVec_basisVecS_mem_magSubspaceS
    {A : ManyBodyOpS V N}
    (hA : ∀ τ : V → Fin (N + 1),
      A.mulVec (basisVecS τ) ∈ magSubspaceS V N (magEigenvalueS τ))
    (M : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    A.mulVec (magProjFn (V := V) (N := N) M v) =
      magProjFn (V := V) (N := N) M (A.mulVec v) := by
  funext σ
  by_cases hσM : magEigenvalueS σ = M
  · have hRHS : magProjFn M (A.mulVec v) σ = A.mulVec v σ := by
      unfold magProjFn
      simp [hσM]
    rw [hRHS]
    rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hτM : magEigenvalueS τ = M
    · change A σ τ * magProjFn M v τ = A σ τ * v τ
      unfold magProjFn
      rw [if_pos hτM]
    · change A σ τ * magProjFn M v τ = A σ τ * v τ
      have hne : magEigenvalueS σ ≠ magEigenvalueS τ := by
        rw [hσM]
        exact Ne.symm hτM
      rw [matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS (hA τ) hne]
      ring
  · have hRHS : magProjFn M (A.mulVec v) σ = 0 := by
      unfold magProjFn
      simp [hσM]
    rw [hRHS]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases hτM : magEigenvalueS τ = M
    · have hne : magEigenvalueS σ ≠ magEigenvalueS τ := by
        rw [hτM]
        exact hσM
      change A σ τ * magProjFn M v τ = 0
      rw [matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS (hA τ) hne,
        zero_mul]
    · change A σ τ * magProjFn M v τ = 0
      unfold magProjFn
      rw [if_neg hτM, mul_zero]

variable (z : ℕ)

/-- The single-cluster Hamiltonian commutes with total magnetization
`Ŝ_tot^(3)`. -/
theorem singleClusterHamiltonianS_commute_totalSpinSOp3 (N : ℕ) :
    Commute (singleClusterHamiltonianS z N)
      (totalSpinSOp3 (Fin (z + 1)) N) := by
  unfold singleClusterHamiltonianS
  classical
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact sub_eq_zero.mp
    (spinSDot_commutator_totalSpinSOp3 (0 : Fin (z + 1)) j N)

/-- The single-cluster Hamiltonian maps every magnetization subspace into
itself. -/
theorem singleClusterHamiltonianS_mulVec_mem_magSubspaceS_of_mem
    (N : ℕ) {M : ℂ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS (Fin (z + 1)) N M) :
    (singleClusterHamiltonianS z N).mulVec v ∈
      magSubspaceS (Fin (z + 1)) N M := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← (singleClusterHamiltonianS_commute_totalSpinSOp3
    (z := z) N).eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- Applying the single-cluster Hamiltonian to a computational basis vector
preserves the basis vector's magnetization sector. -/
theorem singleClusterHamiltonianS_mulVec_basisVecS_mem_magSubspaceS
    (N : ℕ) (σ : Fin (z + 1) → Fin (N + 1)) :
    (singleClusterHamiltonianS z N).mulVec (basisVecS σ) ∈
      magSubspaceS (Fin (z + 1)) N (magEigenvalueS σ) :=
  singleClusterHamiltonianS_mulVec_mem_magSubspaceS_of_mem (z := z) N
    (basisVecS_mem_magSubspaceS σ)

/-- The single-cluster Hamiltonian commutes with the pointwise magnetization
projection `magProjFn`. -/
theorem singleClusterHamiltonianS_mulVec_magProjFn_eq
    (N : ℕ) (M : ℂ) (v : (Fin (z + 1) → Fin (N + 1)) → ℂ) :
    (singleClusterHamiltonianS z N).mulVec
        (magProjFn (V := Fin (z + 1)) (N := N) M v) =
      magProjFn (V := Fin (z + 1)) (N := N) M
        ((singleClusterHamiltonianS z N).mulVec v) :=
  mulVec_magProjFn_eq_of_mulVec_basisVecS_mem_magSubspaceS
    (V := Fin (z + 1)) (N := N)
    (fun τ => singleClusterHamiltonianS_mulVec_basisVecS_mem_magSubspaceS
      (z := z) N τ)
    M v

/-- **Single-cluster weight-component extraction**: every non-zero
single-cluster Hamiltonian eigenvector has a non-zero magnetization component
which is again a Hamiltonian eigenvector with the same eigenvalue and lies in a
single magnetization subspace. -/
theorem singleClusterHamiltonianS_eigenvec_exists_weight_component
    (N : ℕ) {μ : ℂ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hH : (singleClusterHamiltonianS z N).mulVec v = μ • v) :
    ∃ k : Fin (Fintype.card (Fin (z + 1)) * N + 1),
      magProjFn
          (((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v ≠
        0 ∧
      (singleClusterHamiltonianS z N).mulVec
          (magProjFn
            (((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v) =
        μ • magProjFn
          (((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v ∧
      magProjFn
          (((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v ∈
        magSubspaceS (Fin (z + 1)) N
          (((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) := by
  classical
  have hsum_ne :
      (∑ k : Fin (Fintype.card (Fin (z + 1)) * N + 1),
        magProjFn
          (((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v) ≠
        0 := by
    rw [sum_magProjFn_eq (V := Fin (z + 1)) (N := N) v]
    exact hv
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  refine ⟨k, hk, ?_, magProjFn_mem_magSubspaceS _ v⟩
  rw [singleClusterHamiltonianS_mulVec_magProjFn_eq, hH, magProjFn_smul]

end LatticeSystem.Quantum
