import LatticeSystem.Quantum.SpinS.SingleClusterExtractedCoupledLower
import LatticeSystem.Quantum.SpinS.JointDiagonalPredictedEigenvector
import LatticeSystem.Quantum.SpinS.Theorem23ToyGSPredictedCasimir

/-!
# Single-cluster predicted GS joint-Casimir witness

This module specializes the bipartite predicted joint-Casimir eigenvector from
Tasaki §2.5 Theorem 2.3 to the single-cluster leaf/center partition of Problem
2.5.a.  The resulting non-zero total/leaf Casimir witness supplies the upper
bound side needed by the extracted coupled-sector equality wrapper.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38, and §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- **Single-cluster predicted GS joint-Casimir witness**: for `1 ≤ z`, the
leaf/center specialization of the bipartite predicted joint-Casimir eigenvector
gives a non-zero vector with total Casimir
`((z - 1)N/2)(((z - 1)N/2) + 1)` and leaf Casimir
`(zN/2)(zN/2 + 1)`. -/
theorem singleCluster_exists_gs_joint_casimir_witness
    (N : ℕ) (hz : 1 ≤ z) :
    ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v := by
  classical
  let leaf : Fin (z + 1) → Bool := fun x => decide (x ≠ 0)
  have horient :
      (Finset.univ.filter (fun x : Fin (z + 1) => (! leaf x) = true)).card ≤
        (Finset.univ.filter (fun x : Fin (z + 1) => leaf x = true)).card := by
    change
      (Finset.univ.filter
          (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)).card ≤
        (Finset.univ.filter
          (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card
    rw [singleCluster_compl_leaf_bool_card (z := z),
      singleCluster_leaf_bool_card (z := z)]
    exact hz
  obtain ⟨v, hv_ne, htot, hleaf, _hcenter⟩ :=
    exists_jointPredictedCasimir_eigenvector (Λ := Fin (z + 1)) (N := N) leaf horient
  refine ⟨v, hv_ne, ?_, ?_⟩
  · have hpred :
        ((tasaki23PredictedCasimirValue (V := Fin (z + 1)) leaf N : ℝ) : ℂ) =
          ((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1) := by
      rw [tasaki23PredictedCasimirValue_eq_sub (V := Fin (z + 1)) leaf horient]
      dsimp [leaf]
      rw [singleCluster_leaf_bool_card (z := z),
        singleCluster_compl_leaf_bool_card (z := z)]
      push_cast
      ring
    rwa [hpred] at htot
  · have hleaf_val :
        (((Finset.univ.filter
            (fun x : Fin (z + 1) => leaf x = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter
              (fun x : Fin (z + 1) => leaf x = true)).card : ℂ) *
            ((N : ℂ) / 2) + 1)) =
          (z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1) := by
      change
        (((Finset.univ.filter
            (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter
              (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℂ) *
            ((N : ℂ) / 2) + 1)) =
          (z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)
      rw [singleCluster_leaf_bool_card (z := z)]
      ring
    change
      (sublatticeSpinSquaredS N (fun x : Fin (z + 1) => decide (x ≠ 0))).mulVec v =
        (((Finset.univ.filter
            (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter
              (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℂ) *
            ((N : ℂ) / 2) + 1)) • v at hleaf
    rw [← leafSpinSSquared_eq_sublatticeSpinSquaredS_leaf (z := z) N] at hleaf
    rwa [hleaf_val] at hleaf

/-- **Single-cluster Problem 2.5.a final equality from the predicted joint
witness**: for `1 ≤ z`, the predicted leaf/center joint-Casimir witness supplies
the upper bound and the extracted coupled-sector bridge supplies the reverse
lower bound. -/
theorem singleClusterHamiltonianS_minEigenvalue_eq_gs_of_predicted_joint_witness
    [IsAlgClosed ℂ] (N : ℕ) (hz : 1 ≤ z) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_extracted_coupled
      (z := z) N hz (singleCluster_exists_gs_joint_casimir_witness (z := z) N hz)

end LatticeSystem.Quantum
