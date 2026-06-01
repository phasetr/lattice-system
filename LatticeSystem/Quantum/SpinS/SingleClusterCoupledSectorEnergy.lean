import LatticeSystem.Quantum.SpinS.SingleClusterLeafCasimirBound
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianEnergy
import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyBound

/-!
# Coupled-sector energy lower bound for the single-cluster Hamiltonian

This module connects the general Clebsch--Gordan coupled lower bound from
Tasaki §2.5 Theorem 2.3 to the single-cluster star graph in Problem 2.5.a.
The leaf set is treated as one sublattice and the central site as its
complement, so the existing toy-sector energy lower theorem supplies the
Casimir-energy lower bound after dividing by two.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38, and §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- The complement of the leaf set of `Fin (z + 1)` is the singleton center. -/
theorem singleCluster_compl_leaf_bool_card :
    (Finset.univ.filter
        (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)).card = 1 := by
  have hfilter :
      (Finset.univ.filter
          (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)) =
        ({0} : Finset (Fin (z + 1))) := by
    ext x
    simp
  rw [hfilter, Finset.card_singleton]

/-- The 1-axis spin on the center is the 1-axis sublattice spin of the leaf complement. -/
theorem sublatticeSpinSOp1_compl_leaf_eq_onSite_zero (N : ℕ) :
    sublatticeSpinSOp1 N (fun x : Fin (z + 1) => !(decide (x ≠ 0) : Bool)) =
      onSiteS (0 : Fin (z + 1)) (spinSOp1 N) := by
  unfold sublatticeSpinSOp1
  rw [Finset.sum_eq_single (0 : Fin (z + 1))]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- The 2-axis spin on the center is the 2-axis sublattice spin of the leaf complement. -/
theorem sublatticeSpinSOp2_compl_leaf_eq_onSite_zero (N : ℕ) :
    sublatticeSpinSOp2 N (fun x : Fin (z + 1) => !(decide (x ≠ 0) : Bool)) =
      onSiteS (0 : Fin (z + 1)) (spinSOp2 N) := by
  unfold sublatticeSpinSOp2
  rw [Finset.sum_eq_single (0 : Fin (z + 1))]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- The 3-axis spin on the center is the 3-axis sublattice spin of the leaf complement. -/
theorem sublatticeSpinSOp3_compl_leaf_eq_onSite_zero (N : ℕ) :
    sublatticeSpinSOp3 N (fun x : Fin (z + 1) => !(decide (x ≠ 0) : Bool)) =
      onSiteS (0 : Fin (z + 1)) (spinSOp3 N) := by
  unfold sublatticeSpinSOp3
  rw [Finset.sum_eq_single (0 : Fin (z + 1))]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- The leaf-complement sublattice Casimir is the single-site center Casimir. -/
theorem sublatticeSpinSquaredS_compl_leaf_eq_spinSDot_zero_zero (N : ℕ) :
    sublatticeSpinSquaredS N (fun x : Fin (z + 1) => !(decide (x ≠ 0) : Bool)) =
      spinSDot (0 : Fin (z + 1)) 0 N := by
  unfold sublatticeSpinSquaredS spinSDot
  rw [sublatticeSpinSOp1_compl_leaf_eq_onSite_zero,
    sublatticeSpinSOp2_compl_leaf_eq_onSite_zero,
    sublatticeSpinSOp3_compl_leaf_eq_onSite_zero]

/-- **Single-cluster coupled-sector Casimir-energy lower bound**: for `1 ≤ z`, a
joint total/leaf Casimir eigenvector in a magnetization level has single-cluster
Casimir energy at least the predicted ground-state energy.  The proof applies
the general coupled lower bound to the leaf/center partition and uses the
single-site center Casimir scalar. -/
theorem singleClusterGSEnergyS_re_le_casimir_energy_of_coupled_leaf_sector
    (N : ℕ) (hz : 1 ≤ z) (k : ℕ) {α β : ℂ}
    {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (hv_mem :
      v ∈ magSubspaceS (Fin (z + 1)) N
        ((k : ℂ) - ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2)))
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v)
    (hR : (leafSpinSSquared z N).mulVec v = β • v) :
    (singleClusterGSEnergyS z N).re ≤
      ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re := by
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
  have hleaf :
      (sublatticeSpinSquaredS N leaf).mulVec v = β • v := by
    change
      (sublatticeSpinSquaredS N (fun x : Fin (z + 1) => decide (x ≠ 0))).mulVec v =
        β • v
    rw [← leafSpinSSquared_eq_sublatticeSpinSquaredS_leaf (z := z) N]
    exact hR
  have hcenter :
      (sublatticeSpinSquaredS N (fun x => ! leaf x)).mulVec v =
        (((N : ℂ) * ((N : ℂ) + 2) / 4)) • v := by
    change
      (sublatticeSpinSquaredS N
          (fun x : Fin (z + 1) => !(decide (x ≠ 0) : Bool))).mulVec v =
        (((N : ℂ) * ((N : ℂ) + 2) / 4)) • v
    rw [sublatticeSpinSquaredS_compl_leaf_eq_spinSDot_zero_zero (z := z) N]
    exact spinSDot_self_mulVec_eq_smul N (0 : Fin (z + 1)) v
  have htoy :=
    toy_joint_eigenvector_energy_re_ge
      (V := Fin (z + 1)) (N := N) leaf k horient hv_ne hv_mem htot hleaf hcenter
  change
      ((((Finset.univ.filter
          (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℝ) *
            (N : ℝ) / 2 -
          ((Finset.univ.filter
            (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)).card : ℝ) *
            (N : ℝ) / 2) *
          ((((Finset.univ.filter
            (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℝ) *
              (N : ℝ) / 2 -
            ((Finset.univ.filter
              (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)).card : ℝ) *
              (N : ℝ) / 2) + 1) -
          ((Finset.univ.filter
            (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℝ) *
            (N : ℝ) / 2 *
            (((Finset.univ.filter
              (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card : ℝ) *
              (N : ℝ) / 2 + 1) -
          ((Finset.univ.filter
            (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)).card : ℝ) *
            (N : ℝ) / 2 *
            (((Finset.univ.filter
              (fun x : Fin (z + 1) => (!(decide (x ≠ 0) : Bool)) = true)).card : ℝ) *
              (N : ℝ) / 2 + 1) ≤
        (α - β - (N : ℂ) * ((N : ℂ) + 2) / 4).re) at htoy
  rw [singleCluster_leaf_bool_card (z := z),
    singleCluster_compl_leaf_bool_card (z := z)] at htoy
  rw [singleClusterGSEnergyS_re_eq]
  norm_num [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.add_re,
    Complex.normSq] at htoy ⊢
  nlinarith

end LatticeSystem.Quantum
