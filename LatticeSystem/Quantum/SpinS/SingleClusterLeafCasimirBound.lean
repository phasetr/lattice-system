import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian
import LatticeSystem.Quantum.SpinS.SublatticeCasimirSpectralBound

/-!
# Leaf-Casimir spectral bound for the single-cluster Hamiltonian

This module instantiates the general sublattice Casimir spectral max bound to
the leaf set of the single-cluster star graph.  The leaf Casimir
`leafSpinSSquared z N` is the sublattice Casimir for the Boolean predicate
`decide (x != 0)` on `Fin (z + 1)`, and the leaf set has cardinality `z`.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- The leaf set of `Fin (z + 1)`, written as a Boolean predicate, has cardinality `z`. -/
theorem singleCluster_leaf_bool_card :
    (Finset.univ.filter
        (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)).card = z := by
  have hfilter :
      (Finset.univ.filter
          (fun x : Fin (z + 1) => (decide (x ≠ 0) : Bool) = true)) =
        (Finset.univ : Finset (Fin (z + 1))).erase 0 := by
    ext x
    simp [and_comm]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (z + 1))),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The 1-axis leaf spin is the sublattice 1-axis spin for the noncentral sites. -/
theorem leafSpinSOp1_eq_sublatticeSpinSOp1_leaf (N : ℕ) :
    (leafSpinSOp1 z N : ManyBodyOpS (Fin (z + 1)) N) =
      sublatticeSpinSOp1 N (fun x : Fin (z + 1) => decide (x ≠ 0)) := by
  unfold leafSpinSOp1 sublatticeSpinSOp1
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp [and_comm]

/-- The 2-axis leaf spin is the sublattice 2-axis spin for the noncentral sites. -/
theorem leafSpinSOp2_eq_sublatticeSpinSOp2_leaf (N : ℕ) :
    (leafSpinSOp2 z N : ManyBodyOpS (Fin (z + 1)) N) =
      sublatticeSpinSOp2 N (fun x : Fin (z + 1) => decide (x ≠ 0)) := by
  unfold leafSpinSOp2 sublatticeSpinSOp2
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp [and_comm]

/-- The 3-axis leaf spin is the sublattice 3-axis spin for the noncentral sites. -/
theorem leafSpinSOp3_eq_sublatticeSpinSOp3_leaf (N : ℕ) :
    (leafSpinSOp3 z N : ManyBodyOpS (Fin (z + 1)) N) =
      sublatticeSpinSOp3 N (fun x : Fin (z + 1) => decide (x ≠ 0)) := by
  unfold leafSpinSOp3 sublatticeSpinSOp3
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp [and_comm]

/-- The single-cluster leaf Casimir is the sublattice Casimir of the noncentral sites. -/
theorem leafSpinSSquared_eq_sublatticeSpinSquaredS_leaf (N : ℕ) :
    (leafSpinSSquared z N : ManyBodyOpS (Fin (z + 1)) N) =
      sublatticeSpinSquaredS N (fun x : Fin (z + 1) => decide (x ≠ 0)) := by
  unfold leafSpinSSquared sublatticeSpinSquaredS
  rw [leafSpinSOp1_eq_sublatticeSpinSOp1_leaf,
    leafSpinSOp2_eq_sublatticeSpinSOp2_leaf,
    leafSpinSOp3_eq_sublatticeSpinSOp3_leaf]

/-- **Single-cluster leaf-Casimir spectral max bound**: every eigenvalue of
`leafSpinSSquared z N` is at most `(zN/2)(zN/2 + 1)` in real part. -/
theorem leafSpinSSquared_eigenvalue_re_le_max
    (N : ℕ) {β : ℂ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hleaf : (leafSpinSSquared z N).mulVec v = β • v) :
    β.re ≤ ((z : ℝ) * (N : ℝ) / 2) * (((z : ℝ) * (N : ℝ) / 2) + 1) := by
  have hleaf' :
      (sublatticeSpinSquaredS N (fun x : Fin (z + 1) => decide (x ≠ 0))).mulVec v =
        β • v := by
    rw [← leafSpinSSquared_eq_sublatticeSpinSquaredS_leaf (z := z) N]
    exact hleaf
  have hbound :=
    sublatticeSpinSquaredS_eigenvalue_re_le_sA
      (N := N) (fun x : Fin (z + 1) => decide (x ≠ 0)) hv hleaf'
  rwa [singleCluster_leaf_bool_card (z := z)] at hbound

end LatticeSystem.Quantum
