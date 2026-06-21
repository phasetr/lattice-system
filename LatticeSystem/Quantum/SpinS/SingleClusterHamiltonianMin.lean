import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianEnergy
import LatticeSystem.Quantum.SpinS.SingleClusterCoupledSectorEnergy
import LatticeSystem.Quantum.SpinS.SingleClusterLeafCasimirBound
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianMinCore

/-!
# Minimum-eigenvalue bridge for the single-cluster Hamiltonian

Tasaki Problem 2.5.a predicts the ground-state energy
`-S(1 + zS)` for the single-cluster Hamiltonian
`singleClusterHamiltonianS z N`.  The restored Casimir framework already
shows that every non-zero vector in the predicted GS Casimir sector is an
eigenvector with eigenvalue `singleClusterGSEnergyS z N`.

This companion packages the variational upper-bound consequence:
the Hermitian minimum eigenvalue of the single-cluster Hamiltonian is at most
the real part of `singleClusterGSEnergyS z N`, provided such a non-zero
GS-sector vector is available.  The remaining mathematical work is the
Clebsch--Gordan construction of that vector and the spectral lower-bound /
exhaustion argument.  The lower-bound consumer is also packaged here: a global
lower bound for all non-zero real-energy eigenvectors gives the reverse
minimum-eigenvalue inequality, and together with a GS-sector witness gives the
conditional equality.  A further bridge reduces that global callback to
joint-Casimir spectral-exhaustion data plus the corresponding Casimir-energy
lower bound.

Reference:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (z : ℕ)

/-- **Single-cluster min-energy lower bound from joint total-Casimir lower
data**: joint Casimir eigenvalues plus the predicted lower bound on the total
Casimir eigenvalue imply
`Re (singleClusterGSEnergyS z N) ≤ hermitianMinEigenvalue H`.

The leaf-Casimir upper bound is supplied internally by the single-cluster
leaf-Casimir spectral maximum theorem. -/
theorem singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_joint_casimir_total_lower
    (N : ℕ)
    (hjoint_total_lower : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
          (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  exact singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_global_eigenvalue_lower
    (z := z) N
    (singleCluster_global_eigenvalue_lower_of_joint_casimir_total_lower
      (z := z) N hjoint_total_lower)

/-- **Coupled leaf/center sector data give the global lower-bound callback**:
if `1 ≤ z` and every non-zero real-energy `H`-eigenvector belongs to a
magnetization level and is a joint eigenvector of the total and leaf Casimirs,
then it satisfies the single-cluster ground-energy lower bound.

This is the single-cluster specialization of the Clebsch--Gordan coupled-sector
energy lower bound.  It avoids assuming the raw all-sector total-Casimir lower
bound directly; the remaining spectral work is to provide the sector data for
each real-energy eigenvector. -/
theorem singleCluster_global_eigenvalue_lower_of_coupled_leaf_sector
    (N : ℕ) (hz : 1 ≤ z)
    (hsector : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ k : ℕ, ∃ α β : ℂ,
        v ∈ magSubspaceS (Fin (z + 1)) N
          ((k : ℂ) - ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2)) ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v) :
    ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      (singleClusterGSEnergyS z N).re ≤ μ := by
  exact singleCluster_global_eigenvalue_lower_of_joint_casimir_energy_lower
    (z := z) N (by
      intro μ v hv_ne hH
      rcases hsector hv_ne hH with ⟨k, α, β, hv_mem, htot, hR⟩
      exact ⟨α, β, htot, hR,
        singleClusterGSEnergyS_re_le_casimir_energy_of_coupled_leaf_sector
          (z := z) N hz k hv_ne hv_mem htot hR⟩)

/-- **Single-cluster min-energy lower bound from coupled leaf/center sectors**:
the coupled leaf/center sector data imply
`Re (singleClusterGSEnergyS z N) ≤ hermitianMinEigenvalue H`. -/
theorem singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_coupled_leaf_sector
    (N : ℕ) (hz : 1 ≤ z)
    (hsector : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ k : ℕ, ∃ α β : ℂ,
        v ∈ magSubspaceS (Fin (z + 1)) N
          ((k : ℂ) - ((Fintype.card (Fin (z + 1)) : ℂ) * (N : ℂ) / 2)) ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  exact singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_global_eigenvalue_lower
    (z := z) N
    (singleCluster_global_eigenvalue_lower_of_coupled_leaf_sector
      (z := z) N hz hsector)

/-- **Single-cluster conditional min-energy equality from a GS-sector witness and
global lower bound**: a concrete non-zero vector in the predicted GS Casimir
sector gives the upper bound, while the global real-eigenvalue lower-bound
callback gives the reverse inequality. -/
theorem singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_global_lower
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hglobal : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      (singleClusterGSEnergyS z N).re ≤ μ) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  apply le_antisymm
  · exact singleClusterHamiltonianS_hermitianMinEigenvalue_le_gs_of_gs_sector
      (z := z) N hv_ne htot hR
  · exact singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_global_eigenvalue_lower
      (z := z) N hglobal

/-- **Existential conditional min-energy equality for the single-cluster
Hamiltonian**: once the Clebsch--Gordan construction supplies a non-zero vector
in the predicted GS Casimir sector and the spectral lower-bound callback rules
out lower real eigenvalues, the Hermitian minimum eigenvalue equals
`Re (singleClusterGSEnergyS z N)`. -/
theorem singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_exists_gs_sector_and_global_lower
    (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hglobal : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      (singleClusterGSEnergyS z N).re ≤ μ) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  rcases hexists with ⟨v, hv_ne, htot, hR⟩
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_global_lower
    (z := z) N hv_ne htot hR hglobal

/-- **Single-cluster conditional equality from a GS-sector witness and
joint-Casimir lower data**: the witness gives the upper bound, and the
joint-Casimir lower callback gives the reverse inequality. -/
theorem singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_joint_lower
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_global_lower
    (z := z) N hv_ne htot hR
    (singleCluster_global_eigenvalue_lower_of_joint_casimir_energy_lower
      (z := z) N hjoint)

/-- **Existential conditional equality from joint-Casimir lower data**:
the Clebsch--Gordan witness package gives the upper bound, while the
joint-Casimir lower callback gives the reverse inequality. -/
theorem singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_exists_gs_sector_and_joint_lower
    (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  rcases hexists with ⟨v, hv_ne, htot, hR⟩
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_joint_lower
    (z := z) N hv_ne htot hR hjoint

/-- **Single-cluster conditional equality from same-energy joint-Casimir
witnesses**: a concrete predicted GS-sector vector gives the upper bound,
while the existential same-energy joint-Casimir witness callback gives the
reverse inequality. -/
theorem
    singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_exists_joint_lower
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ, ∃ u : (Fin (z + 1) → Fin (N + 1)) → ℂ,
        u ≠ 0 ∧
        (singleClusterHamiltonianS z N).mulVec u = (μ : ℂ) • u ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec u = α • u ∧
        (leafSpinSSquared z N).mulVec u = β • u ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_global_lower
    (z := z) N hv_ne htot hR
    (singleCluster_global_eigenvalue_lower_of_exists_joint_casimir_energy_lower
      (z := z) N hjoint)

/-- **Existential conditional equality from same-energy joint-Casimir
witnesses**: the Clebsch--Gordan witness package gives the upper bound, while
the existential same-energy joint-Casimir witness callback gives the reverse
inequality. -/
theorem
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_exists_joint_lower
    (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ, ∃ u : (Fin (z + 1) → Fin (N + 1)) → ℂ,
        u ≠ 0 ∧
        (singleClusterHamiltonianS z N).mulVec u = (μ : ℂ) • u ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec u = α • u ∧
        (leafSpinSSquared z N).mulVec u = β • u ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  rcases hexists with ⟨v, hv_ne, htot, hR⟩
  exact
    singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_exists_joint_lower
      (z := z) N hv_ne htot hR hjoint

/-- **Single-cluster conditional equality from a GS-sector witness and
joint-Casimir sector bounds**: the witness gives the upper bound, while the
joint-Casimir sector-bounds callback gives the reverse inequality through the
arithmetic lower-bound bridge. -/
theorem singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_joint_casimir_bounds
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint_bounds : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
            (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re ∧
        β.re ≤ (z : ℝ) * (N : ℝ) / 2 *
            ((z : ℝ) * (N : ℝ) / 2 + 1)) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_global_lower
    (z := z) N hv_ne htot hR
    (singleCluster_global_eigenvalue_lower_of_joint_casimir_bounds
      (z := z) N hjoint_bounds)

/-- **Existential conditional equality from joint-Casimir sector bounds**:
the Clebsch--Gordan witness package gives the upper bound, while the
joint-Casimir sector-bounds callback gives the reverse inequality through the
arithmetic lower-bound bridge. -/
theorem singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_joint_casimir_bounds
    (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint_bounds : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
            (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re ∧
        β.re ≤ (z : ℝ) * (N : ℝ) / 2 *
            ((z : ℝ) * (N : ℝ) / 2 + 1)) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  rcases hexists with ⟨v, hv_ne, htot, hR⟩
  exact
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_joint_casimir_bounds
      (z := z) N hv_ne htot hR hjoint_bounds

/-- **Single-cluster conditional equality from a GS-sector witness and joint
total-Casimir lower data**: the witness gives the upper bound, while joint
Casimir spectral data plus the total-Casimir lower bound gives the reverse
inequality.  The leaf-Casimir upper bound is derived automatically from the
leaf spectral maximum theorem. -/
theorem singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_joint_casimir_total_lower
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint_total_lower : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
          (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_eq_gs_of_gs_sector_and_global_lower
    (z := z) N hv_ne htot hR
    (singleCluster_global_eigenvalue_lower_of_joint_casimir_total_lower
      (z := z) N hjoint_total_lower)

/-- **Existential conditional equality from joint total-Casimir lower data**:
the Clebsch--Gordan witness package gives the upper bound, while joint
Casimir spectral data plus the total-Casimir lower bound gives the reverse
inequality.  The leaf-Casimir upper bound is derived automatically from the
leaf spectral maximum theorem. -/
theorem
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_exists_gs_sector_and_joint_casimir_total_lower
    (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hjoint_total_lower : ∀ {μ : ℝ} {w : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec w = (μ : ℂ) • w →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec w = α • w ∧
        (leafSpinSSquared z N).mulVec w = β • w ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
          (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) =
      (singleClusterGSEnergyS z N).re := by
  rcases hexists with ⟨v, hv_ne, htot, hR⟩
  exact
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_gs_sector_and_joint_casimir_total_lower
      (z := z) N hv_ne htot hR hjoint_total_lower

end LatticeSystem.Quantum
