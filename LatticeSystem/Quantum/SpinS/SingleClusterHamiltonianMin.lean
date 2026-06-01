import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianEnergy

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

/-- **Single-cluster GS-sector witness gives the min-energy upper bound**:
if a non-zero vector lies in the predicted Problem 2.5.a GS Casimir sector,
then the Hermitian minimum eigenvalue of `singleClusterHamiltonianS z N`
is bounded above by `Re (singleClusterGSEnergyS z N)`.

This is the variational upper-bound half of the ground-energy equality.
The hypotheses are exactly the Clebsch--Gordan existence target:
`s_R = zN/2` and `s_tot = (z-1)N/2`. -/
theorem singleClusterHamiltonianS_hermitianMinEigenvalue_le_gs_of_gs_sector
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (hv_ne : v ≠ 0)
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
          (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 *
          ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) ≤
      (singleClusterGSEnergyS z N).re := by
  have hEig :
      (singleClusterHamiltonianS z N).mulVec v =
        singleClusterGSEnergyS z N • v :=
    singleClusterHamiltonianS_mulVec_eq_gs_energy_smul (z := z) N htot hR
  have hEigReal :
      (singleClusterHamiltonianS z N).mulVec v =
        (((singleClusterGSEnergyS z N).re : ℝ) : ℂ) • v := by
    rw [hEig]
    congr 1
    apply Complex.ext
    · simp
    · simp
  exact hermitian_min_eigenvalue_le_of_eigenvector_exists
    (singleClusterHamiltonianS_isHermitian z N) hv_ne hEigReal

/-- **Existential GS-sector version of the single-cluster min-energy upper
bound**: once the Clebsch--Gordan construction supplies a non-zero vector in
the predicted GS Casimir sector, the Hermitian minimum eigenvalue is at most
`Re (singleClusterGSEnergyS z N)`.

This packages the remaining representation-theoretic existence obligation as
one hypothesis, ready for the eventual Problem 2.5.a ground-energy equality. -/
theorem singleClusterHamiltonianS_hermitianMinEigenvalue_le_gs_of_exists_gs_sector
    (N : ℕ)
    (hexists : ∃ v : (Fin (z + 1) → Fin (N + 1)) → ℂ,
      v ≠ 0 ∧
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
          (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v ∧
        (leafSpinSSquared z N).mulVec v =
          ((z : ℂ) * (N : ℂ) / 2 *
            ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) ≤
      (singleClusterGSEnergyS z N).re := by
  rcases hexists with ⟨v, hv_ne, htot, hR⟩
  exact singleClusterHamiltonianS_hermitianMinEigenvalue_le_gs_of_gs_sector
    (z := z) N hv_ne htot hR

/-- **Single-cluster global spectral lower-bound bridge**:
if every non-zero real-energy eigenvector of `singleClusterHamiltonianS z N`
has energy at least `Re (singleClusterGSEnergyS z N)`, then the Hermitian
minimum eigenvalue is at least that predicted GS energy.

This packages the spectral/variational exhaustion obligation that remains for
Tasaki Problem 2.5.a after the GS-sector upper-bound bridge. -/
theorem singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_global_eigenvalue_lower
    (N : ℕ)
  (hglobal : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      (singleClusterGSEnergyS z N).re ≤ μ) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  let hH := singleClusterHamiltonianS_isHermitian z N
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hermitian_min_eigenvalue_mem_image hH)
  let v : (Fin (z + 1) → Fin (N + 1)) → ℂ := (hH.eigenvectorBasis i).ofLp
  have hv_ne : v ≠ 0 := by
    intro hv_zero
    have hbasis_zero : hH.eigenvectorBasis i = 0 := by
      ext σ
      exact congrFun hv_zero σ
    have hnorm : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    rw [hbasis_zero, norm_zero] at hnorm
    norm_num at hnorm
  have hv_eig :
      (singleClusterHamiltonianS z N).mulVec v =
        ((hermitianMinEigenvalue hH : ℝ) : ℂ) • v := by
    have heig := Matrix.IsHermitian.mulVec_eigenvectorBasis hH i
    rw [show ((hermitianMinEigenvalue hH : ℝ) : ℂ) =
        ((hH.eigenvalues i : ℝ) : ℂ) from by rw [hi]]
    convert heig using 2
  exact hglobal hv_ne hv_eig

/-- **Joint-Casimir data gives the global lower-bound callback**:
if every non-zero real-energy eigenvector of the single-cluster Hamiltonian
admits joint `Ŝ_tot²` / `Ŝ_R²` Casimir eigenvalues whose Casimir energy is at
least `Re (singleClusterGSEnergyS z N)`, then it satisfies the global
real-eigenvalue lower-bound callback used by the min-eigenvalue bridge.

This isolates the remaining spectral-exhaustion work: prove that every
`H`-eigenvector decomposes into such joint Casimir sectors and that their
Casimir energies lie above the predicted ground-state value. -/
theorem singleCluster_global_eigenvalue_lower_of_joint_casimir_energy_lower
    (N : ℕ)
    (hjoint : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      (singleClusterGSEnergyS z N).re ≤ μ := by
  intro μ v hv_ne hH
  rcases hjoint hv_ne hH with ⟨α, β, htot, hR, hlower⟩
  have hH_joint :
      (singleClusterHamiltonianS z N).mulVec v =
        ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2) • v :=
    singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
      (z := z) N htot hR
  have hμ :
      (μ : ℂ) = (α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2 :=
    smul_left_injective ℂ hv_ne (hH.symm.trans hH_joint)
  have hμ_re :
      (((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) = μ := by
    rw [← hμ]
    simp
  exact hlower.trans_eq hμ_re

/-- **Single-cluster min-energy lower bound from joint-Casimir lower data**:
the joint-Casimir lower callback implies
`Re (singleClusterGSEnergyS z N) ≤ hermitianMinEigenvalue H`.

This is the consumer-facing form of the spectral-exhaustion obligation for
Tasaki Problem 2.5.a. -/
theorem singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_joint_casimir_energy_lower
    (N : ℕ)
    (hjoint : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v ∧
        (singleClusterGSEnergyS z N).re ≤
          ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  exact singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_global_eigenvalue_lower
    (z := z) N
    (singleCluster_global_eigenvalue_lower_of_joint_casimir_energy_lower
      (z := z) N hjoint)

/-- **Single-cluster Casimir-sector arithmetic lower bound**:
if a joint sector has total-Casimir real part at least the predicted
`s_tot = (z - 1)N/2` value and leaf-Casimir real part at most the maximum
`s_R = zN/2` value, then its Casimir energy
`(α - N(N+2)/4 - β)/2` is at least `Re (singleClusterGSEnergyS z N)`.

This is the arithmetic part of the joint-Casimir lower callback; the remaining
spectral work is to justify these sector bounds for every `H`-eigenvector. -/
theorem singleClusterGSEnergyS_re_le_casimir_energy_of_joint_bounds
    (N : ℕ) {α β : ℂ}
    (htot_lower :
      ((z : ℝ) - 1) * (N : ℝ) / 2 *
          (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re)
    (hR_upper :
      β.re ≤ (z : ℝ) * (N : ℝ) / 2 *
          ((z : ℝ) * (N : ℝ) / 2 + 1)) :
    (singleClusterGSEnergyS z N).re ≤
      ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2).re := by
  rw [singleClusterGSEnergyS_re_eq]
  norm_num [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.add_re,
    Complex.normSq]
  nlinarith

/-- **Joint-Casimir sector bounds give the global lower-bound callback**:
if every non-zero real-energy eigenvector has joint Casimir eigenvalues
`α, β` satisfying the predicted total-Casimir lower bound and leaf-Casimir
upper bound, then it satisfies the global real-eigenvalue lower callback.

This packages the spectral statement needed after the arithmetic lower bound:
the remaining work is to prove that every `H`-eigenvector admits such
joint-Casimir sector bounds. -/
theorem singleCluster_global_eigenvalue_lower_of_joint_casimir_bounds
    (N : ℕ)
    (hjoint_bounds : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
            (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re ∧
        β.re ≤ (z : ℝ) * (N : ℝ) / 2 *
            ((z : ℝ) * (N : ℝ) / 2 + 1)) :
    ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      (singleClusterGSEnergyS z N).re ≤ μ := by
  exact singleCluster_global_eigenvalue_lower_of_joint_casimir_energy_lower
    (z := z) N (by
      intro μ v hv_ne hH
      rcases hjoint_bounds hv_ne hH with ⟨α, β, htot, hR, htot_lower, hR_upper⟩
      exact ⟨α, β, htot, hR,
        singleClusterGSEnergyS_re_le_casimir_energy_of_joint_bounds
          (z := z) N htot_lower hR_upper⟩)

/-- **Single-cluster min-energy lower bound from joint-Casimir sector bounds**:
the joint-Casimir sector bounds imply
`Re (singleClusterGSEnergyS z N) ≤ hermitianMinEigenvalue H`. -/
theorem singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_joint_casimir_bounds
    (N : ℕ)
    (hjoint_bounds : ∀ {μ : ℝ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ},
      v ≠ 0 →
      (singleClusterHamiltonianS z N).mulVec v = (μ : ℂ) • v →
      ∃ α β : ℂ,
        (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v ∧
        (leafSpinSSquared z N).mulVec v = β • v ∧
        ((z : ℝ) - 1) * (N : ℝ) / 2 *
            (((z : ℝ) - 1) * (N : ℝ) / 2 + 1) ≤ α.re ∧
        β.re ≤ (z : ℝ) * (N : ℝ) / 2 *
            ((z : ℝ) * (N : ℝ) / 2 + 1)) :
    (singleClusterGSEnergyS z N).re ≤
      hermitianMinEigenvalue (singleClusterHamiltonianS_isHermitian z N) := by
  exact singleClusterGSEnergyS_re_le_hermitianMinEigenvalue_of_global_eigenvalue_lower
    (z := z) N
    (singleCluster_global_eigenvalue_lower_of_joint_casimir_bounds
      (z := z) N hjoint_bounds)

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

end LatticeSystem.Quantum
