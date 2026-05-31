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
exhaustion argument.

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

end LatticeSystem.Quantum
