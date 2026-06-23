import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingUniqueness
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Tasaki §6.2 Theorem 6.3: eigenspace transfer through the symmetrization

The Marshall–Lieb–Mattis uniqueness machinery operates on
`heisenbergHamiltonianS (ringCouplingSym L) N`, while the physical chain is
`afmHeisenbergChainHamiltonianS L N`.  Since the former is `2 ·` the
latter (`heisenbergHamiltonianS_ringCouplingSym_eq`), their eigenspaces coincide with eigenvalues
scaled by `2`.  This module records the resulting **finrank transfer**, the bridge that carries
ground-state uniqueness (`finrank ≤ 1`) from the symmetrized operator back to the physical chain.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, p. 162.
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Eigenspace under a nonzero scalar multiple**: `eigenspace ((2:ℂ) • f) (2μ) = eigenspace f μ`
(the scalar `2` cancels in the eigenvalue equation). -/
theorem eigenspace_two_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V) (μ : ℂ) :
    End.eigenspace ((2 : ℂ) • f) ((2 : ℂ) * μ) = End.eigenspace f μ := by
  ext v
  rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff, LinearMap.smul_apply, mul_smul]
  constructor
  · intro h; exact smul_right_injective V (two_ne_zero) h
  · intro h; rw [h]

/-- **Eigenspace finrank transfer**: the `E`-eigenspace of the physical AFM chain and the
`2E`-eigenspace of the symmetrized Hamiltonian have equal dimension.  Carries `finrank ≤ 1`
(ground-state uniqueness) from the Marshall–Lieb–Mattis operator to the physical chain. -/
theorem afmHeisenberg_eigenspace_finrank_eq_ringCouplingSym (L N : ℕ) (E : ℂ) :
    Module.finrank ℂ
        (End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (ringCouplingSym L) N)) (2 * E)) =
      Module.finrank ℂ (End.eigenspace (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) E) := by
  have hop : Matrix.toLin' (heisenbergHamiltonianS (ringCouplingSym L) N) =
      (2 : ℂ) • Matrix.toLin' (afmHeisenbergChainHamiltonianS L N) := by
    rw [heisenbergHamiltonianS_ringCouplingSym_eq, map_smul]
  rw [hop, eigenspace_two_smul]

end LatticeSystem.Quantum
