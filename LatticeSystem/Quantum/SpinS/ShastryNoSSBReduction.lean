import LatticeSystem.Quantum.SpinS.ShastryNoSSB
import LatticeSystem.Quantum.SpinS.ReversalSymmetricGroundEnergy
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionSymmetry
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction

/-!
# Tasaki §4.1 Theorem 4.2: variational reduction to a scalar energy-gain condition

The one-dimensional staggered-field ring Hamiltonian `Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h Ô_L^{(3)}`
(eq. (4.1.9), p. 76) is the concrete instance of Tasaki's abstract symmetry-breaking field family
`Ĥ_h = Ĥ − h Ô_L` (eq. (3.4.19), p. 69).  The many-body spin reversal `Θ` commutes with the
Heisenberg part and reverses the staggered order operator, so it maps `Ĥ_h` to `Ĥ_{−h}`; this is
the concrete input that the abstract ground-energy layer of
`ReversalSymmetricGroundEnergy.lean` needs.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77; §3.4, eq. (3.4.19), p. 69.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **The many-body spin reversal negates the staggered field**: `Θ Ĥ_h Θ = Ĥ_{−h}` (eq. (4.1.9),
p. 76).  The Heisenberg part is fixed by `Θ` (it is the `λ = 1`, `D = 0` case of the anisotropic
Hamiltonian, which `manyBodyReversalS_conj_anisotropicHeisenbergS` shows is reversal invariant),
while `manyBodyReversalS_conj_staggeredOrderOpS` reverses `Ô_L^{(3)}`; the two signs combine to
flip `h`.  Holds for every ring size `L` — no parity assumption — because the reversal acts
site-by-site and never sees the sublattice pattern.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, eq. (4.1.9), p. 76. -/
theorem staggeredFieldChainHamiltonianS_conj_manyBodyReversalS (L : ℕ) (h : ℝ) (N : ℕ) :
    manyBodyReversalS (Fin L) N * staggeredFieldChainHamiltonianS L h N *
        manyBodyReversalS (Fin L) N =
      staggeredFieldChainHamiltonianS L (-h) N := by
  have hHeis : manyBodyReversalS (Fin L) N * heisenbergHamiltonianS (ringCoupling L) N *
      manyBodyReversalS (Fin L) N = heisenbergHamiltonianS (ringCoupling L) N := by
    rw [← anisotropicHeisenbergS_one_zero (ringCoupling L) N,
      manyBodyReversalS_conj_anisotropicHeisenbergS]
  unfold staggeredFieldChainHamiltonianS
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hHeis,
    manyBodyReversalS_conj_staggeredOrderOpS]
  simp [smul_neg, neg_smul]

end LatticeSystem.Quantum
