import LatticeSystem.Quantum.SpinS.HeisenbergCore

/-!
# Tasaki §8.1.2–§8.1.3: hidden antiferromagnetic order and edge states (Theorem 8.2)

The **Haldane phase** of the anisotropic `S = 1` chain (8.1.1) is distinguished from the large-`D`
phase by **hidden antiferromagnetic order**, measured by the den Nijs–Rommelse string order
parameter
`O_string^{(α)}(D)` (§7.2.1) of its ground state.  It is conjectured that `O_string^{(α)}(D) > 0`
for
`0 ≤ D < D_c` (Haldane phase) and `= 0` for `D > D_c` (large-`D` phase), so the string order
parameter
is the order parameter separating the two phases.  The positivity in the Haldane phase is the
**hidden-order assumption** (8.1.10): for sufficiently large `L`,
`⟨Φ_GS| (Ô_string^{(α)} / L)² |Φ_GS⟩ ≥ q_α`  with `L`-independent `q_α > 0`.

Koma and Tasaki then proved, exactly as in the tower-of-states argument of Theorem 3.1
(Horsch–von der Linden), that hidden order forces low-lying excitations — the **edge states**:

**Theorem 8.2**: for the *open* anisotropic chain, assume the hidden-order bound (8.1.10) for the
unique ground state.  Then there exist **three independent excited states** `|Ψ_ν⟩` (`ν = 1, 2, 3`)
whose energies satisfy `E_GS < E_ν ≤ E_GS + C_ν / L` with `L`-independent constants `C_ν`.  Thus
hidden antiferromagnetic order forces a near four-fold degeneracy of low-lying states (the free
`S = 1/2` edge spins of the open chain).  Edge states are an open-boundary phenomenon, so the
theorem uses the open-chain Hamiltonian `openAnisotropicChainHamiltonianS`.

This module carries only the model definitions.  The string operator, the concrete hidden-order
predicate `HasStringLRO`, the `Z₂ × Z₂` symmetry analysis, the uniform energy estimates and the
proof of Theorem 8.2 live in the downstream leaves `AnisotropicEdgeStringOrder`,
`AnisotropicEdgeSymmetry`, `AnisotropicEdgeEnergy` and `AnisotropicEdgeStatesDischarge`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.2–§8.1.3, Theorem 8.2, eqs. (8.1.8)–(8.1.12), pp. 236–238; T. Koma, H. Tasaki, J. Stat.
Phys. **76**, 745 (1994); M. den Nijs, K. Rommelse, Phys. Rev. B **40**, 4709 (1989).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **open-chain anisotropic `S = 1` Hamiltonian** with crystal-field anisotropy `D`: the
open-boundary analogue of `anisotropicChainHamiltonianS`,
`Ĥ_D^open = Σ_{x=0}^{L-2} Ŝ_x·Ŝ_{x+1} + D Σ_x (Ŝ_x^{(3)})²` (eq. (8.1.1) with open boundary).  The
free boundary spins make the edge states of Theorem 8.2 possible. -/
noncomputable def openAnisotropicChainHamiltonianS (L : ℕ) (D : ℝ) : ManyBodyOpS (Fin L) 2 :=
  heisenbergHamiltonianS (openBondCoupling L) 2 +
    (D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2

end LatticeSystem.Quantum
