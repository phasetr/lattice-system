import LatticeSystem.Quantum.SpinS.AndersonTower

/-!
# Tasaki §4.2: the staggered-field Hamiltonian `Ĥ_h = Ĥ − h Ô_L^{(1)}` (Theorem 4.13 setup)

Adding an infinitesimal staggered magnetic field `−h Ô_L^{(1)}` to the antiferromagnetic Heisenberg
Hamiltonian triggers spontaneous symmetry breaking.  This module records only the field Hamiltonian
`Ĥ_h = Ĥ − h Ô_L^{(1)}` (eq. (4.2.27)); Theorem 4.13 itself (eq. (4.2.28)),
`lim_{h↓0} liminf_{L↑∞} ⟨Φ_GS,h| Ô_L^{(1)}/L^d |Φ_GS,h⟩ ≥ m∗`, is **proved axiom-free** downstream
as `tanakaSSB_field_lowerBound` in `AndersonTowerTheorem413` (Rayleigh–Ritz variational, §3.4).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1, Theorem 4.13, eqs. (4.2.27)–(4.2.28), pp. 102–103 (footnote 26: rigorously `liminf`).
-/

namespace LatticeSystem.Quantum

open Matrix Filter

variable {N : ℕ}

/-- The **staggered-field Hamiltonian** `Ĥ_h = Ĥ − h Ô_L^{(1)}` (eq. (4.2.27)) on the
`d`-dimensional
hypercubic torus: the antiferromagnetic nearest-neighbor Heisenberg Hamiltonian minus an external
staggered field `h ≥ 0` coupled to the `1`-axis staggered order operator. -/
noncomputable def staggeredFieldHamiltonianS (d L N : ℕ) [NeZero L] (h : ℝ) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  heisenbergHamiltonianS (torusNNCoupling d L) N -
    (h : ℂ) • staggeredOrderOp1S (torusParitySublattice d L) N

end LatticeSystem.Quantum
