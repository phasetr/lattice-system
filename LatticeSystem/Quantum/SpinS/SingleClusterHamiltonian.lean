import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Single-cluster (star-graph) Heisenberg Hamiltonian (Tasaki Problem 2.5.a)

Defines `singleClusterHamiltonianS z N` for spin-`S` (with `S = N/2`)
on the star graph `K_{1,z}` with central vertex `0 : Fin (z + 1)` and
`z` leaves at sites `1, …, z`:

  `H = Σ_{j=1}^z Ŝ_0 · Ŝ_j`

(Tasaki Problem 2.5.a, p. 38). The ground-state energy of this
Hamiltonian is `−S(1 + zS) = −(N/2)(1 + z·N/2) = −N(2 + zN)/4`.

This is the `z + 1`-vertex star-graph instance of the Heisenberg
Hamiltonian; alternatively it can be written
`H = Ŝ_0 · (Σ_{j=1}^z Ŝ_j)` (sum over leaves).

Tracked as part of γ-5 (Problem 2.5.a) toward Tasaki §2.5
(Issue #412).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- The single-cluster (star-graph) Heisenberg Hamiltonian on `Fin (z + 1)`,
with central vertex `0` and `z` leaves at sites `1, …, z`:

  `H = Σ_{j ∈ {1,…,z}} Ŝ_0 · Ŝ_j`

(Tasaki Problem 2.5.a, p. 38). The ground state energy is `−S(1 + zS)`. -/
noncomputable def singleClusterHamiltonianS (N : ℕ) :
    ManyBodyOpS (Fin (z + 1)) N :=
  ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0, spinSDot 0 j N

end LatticeSystem.Quantum
