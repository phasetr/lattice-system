import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Single-cluster (star-graph) Heisenberg Hamiltonian (Tasaki Problem 2.5.a)

Defines `singleClusterHamiltonianS z N` for spin-`S` (with `S = N/2`)
on the `z + 1`-vertex star configuration with central vertex
`0 : Fin (z + 1)` and `z` leaves at sites `1, …, z`:

  `H = Σ_{j ∈ {1, …, z}} Ŝ_0 · Ŝ_j`

(Tasaki Problem 2.5.a, p. 38). Tasaki shows that the ground-state
energy of this Hamiltonian is `−S(1 + zS)`; the proof is deferred to
subsequent γ-5 steps (via Casimir decomposition `H = (1/2)((Ŝ_tot)² −
Ŝ_0² − Ŝ_R²)` where `Ŝ_R = Σ_{j=1}^z Ŝ_j`).

Note: this is the unordered (sum-over-leaves) form, not the ordered
double-sum convention of `heisenbergHamiltonianOnGraphS` over the
star graph (which would double-count each edge at unit coupling).

Tracked as part of γ-5 (Problem 2.5.a) toward Tasaki §2.5
(Issue #412).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- The single-cluster (star) Heisenberg Hamiltonian on `Fin (z + 1)`,
with central vertex `0` and `z` leaves at sites `1, …, z`:

  `H = Σ_{j ∈ {1,…,z}} Ŝ_0 · Ŝ_j`

(Tasaki Problem 2.5.a, p. 38). Tasaki claims the ground-state energy
is `−S(1 + zS)`; the proof is deferred to subsequent γ-5 steps. -/
noncomputable def singleClusterHamiltonianS (N : ℕ) :
    ManyBodyOpS (Fin (z + 1)) N :=
  ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0, spinSDot 0 j N

/-- The single-cluster Hamiltonian is Hermitian: sum of Hermitian
two-site dot products `spinSDot 0 j N` (γ-5 step 244). -/
theorem singleClusterHamiltonianS_isHermitian (N : ℕ) :
    (singleClusterHamiltonianS z N : ManyBodyOpS (Fin (z + 1)) N).IsHermitian := by
  unfold singleClusterHamiltonianS
  classical
  induction (Finset.univ.erase (0 : Fin (z + 1))) using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns]
    exact Matrix.IsHermitian.add (spinSDot_isHermitian 0 a N) ih

end LatticeSystem.Quantum
