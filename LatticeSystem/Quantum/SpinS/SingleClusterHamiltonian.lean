import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.MultiSite

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

/-- At `z = 0` (single-vertex configuration), the Hamiltonian is zero
since there are no leaves to couple to: `Finset.univ.erase 0 = ∅` in
`Fin 1`. The expected ground-state energy `−S(1 + 0·S) = −S` is
**not** matched by `0`; this discrepancy reflects that Tasaki's
formula is intended for `z ≥ 1` (γ-5 step 245). -/
theorem singleClusterHamiltonianS_zero_z (N : ℕ) :
    (singleClusterHamiltonianS 0 N : ManyBodyOpS (Fin 1) N) = 0 := by
  unfold singleClusterHamiltonianS
  rw [show (Finset.univ.erase (0 : Fin 1) : Finset (Fin 1)) = ∅ by
    ext j
    simp [Fin.fin_one_eq_zero]]
  exact Finset.sum_empty

/-- The all-up state expectation of the single-cluster Hamiltonian:
`<Φ_⊤ | H | Φ_⊤> = z·(N/2)²` for `H = Σ_{j ≠ 0} Ŝ_0 · Ŝ_j` on
`Fin (z + 1)`.

Each two-site dot product `Ŝ_0 · Ŝ_j` at `j ≠ 0` evaluated on the
constant-`0` (all-up) configuration gives `(N/2 − 0)(N/2 − 0) = (N/2)²`
(via `spinSDot_apply_diag_of_ne`). Sum over `z` leaves gives `z·(N/2)²`.

This is far above Tasaki's true GS energy `−S(1 + zS) = −(N/2)(1 + zN/2)`
since the all-up state is in the maximum-`s_tot` sector (the highest
Casimir energy), not the minimum `s_tot = (z−1)S` sector
(γ-5 step 246). -/
theorem singleClusterHamiltonianS_allUp_expectation (N : ℕ) :
    dotProduct (star (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))))
        ((singleClusterHamiltonianS z N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)))) =
      (z : ℂ) * ((N : ℂ) / 2) ^ 2 := by
  unfold singleClusterHamiltonianS allAlignedStateS
  rw [Matrix.sum_mulVec, dotProduct_sum]
  have hEach : ∀ j ∈ Finset.univ.erase (0 : Fin (z + 1)),
      dotProduct (star (basisVecS (allAlignedConfigS (Fin (z + 1)) N 0)))
          ((spinSDot 0 j N).mulVec
            (basisVecS (allAlignedConfigS (Fin (z + 1)) N 0))) =
        ((N : ℂ) / 2) ^ 2 := by
    intro j hj
    rw [basisVecS_expectation_eq_diagonal]
    have h0j : (0 : Fin (z + 1)) ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [spinSDot_apply_diag_of_ne h0j]
    unfold allAlignedConfigS
    simp
    ring
  rw [Finset.sum_congr rfl hEach]
  rw [Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (z + 1))),
    Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

end LatticeSystem.Quantum
