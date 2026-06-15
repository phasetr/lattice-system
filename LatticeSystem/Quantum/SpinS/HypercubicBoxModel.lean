import LatticeSystem.Lattice.HypercubicLattice
import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The finite-volume Heisenberg model on a hypercubic box

This connects the graph-centric infinite-volume substrate
(`Lattice/HypercubicLattice.lean`, Issue #4557) to the concrete spin-`S`
many-body operators: the **finite-volume Heisenberg model** on the box
`Λ_n ⊂ ℤᵈ`, obtained by instantiating the graph-centric spin-`S` Heisenberg
Hamiltonian `heisenbergHamiltonianOnGraphS` on the induced box graph
`hypercubicBoxGraph d n`.

The antiferromagnetic specialization `boxAFMHeisenbergHamiltonianS` is precisely
the finite-volume model whose `L ↑ ∞` thermodynamic limit is the §4.3
infinite-volume antiferromagnetic Heisenberg model (`InfiniteSpinSystem`); the
increasing boxes `Λ_n ↑ ℤᵈ` (PR1) provide the exhaustion along which the limit is
taken.

**Coupling convention.**  `heisenbergHamiltonianOnGraphS G J N` is the
*ordered-pair* sum `Σ_{x,y} (couplingOf G J)(x,y) · Ŝ_x · Ŝ_y`, in which each
*unordered* nearest-neighbor bond `{x, y}` is counted twice (once as `(x, y)` and
once as `(y, x)`).  To match Tasaki's *unordered-bond* convention
`Ĥ = Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y` with edge coefficient `+1`, the antiferromagnetic
specialization uses `J = 1/2` (so the doubled ordered sum yields coefficient `+1`
per unordered bond).

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §3.1, §4.3.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice

/-- The **finite-volume spin-`S` Heisenberg Hamiltonian** on the hypercubic box
`Λ_n ⊂ ℤᵈ` with uniform edge weight `J`: the graph-centric Heisenberg
Hamiltonian on the induced box graph `hypercubicBoxGraph d n`.  (Ordered-pair
sum; see the module note on the coupling convention.) -/
noncomputable def boxHeisenbergHamiltonianS (d n : ℕ) (J : ℂ) (N : ℕ) :
    ManyBodyOpS (hypercubicBoxVertex d n) N :=
  heisenbergHamiltonianOnGraphS (hypercubicBoxGraph d n) J N

/-- The finite-box Heisenberg Hamiltonian is the spin-`S` Heisenberg Hamiltonian
of the finite-volume coupling `hypercubicBoxCoupling d n J` (PR5), tying the
graph-centric substrate to the many-body operator. -/
theorem boxHeisenbergHamiltonianS_eq_heisenbergHamiltonianS_boxCoupling
    (d n : ℕ) (J : ℂ) (N : ℕ) :
    boxHeisenbergHamiltonianS d n J N =
      heisenbergHamiltonianS (hypercubicBoxCoupling d n J) N := rfl

/-- The finite-box spin-`S` Heisenberg Hamiltonian is **Hermitian** for any real
edge weight `J` (`star J = J`). -/
theorem boxHeisenbergHamiltonianS_isHermitian (d n : ℕ) {J : ℂ}
    (hJ : star J = J) (N : ℕ) :
    (boxHeisenbergHamiltonianS d n J N).IsHermitian :=
  heisenbergHamiltonianOnGraphS_isHermitian (hypercubicBoxGraph d n) hJ N

/-- The **finite-volume antiferromagnetic spin-`S` Heisenberg Hamiltonian** on the
box `Λ_n ⊂ ℤᵈ`: `Ĥ_{Λ_n} = Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y` in Tasaki's unordered-bond
convention (the edge weight `J = 1/2` compensates the doubled ordered-pair sum).
This is the finite-volume model whose thermodynamic limit is the §4.3
infinite-volume model. -/
noncomputable def boxAFMHeisenbergHamiltonianS (d n N : ℕ) :
    ManyBodyOpS (hypercubicBoxVertex d n) N :=
  boxHeisenbergHamiltonianS d n ((1 : ℂ) / 2) N

/-- The finite-volume antiferromagnetic Heisenberg Hamiltonian on the box is
**Hermitian** (the coupling `J = 1/2` is real). -/
theorem boxAFMHeisenbergHamiltonianS_isHermitian (d n N : ℕ) :
    (boxAFMHeisenbergHamiltonianS d n N).IsHermitian :=
  boxHeisenbergHamiltonianS_isHermitian d n (by norm_num) N

/-! ### Finite-volume ground-state energy and bond count

The finite-volume groundwork for the thermodynamic limit (Issue #4564): the
ground-state energy `E_{GS,n}` of the box model (the least eigenvalue of the
Hermitian Hamiltonian) and the bond count `|B_n|`, whose ratio is the
finite-volume energy density `E_{GS,n}/|B_n|` (Tasaki §4.3 eq. (4.3.4)).  All
defined/proved — no axioms; the `L↑∞` limit content is recorded separately. -/

/-- The **finite-volume ground-state energy** `E_{GS,n}` of the antiferromagnetic
box Heisenberg model: the least eigenvalue of the Hermitian Hamiltonian
`boxAFMHeisenbergHamiltonianS d n N`. -/
noncomputable def boxGroundEnergyS (d n N : ℕ) : ℝ :=
  hermitianMinEigenvalue (boxAFMHeisenbergHamiltonianS_isHermitian d n N)

/-- The ground-state energy is `≤` every eigenvalue of the box Hamiltonian (it is
the least eigenvalue). -/
theorem boxGroundEnergyS_le_eigenvalues (d n N : ℕ)
    (i : hypercubicBoxVertex d n → Fin (N + 1)) :
    boxGroundEnergyS d n N ≤ (boxAFMHeisenbergHamiltonianS_isHermitian d n N).eigenvalues i :=
  hermitian_min_eigenvalue_le (boxAFMHeisenbergHamiltonianS_isHermitian d n N) i

/-- The **bond count** `|B_n|` of the finite hypercubic box: the number of
nearest-neighbor bonds (edges of the induced box graph `hypercubicBoxGraph d n`). -/
noncomputable def boxBondCount (d n : ℕ) : ℕ :=
  (LatticeSystem.Lattice.hypercubicBoxGraph d n).edgeFinset.card

/-- The **finite-volume ground-state energy density** `E_{GS,n} / |B_n|` (per bond,
Tasaki §4.3 eq. (4.3.4)); the `L↑∞` limit of this quantity is the infinite-volume
ground-state energy density `ε_GS` (recorded separately as a documented axiom). -/
noncomputable def boxGroundEnergyDensityS (d n N : ℕ) : ℝ :=
  boxGroundEnergyS d n N / (boxBondCount d n : ℝ)

/-- The box has at least one nearest-neighbor bond once `0 < d` and `1 ≤ n`: the
origin `0` and the unit vector `e_i` are both in `Λ_n` and are adjacent.  Hence the
energy density has a positive denominator on the tail (so it is not vacuously
ill-defined). -/
theorem boxBondCount_pos (d n : ℕ) (hd : 0 < d) (hn : 1 ≤ n) : 0 < boxBondCount d n := by
  classical
  rw [boxBondCount, Finset.card_pos]
  let i : Fin d := ⟨0, hd⟩
  -- the origin `0` as a box vertex
  have h0mem : (fun _ : Fin d => (0 : ℤ)) ∈ LatticeSystem.Lattice.hypercubicBox d n := by
    rw [LatticeSystem.Lattice.mem_hypercubicBox]
    intro j
    show -(n : ℤ) < 0 ∧ (0 : ℤ) ≤ (n : ℤ)
    omega
  -- the unit vector `e_i` as a box vertex
  have h1mem : (fun j : Fin d => if j = i then (1 : ℤ) else 0) ∈
      LatticeSystem.Lattice.hypercubicBox d n := by
    rw [LatticeSystem.Lattice.mem_hypercubicBox]
    intro j
    show -(n : ℤ) < (if j = i then (1 : ℤ) else 0) ∧ (if j = i then (1 : ℤ) else 0) ≤ (n : ℤ)
    split_ifs <;> omega
  refine ⟨s(⟨fun _ => 0, h0mem⟩, ⟨fun j => if j = i then 1 else 0, h1mem⟩), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hypercubicBoxGraph_adj]
  refine ⟨i, ?_, ?_⟩
  · change |(0 : ℤ) - (if i = i then (1 : ℤ) else 0)| = 1
    simp
  · intro j hj
    change (0 : ℤ) = (if j = i then (1 : ℤ) else 0)
    rw [if_neg hj]

/-- **Tasaki §4.3 eq. (4.3.4), documented axiom.**  The finite-volume per-bond
ground-state energy density of the spin-`S` antiferromagnetic Heisenberg model on
the boxes `Λ_n ⊂ ℤᵈ` **converges** as the box grows (`n → ∞`); its limit is the
infinite-volume ground-state energy density `ε_GS = ε_GS(d, N)`.  Recorded as a
faithful documented axiom: the existence of the thermodynamic limit is the deep
analytic / operator-algebraic content.  The `0 < d` hypothesis ensures the box
has bonds (cf. `boxBondCount_pos`, so the per-bond density is well-defined on the
tail); `0 < N` restricts to genuine spin `S > 0`.  The limit value `ε_GS` is
existentially bound (pinned to the genuine limit of the box sequence, not an
arbitrary constant — unique by the Hausdorff property of `ℝ`). -/
axiom boxGroundEnergyDensityS_tendsto (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    ∃ εGS : ℝ,
      Filter.Tendsto (fun n : ℕ => boxGroundEnergyDensityS d n N)
        Filter.atTop (nhds εGS)

end LatticeSystem.Quantum
