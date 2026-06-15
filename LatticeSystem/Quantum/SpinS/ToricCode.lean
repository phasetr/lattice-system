import LatticeSystem.Quantum.SpinS.AKLT

/-!
# Tasaki §8.4: topological order in Kitaev's toric code model (Theorem 8.9)

Kitaev's **toric code** is the prototypical model with **topological order** — a nontrivial gapped
phase whose ground-state degeneracy is protected by the global topology of the lattice, *not* by any
symmetry, and is therefore *intrinsically* stable.  Qubits (`S = 1/2`) live on the **edges** `E` of
an
`L × L` square lattice with periodic boundary (a torus): `ToricEdge L = (ZMod L × ZMod L) × Fin 2`
(a vertex together with a direction, horizontal `0` or vertical `1`), so `|E| = 2 L²`.  The
Hamiltonian (eq. (8.4.1)) is a sum of commuting **stabilizers**:
`Ĥ_tc = −Σ_v ∏_{x∈A_v} σ̂_x^{(3)} − Σ_p ∏_{x∈B_p} σ̂_x^{(1)}`,
where `A_v` is the set of four edges incident to vertex `v` and `B_p` the four edges of plaquette
`p`.
All terms commute and have eigenvalues `±1`, so the spectrum is integral and the gap is at least
`2`;
on the torus the ground states are **four-fold degenerate**.

**Theorem 8.9** (Bravyi–Hastings–Michalakis): for the perturbed model `Ĥ_ε = Ĥ_tc + ε Σ_x V̂_x`
(eq. (8.4.19), with `V̂_x` of fixed range `r` and `‖V̂_x‖ ≤ 1`, *not* assumed symmetric or
translation-invariant), there is a constant `ε₀ > 0` such that for all `|ε| ≤ ε₀` and all `L` the
Hamiltonian has **four near-degenerate ground states** separated from the rest of the spectrum by a
nonzero constant **independent of `L`**.  The topological four-fold degeneracy is robust against
*arbitrary* local perturbations — unlike the Haldane-phase edge degeneracy, which needs a protecting
symmetry.

The torus lattice, the stabilizers, and both Hamiltonians are *defined concretely*.  The
perturbation
class and the four-fold near-degeneracy are honest uninterpreted markers (their faithful forms
involve
operator norms and the infinite-volume spectrum); Theorem 8.9 is a documented axiom, with `ε₀` and
the
separation `Δ` quantified outside `∀ L` so the stability is genuinely length-uniform.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.4, Theorem 8.9, eqs. (8.4.1), (8.4.19), pp. 288–297; A. Yu. Kitaev, Ann. Phys. **303**, 2
(2003); S. Bravyi, M. B. Hastings, S. Michalakis, J. Math. Phys. **51**, 093512 (2010).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ} [NeZero L]

/-- The **edge set** of the `L × L` toric-code lattice: a vertex `(i, j) ∈ ZMod L × ZMod L` together
with a direction `Fin 2` (`0` = horizontal edge to `(i+1, j)`, `1` = vertical edge to `(i, j+1)`).
There are `2 L²` edges; qubits live here. -/
abbrev ToricEdge (L : ℕ) : Type := (ZMod L × ZMod L) × Fin 2

/-- The **star** `A_v`: the four edges incident to the vertex `(i, j)` — the horizontal edges at
`(i, j)` and `(i−1, j)`, and the vertical edges at `(i, j)` and `(i, j−1)`. -/
def starEdges (L : ℕ) [NeZero L] (v : ZMod L × ZMod L) : Finset (ToricEdge L) :=
  {(v, 0), ((v.1 - 1, v.2), 0), (v, 1), ((v.1, v.2 - 1), 1)}

/-- The **plaquette** `B_p`: the four edges of the unit square at `(i, j)` — the horizontal edges at
`(i, j)` and `(i, j+1)`, and the vertical edges at `(i, j)` and `(i+1, j)`. -/
def plaquetteEdges (L : ℕ) [NeZero L] (p : ZMod L × ZMod L) : Finset (ToricEdge L) :=
  {(p, 0), ((p.1, p.2 + 1), 0), (p, 1), ((p.1 + 1, p.2), 1)}

/-- The single-edge **Pauli `Z`** `σ̂_e^{(3)} = 2 Ŝ_e^{(3)}` on edge `e`. -/
noncomputable def sigmaZS (e : ToricEdge L) : ManyBodyOpS (ToricEdge L) 1 :=
  (2 : ℂ) • spinSSiteOp3 e 1

/-- The single-edge **Pauli `X`** `σ̂_e^{(1)} = 2 Ŝ_e^{(1)}` on edge `e`. -/
noncomputable def sigmaXS (e : ToricEdge L) : ManyBodyOpS (ToricEdge L) 1 :=
  (2 : ℂ) • spinSSiteOp1 e 1

/-- The **star operator** `A_v = ∏_{x∈A_v} σ̂_x^{(3)}` — the product of the four `σ̂^{(3)}` on the
edges incident to vertex `v` (commuting diagonal operators on distinct edges). -/
noncomputable def starOperatorS (L : ℕ) [NeZero L] (v : ZMod L × ZMod L) :
    ManyBodyOpS (ToricEdge L) 1 :=
  ((starEdges L v).toList.map sigmaZS).prod

/-- The **plaquette operator** `B_p = ∏_{x∈B_p} σ̂_x^{(1)}` — the product of the four `σ̂^{(1)}` on
the edges of plaquette `p` (commuting operators on distinct edges). -/
noncomputable def plaquetteOperatorS (L : ℕ) [NeZero L] (p : ZMod L × ZMod L) :
    ManyBodyOpS (ToricEdge L) 1 :=
  ((plaquetteEdges L p).toList.map sigmaXS).prod

/-- The **toric code Hamiltonian** (eq. (8.4.1)) `Ĥ_tc = −Σ_v A_v − Σ_p B_p`: minus the sum of the
star operators over all vertices and the plaquette operators over all plaquettes.  All terms
commute,
have eigenvalues `±1`, and the ground states are four-fold degenerate on the torus. -/
noncomputable def toricCodeHamiltonianS (L : ℕ) [NeZero L] : ManyBodyOpS (ToricEdge L) 1 :=
  -(∑ v : ZMod L × ZMod L, starOperatorS L v) - ∑ p : ZMod L × ZMod L, plaquetteOperatorS L p

/-- The **perturbed toric code Hamiltonian** (eq. (8.4.19)) `Ĥ_ε = Ĥ_tc + ε Σ_x V̂_x`. -/
noncomputable def perturbedToricHamiltonianS (L : ℕ) [NeZero L] (ε : ℝ)
    (V : ToricEdge L → ManyBodyOpS (ToricEdge L) 1) : ManyBodyOpS (ToricEdge L) 1 :=
  toricCodeHamiltonianS L + (ε : ℂ) • ∑ x : ToricEdge L, V x

/-- **Local-perturbation marker** `IsToricPerturbation L r V`: the family `V_x` consists of local
operators of fixed range `r` with `‖V̂_x‖ ≤ 1`, not assumed symmetric or translation-invariant.  An
uninterpreted predicate. -/
axiom IsToricPerturbation (L : ℕ) [NeZero L] (r : ℕ)
    (V : ToricEdge L → ManyBodyOpS (ToricEdge L) 1) : Prop

/-- **Four-fold near-degeneracy marker** `HasFourNearlyDegenerateGroundStates H Δ`: the Hamiltonian
`H` has a four-dimensional cluster of near-degenerate low-energy states separated from the rest of
the
spectrum by at least `Δ`.  An uninterpreted predicate. -/
axiom HasFourNearlyDegenerateGroundStates {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (H : ManyBodyOpS Λ 1) (Δ : ℝ) : Prop

/-- **Tasaki Theorem 8.9 (stability of topological order, Bravyi–Hastings–Michalakis), AXIOM.**  For
range-`r` perturbations of the toric code there is a coupling threshold `ε₀ > 0` and a separation
`Δ > 0` — both **independent of the lattice size `L`** — such that for every `|ε| ≤ ε₀`, every `L`,
and every local perturbation family `V` (`IsToricPerturbation`), the perturbed Hamiltonian
`Ĥ_ε = Ĥ_tc + ε Σ_x V̂_x` has **four near-degenerate ground states** separated from the rest of the
spectrum by at least `Δ` (`HasFourNearlyDegenerateGroundStates`).  The topological four-fold
degeneracy is thus stable against *arbitrary* local perturbations, with no symmetry required —
protected by the global topology.  Recorded as a documented axiom. -/
axiom tasaki_theorem_8_9 (r : ℕ) :
    ∃ ε₀ Δ : ℝ, 0 < ε₀ ∧ 0 < Δ ∧ ∀ ε : ℝ, |ε| ≤ ε₀ →
      ∀ (L : ℕ) [NeZero L] (V : ToricEdge L → ManyBodyOpS (ToricEdge L) 1),
        IsToricPerturbation L r V →
          HasFourNearlyDegenerateGroundStates (perturbedToricHamiltonianS L ε V) Δ

end LatticeSystem.Quantum
