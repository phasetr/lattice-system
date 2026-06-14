import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.HaldaneConjecture

/-!
# Tasaki §7.3.3: the Briegel–Raussendorf (cluster / graph) state and Theorem 7.8

The **Briegel–Raussendorf state** (cluster state on a regular lattice, graph state in general) is
the
`S = 1/2` analogue of the VBS state: a short-range-entangled state with no Néel order but a hidden
string order, central to measurement-based quantum computation and the theory of symmetry-protected
topological phases.  On a graph `(Λ, B)` it is the unique ground state of the **stabilizer
Hamiltonian** (eq. (7.3.30))
`Ĥ_BR = −Σ_{x∈Λ} σ̂_x^{(1)} ∏_{y∈N(x)} σ̂_y^{(3)}`,
a sum of the commuting stabilizers `K̂_x = σ̂_x^{(1)} ∏_{y∼x} σ̂_y^{(3)}` (each `K̂_x² = 1`, so
`K̂_x` has eigenvalues `±1`).

**Theorem 7.8**: the cluster state `|Φ_C⟩` is the **unique** ground state of `Ĥ_BR`, with ground
energy `E_GS = −N` (`N = |Λ|`), and the energy gap above the ground state is exactly `2`.

We work with the vertex set `Λ = Fin L`.  The Pauli operators, the neighbour-`Z` product, the
stabilizers, and the stabilizer Hamiltonian are all *defined concretely*.  The cluster state itself
(the simultaneous `+1` eigenvector of every `K̂_x`) is carried by the uninterpreted marker
`IsClusterState`, and Theorem 7.8 — proved by mapping `Ĥ_BR` to the trivial paramagnet
`Ĥ_→ = −Σ_x σ̂_x^{(1)}` through the unitary `Û_C = ∏ Ĉ` of controlled-`Z` gates — is recorded as a
documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.3.3, Theorem 7.8, eqs. (7.3.29)–(7.3.37), pp. 217–220; H. J. Briegel, R. Raussendorf,
Phys.
Rev. Lett. **86**, 910 (2001); R. Raussendorf, H. J. Briegel, Phys. Rev. Lett. **86**, 5188 (2001).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The single-site **Pauli `X` operator** `σ̂_x^{(1)} = 2 Ŝ_x^{(1)}` on qubit site `x` (spin
`S = 1/2`, `N = 1`); on the basis `Fin 2` it is the off-diagonal flip `[[0,1],[1,0]]`. -/
noncomputable def pauliXS (x : Fin L) : ManyBodyOpS (Fin L) 1 :=
  (2 : ℂ) • spinSSiteOp1 x 1

/-- The single-site **Pauli `Z` operator** `σ̂_x^{(3)} = 2 Ŝ_x^{(3)}` on qubit site `x`; on the
basis
`Fin 2` it is the diagonal `diag(1, −1)` (eigenvalue `(−1)^{σ_x}`). -/
noncomputable def pauliZS (x : Fin L) : ManyBodyOpS (Fin L) 1 :=
  (2 : ℂ) • spinSSiteOp3 x 1

/-- The **neighbour-`Z` product** `∏_{y∈N(x)} σ̂_y^{(3)}` for a vertex `x` of the graph `G`: as each
`σ̂_y^{(3)}` is diagonal and the factors on distinct neighbours commute, the product is the single
diagonal operator multiplying a configuration `σ` by `∏_{y∼x} (−1)^{σ_y}`. -/
noncomputable def neighborZProduct (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (x : Fin L) :
    ManyBodyOpS (Fin L) 1 :=
  Matrix.diagonal fun cfg : Fin L → Fin 2 =>
    ∏ y ∈ Finset.univ.filter fun y : Fin L => G.Adj x y, (-1 : ℂ) ^ ((cfg y).val)

/-- The **Briegel–Raussendorf stabilizer** `K̂_x = σ̂_x^{(1)} ∏_{y∼x} σ̂_y^{(3)}` at vertex `x`.
Each
`K̂_x` is self-inverse (`K̂_x² = 1`) and they mutually commute, so they share an eigenbasis with
eigenvalues `±1`. -/
noncomputable def brStabilizer (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (x : Fin L) :
    ManyBodyOpS (Fin L) 1 :=
  pauliXS x * neighborZProduct G x

/-- The **Briegel–Raussendorf (graph-state) Hamiltonian** `Ĥ_BR = −Σ_x K̂_x` (eq. (7.3.30)): minus
the sum of the stabilizers over all vertices of the graph `G`. -/
noncomputable def graphStateHamiltonianS (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    ManyBodyOpS (Fin L) 1 :=
  (-1 : ℂ) • ∑ x : Fin L, brStabilizer G x

/-- **Cluster-state marker** `IsClusterState G Φ`: the state `Φ` is the Briegel–Raussendorf / graph
state of `G` (eq. (7.3.29)), the simultaneous `+1` eigenvector of every stabilizer `K̂_x`.  A
faithful
definition needs the explicit controlled-`Z` construction `Φ = Û_C Φ_→`; it is kept as an
uninterpreted predicate so Theorem 7.8 applies only to the genuine cluster state. -/
axiom IsClusterState (G : SimpleGraph (Fin L)) (Φ : (Fin L → Fin 2) → ℂ) : Prop

/-- **Tasaki Theorem 7.8 (the cluster state is the unique gapped ground state), AXIOM.**  The
Briegel–Raussendorf / graph state `Φ` (`IsClusterState`) is the **unique ground state** of the
stabilizer Hamiltonian `Ĥ_BR = −Σ_x K̂_x` (eq. (7.3.30)): the ground energy is `E_GS = −N`
(`N = |Λ| = L`), the gap above it is **exactly `2`** (`IsPositiveSpectralGap … 2`), and every
ground-energy eigenvector is a scalar multiple of `Φ`.  Proved by mapping `Ĥ_BR` to the trivial
paramagnet `Ĥ_→ = −Σ_x σ̂_x^{(1)}` (whose unique ground state is the product state `Φ_→`) through
the
unitary `Û_C = ∏ Ĉ` of controlled-`Z` gates with `Û_C² = 1`; recorded as a documented axiom. -/
axiom tasaki_theorem_7_8 (G : SimpleGraph (Fin L)) [DecidableRel G.Adj]
    (Φ : (Fin L → Fin 2) → ℂ) (hΦ : IsClusterState G Φ) :
    IsGroundEnergy (graphStateHamiltonianS G) (-(Fintype.card (Fin L) : ℝ)) ∧
      IsPositiveSpectralGap (graphStateHamiltonianS G) 2 ∧ Φ ≠ 0 ∧
        ∀ Ψ : (Fin L → Fin 2) → ℂ, Ψ ≠ 0 →
          (graphStateHamiltonianS G).mulVec Ψ = (-(Fintype.card (Fin L) : ℝ) : ℂ) • Ψ →
            ∃ c : ℂ, Ψ = c • Φ

end LatticeSystem.Quantum
