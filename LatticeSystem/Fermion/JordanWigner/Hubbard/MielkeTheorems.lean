import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeHamiltonian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivityClassification
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Tasaki §11.3.2: Mielke's flat-band theorems (line graph, flat band, ferromagnetism)

Mielke's model is the Hubbard model on the *line graph* `(Λ,B)` of a base lattice
`(Λ̃,B̃)`.  The line graph is mathlib's `SimpleGraph.lineGraph` (its vertices are the
edges of the base graph; two are adjacent iff they share a base vertex), and a
concrete realisation on `Fin (M+1)` is recorded by a graph isomorphism
`SimpleGraph.Iso G (lineGraph Gbase)`.

This file holds the statement data (`mielkeFlatBandDim`, `mielkeSingleElectronOp`,
`mielkeGroundSubmodule`) and Tasaki's two §11.3.2 results:

* **Theorem 11.12 (flat band)**: the single-electron Schrödinger operator on the
  line graph has exactly `D(Λ̃,B̃)` zero-energy eigenstates.  *Tasaki defers the proof
  to §11.3.3*; it is **now proved** (no longer an axiom) in
  `Hubbard/MielkeIncidenceMatrix.lean` (which imports this file), via the §11.3.3
  incidence-matrix construction — see `mielke_theorem_11_12` there (Issue #4180).
* **Theorem 11.13 (Mielke's ferromagnetism)**: for a biconnected base lattice at
  half-filling `N = D`, the ground states are the maximal-spin `(2S_max+1)`-fold
  multiplet with `S_tot = S_max = N/2`.  *Tasaki states it without proof* ("We state
  it without a proof"), so it remains a **documented axiom**, matching the policy for
  Theorem 11.8 / Lemma 11.9 and the §11.3.1 classification axiom.

`D(Λ̃,B̃) = |B̃| − |Λ̃| + 1` if `(Λ̃,B̃)` is bipartite, else `|B̃| − |Λ̃|`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.2, Theorems 11.12–11.13 (and §11.3.3 for the 11.12 proof).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice

open Classical in
/-- **`D(Λ̃,B̃)`** (Tasaki §11.3.2): the number of flat-band single-electron states
of the line graph, `|B̃| − |Λ̃| + 1` for a bipartite base lattice and `|B̃| − |Λ̃|`
otherwise. -/
noncomputable def mielkeFlatBandDim {Nbase : ℕ} (Gbase : SimpleGraph (Fin (Nbase + 1)))
    [DecidableRel Gbase.Adj] : ℕ :=
  Gbase.edgeFinset.card - (Nbase + 1) + (if Gbase.Colorable 2 then 1 else 0)

/-- The Mielke single-electron Schrödinger operator on a graph `G` over an
arbitrary finite vertex type (eq. (11.3.32)): `T = t·(adjacency of G) + 2t·I`,
whose `ε = 0` eigenspace is the flat band.  When `G` is the line graph of a base
lattice this is the operator whose kernel Theorem 11.12 counts; the §11.3.3 proof
realises it as `SᴴS` for the base lattice's incidence matrix `S`, which lives over
`G.edgeSet` rather than `Fin (M+1)`, so the operator is stated at this generality. -/
noncomputable def mielkeSingleElectronOpOn {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (t : ℝ) : Matrix Λ Λ ℂ :=
  Matrix.of (couplingOf G (t : ℂ)) + (2 * t : ℂ) • (1 : Matrix Λ Λ ℂ)

/-- The Mielke single-electron Schrödinger operator on the line graph `Λ`
(eq. (11.3.32)), concretely realised on `Fin (M+1)`: `T = t·(adjacency of Λ) + 2t·I`,
whose `ε = 0` eigenspace is the flat band.  A thin wrapper around
`mielkeSingleElectronOpOn` specialised to `Fin (M+1)`. -/
noncomputable def mielkeSingleElectronOp {M : ℕ} (G : SimpleGraph (Fin (M + 1)))
    [DecidableRel G.Adj] (t : ℝ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ :=
  mielkeSingleElectronOpOn G t

-- **Tasaki Theorem 11.12 (flat band in a general line graph)** is now *proved* (no
-- longer an axiom) in `Hubbard/MielkeIncidenceMatrix.lean` as `mielke_theorem_11_12`,
-- discharged via the §11.3.3 incidence-matrix construction (Issue #4180).  It lives in
-- that downstream file because the proof needs the incidence/rank/zero-mode results,
-- and that file imports this one.

/-- The half-filled Mielke ground subspace: the zero-energy states (`ker Ĥ`, the
`2t·N̂` shift placing the ground energy at `0`) in the `N`-electron sector. -/
noncomputable def mielkeGroundSubmodule {M : ℕ} (G : SimpleGraph (Fin (M + 1)))
    [DecidableRel G.Adj] (t U : ℝ) (N : ℕ) :
    Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  LinearMap.ker (mielkeHamiltonian M G t U).mulVecLin ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * M + 1)).mulVecLin (N : ℂ)

/-- **Maximal-spin (`S = D/2`) multiplet ground subspace.**  A submodule `sub` of the
`(N+1)`-site spinful Fock space is the *saturated-ferromagnetic* ground subspace at the
maximal spin `S_max = D/2` when it is the `(D+1) = (2 S_max + 1)`-fold multiplet
(`finrank = D + 1`) and every vector is an `(Ŝ_tot)²` eigenvector at the maximal eigenvalue
`S_max (S_max + 1)`.  This is the common conclusion shared by Mielke's Theorem 11.13
(`mielke_theorem_11_13`), the general flat-band Theorem 11.15 (`generalFlatBandFerromagnetic`),
and §11.5's ferromagnetic t-J results, so it is factored out as one reusable predicate. -/
def IsMaximalSpinMultipletSubmodule (N : ℕ)
    (sub : Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ)) (D : ℕ) : Prop :=
  Module.finrank ℂ sub = D + 1 ∧
    ∀ v ∈ sub, (fermionTotalSpinSquared N).mulVec v
      = (((D : ℂ) / 2) * ((D : ℂ) / 2 + 1)) • v

/-- **Tasaki Theorem 11.13 (Mielke's flat-band ferromagnetism), AXIOM.**  For a
biconnected base lattice `(Λ̃,B̃)`, the Hubbard model on its line graph at
half-filling `N = D(Λ̃,B̃)` (with `t, U > 0`) has ground states that all carry
total spin `S_tot = S_max = N/2`, unique apart from the `2S_max + 1 = N + 1`-fold
multiplet degeneracy.  Tasaki states this without proof, so it is a documented
axiom (matching the Theorem 11.8 / §11.3.1 classification policy): the ground
subspace has `finrank = N + 1` and every ground state is a `(Ŝ_tot)²` eigenvector
at `S_max(S_max + 1)`. -/
axiom mielke_theorem_11_13 {Nbase M : ℕ} (Gbase : SimpleGraph (Fin (Nbase + 1)))
    [DecidableRel Gbase.Adj] (G : SimpleGraph (Fin (M + 1))) [DecidableRel G.Adj]
    (t U : ℝ) (ht : 0 < t) (hU : 0 < U)
    (hLG : Nonempty (SimpleGraph.Iso G Gbase.lineGraph)) (hbc : IsBiconnected Gbase) :
    IsMaximalSpinMultipletSubmodule M
      (mielkeGroundSubmodule G t U (mielkeFlatBandDim Gbase)) (mielkeFlatBandDim Gbase)

end LatticeSystem.Fermion
