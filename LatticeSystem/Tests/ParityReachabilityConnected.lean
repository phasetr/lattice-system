import LatticeSystem.Quantum.SpinS.ParityReachConnectedTotal
import LatticeSystem.Quantum.SpinS.ParityReachableMagSum
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Signature pins: connected-graph parity-reachability totality (Red fixture)

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), PR-1 of the connectivity/reachability
arc. Pins the exact signatures of the three connected-graph totality theorems that
`LatticeSystem/Quantum/SpinS/ParityReachConnectedTotal.lean` must provide, before they exist
(TDD Red).

Each pin mirrors the complete-bipartite originals
(`parityReachableS_total` in `BipartiteCompleteGraphStructural.lean`,
`ionParityReachableS_total` in `ParityReachableNoParityBondTotal.lean`,
`bondParityReachableS_total` in `ParityReachableNoSingleIonTotal.lean`) with `hA_ne`/`hB_ne`
replaced by `hG : G.Connected` (plus `hV : Nontrivial V` for the bond-only relation), and with
**no** bipartiteness or balanced-sublattice hypothesis: reachability along the three relations
is purely graph-theoretic (Footnote 28, p. 33 connectedness only), and bipartiteness/balance are
not needed until the sign-gauge and sector arguments of PR-2/PR-3.
-/

namespace LatticeSystem.Tests.ParityReachabilityConnected

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Signature pin.** The full parity-block relation is total on same-parity configurations of a
connected graph, with no bipartiteness or balance hypothesis and `1 ≤ N`. -/
example {G : SimpleGraph V} (hG : G.Connected) (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)} (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    ParityReachableS G σ σ' :=
  parityReachableS_total_of_connected hG hN h_par

/-- **Signature pin.** The ion-only (no bond-parity-hop) relation is total on same-parity
configurations of a connected graph, with no bipartiteness or balance hypothesis and `2 ≤ N`
(not `1 ≤ N`: a single-ion `±2` move needs room `1 < N`). -/
example {G : SimpleGraph V} (hG : G.Connected) (hN : 2 ≤ N)
    {σ σ' : V → Fin (N + 1)} (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    IonParityReachableS G σ σ' :=
  ionParityReachableS_total_of_connected hG hN h_par

/-- **Signature pin.** The bond-only (no single-ion) relation is total on same-parity
configurations of a connected graph, with no bipartiteness or balance hypothesis, `1 ≤ N`, and an
**explicit** `Nontrivial V` hypothesis. `Nontrivial V` is genuinely necessary here and not on the
other two relations: on the one-vertex connected graph with `N = 2`, `σ = (2)` and `σ' = (0)` are
same-parity (both even) and reachable by a single-ion `±2` move, but there is no edge at all, so
the bond-only relation (whose only two step kinds are transverse and bond-parity hops, both
requiring an edge) cannot reach `σ'` from `σ`. Dropping `hV` for symmetry with the other two pins
would make this statement false. -/
example {G : SimpleGraph V} (hV : Nontrivial V) (hG : G.Connected) (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)} (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    BondParityReachableS G σ σ' :=
  bondParityReachableS_total_of_connected hV hG hN h_par

/-- **Discriminating witness (four-vertex path, not the four-cycle).** On `V = Fin 4`,
`A = {0, 2}`, the path `pathGraph 4` (edges `{0,1},{1,2},{2,3}`) is connected (Footnote 28, p. 33)
and satisfies every hypothesis of the new connected capstones above. The old complete-bipartite
theorems say nothing about it, and not because their hypotheses fail: `hA_ne` (`a = 0`) and
`hB_ne` (`b = 1`) both hold for this marking, and neither mentions adjacency. What fails is the
*conclusion*, which is about the fixed graph `bipartiteCompleteGraphOf A` — and for this marking
that graph is not `pathGraph 4`, witnessed by the crossing pair `{0,3}`
(`(bipartiteCompleteGraphOf A).Adj 0 3` while `¬ (pathGraph 4).Adj 0 3`). The four-cycle
`cycleGraph 4` does **not** discriminate: with this same marking its edge set is exactly the four
crossing pairs, so `cycleGraph 4 = bipartiteCompleteGraphOf A` as graphs and the old theorems
already cover it. -/
example :
    (SimpleGraph.pathGraph 4).Connected ∧
      (bipartiteCompleteGraphOf (fun x : Fin 4 => decide (x = 0 ∨ x = 2))).Adj 0 3 ∧
      ¬ (SimpleGraph.pathGraph 4).Adj (0 : Fin 4) 3 := by
  refine ⟨SimpleGraph.pathGraph_connected 3, ?_, ?_⟩
  · simp
  · simp [SimpleGraph.pathGraph_adj]

/-- **Regression: `h_par` is exactly the invariant it claims to be.** `ParityReachableS` already
preserves `magSumS`-parity (the converse direction of the hypothesis `h_par` above), so the new
capstone's hypothesis is not stronger than what the relation can actually deliver. -/
example {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)} (h : ParityReachableS G σ σ') :
    magSumS σ' % 2 = magSumS σ % 2 :=
  parityReachableS_magSumS_parity_eq h

end LatticeSystem.Tests.ParityReachabilityConnected
