import LatticeSystem.Fermion.JordanWigner.Hubbard.TJStepRelation
import Mathlib.Logic.Relation

/-!
# Tasaki 11.5: adjacent-value swaps are connectivity steps (Prop 11.24 PR-C2 bridge)

Toward the sector connectivity (`TJStep`-reachability of any two same-sector states), this file
introduces the model-agnostic **adjacent-swap step** — exchanging the values at an adjacent pair of
*differing* sites — and shows every such swap is a `TJStep`:

* if one of the two sites is empty, the swap moves the electron into it — a **hop**
  (`tJSiteHop`);
* otherwise both carry electrons of opposite spin (`{↑, ↓}`), and the swap is an **exchange**
  (`tJSpinSwap`).

Both moves are precomposition with the transposition `Equiv.swap a b`, which is exactly what an
adjacent-value swap is.  Hence `Relation.ReflTransGen (AdjacentSwapStep N)` lifts to
`Relation.ReflTransGen (TJStep N)` via `tjReachable_of_adjacentSwapReachable`.  The combinatorial
part — that two states with equal value-counts are adjacent-swap reachable — is the next PR; this is
the bridge from that purely combinatorial reachability to the physical step relation.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-- A `Fin 3` value is `0`, `1`, or `2`. -/
private theorem fin3_cases (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp

/-- **An adjacent-value swap step.**  `s'` is obtained from `s` by exchanging the values at an
adjacent pair `a, b` of *distinct* values (precomposition with `Equiv.swap a b`). -/
def AdjacentSwapStep (N : ℕ) (s s' : Fin (N + 1) → Fin 3) : Prop :=
  ∃ a b : Fin (N + 1), (cycleGraph (N + 1)).Adj a b ∧ s a ≠ s b ∧
    s' = fun k => s (Equiv.swap a b k)

/-- **Every adjacent-value swap is a connectivity step.**  Swapping an empty site with an occupied
neighbour is a hop; swapping two opposite-spin neighbours is an exchange. -/
theorem adjacentSwapStep_to_TJStep (s s' : Fin (N + 1) → Fin 3) (h : AdjacentSwapStep N s s') :
    TJStep N s s' := by
  obtain ⟨a, b, hAdj, hne, hs'⟩ := h
  have hswapcomm : s' = fun k => s (Equiv.swap b a k) := by
    rw [hs']; funext k; rw [Equiv.swap_comm]
  rcases fin3_cases (s a) with ha | ha | ha
  · -- s a = ∅: hop b → a
    refine Or.inl ⟨b, a, hAdj.symm, fun hb => hne (ha.trans hb.symm), ha, ?_⟩
    rw [hswapcomm, tJSiteHop_eq_comp_swap s b a ha]
  · rcases fin3_cases (s b) with hb | hb | hb
    · -- s b = ∅: hop a → b
      refine Or.inl ⟨a, b, hAdj, by rw [ha]; decide, hb, ?_⟩
      rw [hs', tJSiteHop_eq_comp_swap s a b hb]
    · exact absurd (ha.trans hb.symm) hne
    · -- s a = ↑, s b = ↓: exchange b, a
      refine Or.inr ⟨b, a, hAdj.symm, hb, ha, ?_⟩
      rw [hswapcomm, tJSpinSwap_eq_comp_swap s b a]
  · rcases fin3_cases (s b) with hb | hb | hb
    · -- s b = ∅: hop a → b
      refine Or.inl ⟨a, b, hAdj, by rw [ha]; decide, hb, ?_⟩
      rw [hs', tJSiteHop_eq_comp_swap s a b hb]
    · -- s a = ↓, s b = ↑: exchange a, b
      refine Or.inr ⟨a, b, hAdj, ha, hb, ?_⟩
      rw [hs', tJSpinSwap_eq_comp_swap s a b]
    · exact absurd (ha.trans hb.symm) hne

/-- **Adjacent-swap reachability** is the reflexive–transitive closure of `AdjacentSwapStep`. -/
def AdjacentSwapReachable (N : ℕ) (s s' : Fin (N + 1) → Fin 3) : Prop :=
  Relation.ReflTransGen (AdjacentSwapStep N) s s'

/-- **Adjacent-swap reachability lifts to `TJStep` reachability.**  Since each adjacent swap is a
`TJStep`, a chain of adjacent swaps is a chain of connectivity steps. -/
theorem tjReachable_of_adjacentSwapReachable (s s' : Fin (N + 1) → Fin 3)
    (h : AdjacentSwapReachable N s s') :
    Relation.ReflTransGen (TJStep N) s s' :=
  h.mono (adjacentSwapStep_to_TJStep)

end LatticeSystem.Fermion
