import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAdjacentSwap

/-!
# Tasaki 11.5: adjacent-swap reachability basics (Prop 11.24 PR-C2 combinatorics a)

Foundational lemmas for the combinatorial reachability `same value-counts ⟹ AdjacentSwapReachable`
(the next PR's selection-sort).  This file collects the reusable pieces:

* `adjacentSwapReachable_swap` — for an adjacent pair `a, b`, the value-swapped config
  `s ∘ Equiv.swap a b` is reachable (a single step if the values differ, `refl` if equal);
* `adjacentSwapStep_count` / `adjacentSwapReachable_count` — a step (hence the whole closure)
  preserves the count of sites in every value (swaps are site bijections);
* `exists_needed_value_right_of_same_counts` — if `s, s'` have equal value-counts, agree on a prefix
  `[0, p)`, and disagree at `p`, then the value `s' p` occurs in `s` at some position right of `p`
  (the target the next PR bubbles into place).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **Precomposition with a transposition preserves value-counts** (it is a site bijection). -/
theorem comp_swap_count (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (v : Fin 3) :
    (Finset.univ.filter (fun k => s (Equiv.swap a b k) = v)).card
      = (Finset.univ.filter (fun k => s k = v)).card := by
  refine Finset.card_bij' (fun k _ => Equiv.swap a b k) (fun k _ => Equiv.swap a b k) ?_ ?_ ?_ ?_
  · intro k hk; simpa using hk
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [Equiv.swap_apply_self]; exact hk
  · intro k _; exact Equiv.swap_apply_self a b k
  · intro k _; exact Equiv.swap_apply_self a b k

/-- **An adjacent-swap step preserves value-counts.** -/
theorem adjacentSwapStep_count (s s' : Fin (N + 1) → Fin 3) (h : AdjacentSwapStep N s s')
    (v : Fin 3) :
    (Finset.univ.filter (fun k => s' k = v)).card
      = (Finset.univ.filter (fun k => s k = v)).card := by
  obtain ⟨a, b, _, _, hs'⟩ := h
  rw [hs']; exact comp_swap_count s a b v

/-- **Adjacent-swap reachability preserves value-counts.** -/
theorem adjacentSwapReachable_count (s s' : Fin (N + 1) → Fin 3)
    (h : AdjacentSwapReachable N s s') (v : Fin 3) :
    (Finset.univ.filter (fun k => s' k = v)).card
      = (Finset.univ.filter (fun k => s k = v)).card := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [adjacentSwapStep_count _ _ hstep v, ih]

/-- **The value-swapped config is adjacent-swap reachable.**  For an adjacent pair `a, b`, swapping
the values is a single step when they differ and is the identity (`refl`) when they coincide. -/
theorem adjacentSwapReachable_swap (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hAdj : (cycleGraph (N + 1)).Adj a b) :
    AdjacentSwapReachable N s (fun k => s (Equiv.swap a b k)) := by
  by_cases h : s a = s b
  · have hid : (fun k => s (Equiv.swap a b k)) = s := by
      funext k
      rcases eq_or_ne k a with rfl | hka
      · rw [Equiv.swap_apply_left, h]
      · rcases eq_or_ne k b with rfl | hkb
        · rw [Equiv.swap_apply_right, ← h]
        · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
    rw [hid]; exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨a, b, hAdj, h, rfl⟩

/-- **The needed value lies to the right.**  If `s` and `s'` have equal value-counts, agree on the
prefix `[0, p)`, and disagree at `p`, then the value `s' p` occurs in `s` at some site strictly to
the right of `p`. -/
theorem exists_needed_value_right_of_same_counts (s s' : Fin (N + 1) → Fin 3)
    (hcount : ∀ v, (Finset.univ.filter (fun k => s k = v)).card
        = (Finset.univ.filter (fun k => s' k = v)).card)
    (p : Fin (N + 1)) (hpre : ∀ k : Fin (N + 1), k.val < p.val → s k = s' k)
    (hne : s p ≠ s' p) :
    ∃ q : Fin (N + 1), p.val < q.val ∧ s q = s' p := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- `hcon : ∀ q, p.val < q.val → s q ≠ s' p`.
  set v := s' p with hv
  -- `{k | s k = v} ⊆ {k | k.val < p.val ∧ s' k = v}`.
  have hsub : Finset.univ.filter (fun k => s k = v)
      ⊆ Finset.univ.filter (fun k => k.val < p.val ∧ s' k = v) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases lt_trichotomy k.val p.val with hlt | heq | hgt
    · exact ⟨hlt, (hpre k hlt) ▸ hk⟩
    · exact absurd (((Fin.ext heq) ▸ hk : s p = v)) (hv ▸ hne)
    · exact absurd hk (hcon k hgt)
  -- `{k | k.val < p.val ∧ s' k = v} ⊂ {k | s' k = v}` (it misses `p`, which has `s' p = v`).
  have hsub2 : Finset.univ.filter (fun k => k.val < p.val ∧ s' k = v)
      ⊆ Finset.univ.filter (fun k => s' k = v) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.2
  have hp_mem : p ∈ Finset.univ.filter (fun k => s' k = v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hv.symm
  have hp_not : p ∉ Finset.univ.filter (fun k => k.val < p.val ∧ s' k = v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro hlt; exact absurd hlt (lt_irrefl _)
  have hlt_card : (Finset.univ.filter (fun k => k.val < p.val ∧ s' k = v)).card
      < (Finset.univ.filter (fun k => s' k = v)).card :=
    Finset.card_lt_card ⟨hsub2, fun h => hp_not (h hp_mem)⟩
  have : (Finset.univ.filter (fun k => s k = v)).card
      < (Finset.univ.filter (fun k => s' k = v)).card :=
    lt_of_le_of_lt (Finset.card_le_card hsub) hlt_card
  exact absurd (hcount v) (ne_of_lt this)

end LatticeSystem.Fermion
