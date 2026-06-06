import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSwapReachableBasics

/-!
# Tasaki 11.5: same value-counts ⟹ adjacent-swap reachable (Prop 11.24 PR-C2 combinatorics b)

The combinatorial heart of the Perron–Frobenius connectivity: two `Fin 3`-configurations on the
cyclic chain with equal value-counts are connected by a chain of adjacent value-swaps
(`adjacentSwapReachable_of_same_counts`).  The proof is a **selection sort**:

* `bubble_reachable` — move the value at a position `q` leftward to a target `p ≤ q` via a chain of
  nearest-neighbour swaps (`AdjacentSwapReachable`), leaving the prefix `[0, p)` untouched;
* `reach_of_agree_aux` — induction on the number of not-yet-fixed positions: at the leftmost
  disagreement `p`, the needed value `s' p` sits to the right (`exists_needed_value_right_of_…`);
  it into place, which fixes `[0, p]` and preserves the counts, then recurse.

Combined with the bridge `tjReachable_of_adjacentSwapReachable` (previous PR), this gives full
`TJStep`-reachability within a sector — the input to the irreducibility step.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **Consecutive sites are adjacent on the cycle.**  `a.val + 1 = b.val` (`0 < N`) gives
`(cycleGraph (N + 1)).Adj a b` (a non-wrap nearest-neighbour edge). -/
theorem adj_of_val_succ (hpos : 0 < N) (a b : Fin (N + 1)) (h : a.val + 1 = b.val) :
    (cycleGraph (N + 1)).Adj a b := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [cycleGraph_adj_iff]
  refine Or.inl (Fin.ext ?_)
  have hne : a ≠ Fin.last (M + 1) := by
    intro hl; rw [hl, Fin.val_last] at h; omega
  rw [Fin.val_add_one, if_neg hne]; exact h

/-- **The bubble step.**  Moving the value at position `q = p + g` leftward to `p` by `g`
nearest-neighbour swaps yields a reachable config equal to `s q` at `p` and unchanged on the prefix
`[0, p)`. -/
theorem bubble_reachable (hpos : 0 < N) (p : Fin (N + 1)) :
    ∀ (g : ℕ) (s : Fin (N + 1) → Fin 3) (q : Fin (N + 1)), q.val = p.val + g →
      ∃ s'' : Fin (N + 1) → Fin 3, AdjacentSwapReachable N s s'' ∧ s'' p = s q ∧
        (∀ k : Fin (N + 1), k.val < p.val → s'' k = s k)
  | 0, s, q, hq =>
      ⟨s, Relation.ReflTransGen.refl, by rw [show q = p from Fin.ext (by omega)], fun _ _ => rfl⟩
  | g + 1, s, q, hq => by
    have hqpos : 0 < q.val := by omega
    set q' : Fin (N + 1) := ⟨q.val - 1, by omega⟩ with hq'
    have hadj : (cycleGraph (N + 1)).Adj q' q :=
      adj_of_val_succ hpos q' q (by simp only [hq']; omega)
    have hq'val : q'.val = p.val + g := by simp only [hq']; omega
    obtain ⟨s'', hreach, hval, hpre⟩ :=
      bubble_reachable hpos p g (fun k => s (Equiv.swap q' q k)) q' hq'val
    refine ⟨s'', (adjacentSwapReachable_swap s q' q hadj).trans hreach, ?_, ?_⟩
    · rw [hval, Equiv.swap_apply_left]
    · intro k hk
      rw [hpre k hk, Equiv.swap_apply_of_ne_of_ne]
      · intro h; rw [h] at hk; simp only [hq'] at hk; omega
      · intro h; rw [h] at hk; omega

/-- **Selection-sort reachability.**  If `s` and `s'` agree on the first `N + 1 - m` positions and
have equal value-counts, then `s` is adjacent-swap reachable to `s'`.  Induction on `m`: at the
leftmost disagreement, bubble the needed value into place and recurse. -/
theorem reach_of_agree_aux (hpos : 0 < N) (s' : Fin (N + 1) → Fin 3) :
    ∀ (m : ℕ) (s : Fin (N + 1) → Fin 3),
      (∀ k : Fin (N + 1), k.val < N + 1 - m → s k = s' k) →
      (∀ v, (Finset.univ.filter (fun k => s k = v)).card
        = (Finset.univ.filter (fun k => s' k = v)).card) →
      AdjacentSwapReachable N s s'
  | 0, s, hagree, _ => by
    rw [show s = s' from funext fun k => hagree k (by omega)]
    exact Relation.ReflTransGen.refl
  | m + 1, s, hagree, hcount => by
    set p : Fin (N + 1) := ⟨N - m, by omega⟩ with hp
    have hpre : ∀ k : Fin (N + 1), k.val < p.val → s k = s' k := by
      intro k hk; exact hagree k (by simp only [hp] at hk ⊢; omega)
    by_cases hpeq : s p = s' p
    · -- `p` already agrees: extend the agreed prefix and recurse with `m`.
      refine reach_of_agree_aux hpos s' m s (fun k hk => ?_) hcount
      have hle : k.val ≤ p.val := by simp only [hp]; omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hpre k hlt
      · rw [show k = p from Fin.ext heq]; exact hpeq
    · -- `p` disagrees: bubble the needed value `s' p` from the right into `p`.
      obtain ⟨q, hpq, hsq⟩ :=
        exists_needed_value_right_of_same_counts s s' hcount p hpre hpeq
      obtain ⟨s'', hreach, hval, hbpre⟩ :=
        bubble_reachable hpos p (q.val - p.val) s q (by omega)
      have hcount'' : ∀ v, (Finset.univ.filter (fun k => s'' k = v)).card
          = (Finset.univ.filter (fun k => s' k = v)).card := fun v => by
        rw [adjacentSwapReachable_count s s'' hreach v]; exact hcount v
      refine hreach.trans (reach_of_agree_aux hpos s' m s'' (fun k hk => ?_) hcount'')
      have hle : k.val ≤ p.val := by simp only [hp]; omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · rw [hbpre k hlt]; exact hpre k hlt
      · rw [show k = p from Fin.ext heq, hval, hsq]

/-- **Same value-counts ⟹ adjacent-swap reachable.**  Any two `Fin 3`-configurations on the cyclic
chain with equal value-counts are connected by adjacent value-swaps. -/
theorem adjacentSwapReachable_of_same_counts (hpos : 0 < N) (s s' : Fin (N + 1) → Fin 3)
    (hcount : ∀ v, (Finset.univ.filter (fun k => s k = v)).card
        = (Finset.univ.filter (fun k => s' k = v)).card) :
    AdjacentSwapReachable N s s' :=
  reach_of_agree_aux hpos s' (N + 1) s (fun k hk => absurd hk (by omega)) hcount

end LatticeSystem.Fermion
