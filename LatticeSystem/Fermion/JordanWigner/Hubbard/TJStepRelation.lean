import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorExchange

/-!
# Tasaki 11.5: the elementary connectivity step on t-J sector states (Prop 11.24 PR-C1)

Toward the Perron–Frobenius irreducibility of the t-J sector matrix (Prop 11.24), this file
introduces the elementary move `TJStep` between site-states on the cyclic chain, and shows it
preserves the spin counts (hence the `N̂ = Ne`, `Ŝ³ = ½` sector).  A step is either

* a **hop**: an electron moves from an occupied site `a` to an adjacent empty site `b`
  (`s' = tJSiteHop s a b`), or
* an **exchange**: an antiparallel adjacent pair `s i = ↓`, `s j = ↑` swaps spins
  (`s' = tJSpinSwap s i j`).

Both moves are precomposition with the transposition `Equiv.swap`, so they are bijections of the
site set and preserve the count of sites in every spin state — in particular `#↑` and `#↓`, so the
reachability closure of `TJStep` stays inside one sector.  This is the step relation whose positive
matrix entries (next PRs) feed `matrix_pow_succ_pos_of_path` and
`Matrix.isIrreducible_iff_exists_pow_pos`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **The spin-swap move is precomposition with the transposition `swap i j`.**  Unlike the hop, no
emptiness hypothesis is needed: `tJSpinSwap s i j = s ∘ Equiv.swap i j` always. -/
theorem tJSpinSwap_eq_comp_swap (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) :
    tJSpinSwap s i j = fun k => s (Equiv.swap i j k) := by
  funext k
  rw [tJSpinSwap]
  by_cases hki : k = i
  · subst hki; rw [if_pos rfl, Equiv.swap_apply_left]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst hkj; rw [if_pos rfl, Equiv.swap_apply_right]
    · rw [if_neg hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- **The spin-swap move preserves the count of sites in any state `v`** (it is a transposition,
hence a bijection of the sites). -/
theorem tJSpinSwap_count (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) (v : Fin 3) :
    (Finset.univ.filter (fun k => tJSpinSwap s i j k = v)).card
      = (Finset.univ.filter (fun k => s k = v)).card := by
  rw [tJSpinSwap_eq_comp_swap s i j]
  refine Finset.card_bij' (fun k _ => Equiv.swap i j k) (fun k _ => Equiv.swap i j k) ?_ ?_ ?_ ?_
  · intro k hk; simpa using hk
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [Equiv.swap_apply_self]; exact hk
  · intro k _; exact Equiv.swap_apply_self i j k
  · intro k _; exact Equiv.swap_apply_self i j k

/-- **The elementary connectivity step on sector site-states.**  `s'` is obtained from `s` by one of
the two off-diagonal moves of the t-J Hamiltonian on the cyclic chain: a nearest-neighbour/wrap hop
of an electron into an adjacent empty site, or an adjacent antiparallel spin exchange. -/
def TJStep (N : ℕ) (s s' : Fin (N + 1) → Fin 3) : Prop :=
  (∃ a b : Fin (N + 1), (cycleGraph (N + 1)).Adj a b ∧ s a ≠ 0 ∧ s b = 0 ∧
      s' = tJSiteHop s a b) ∨
    (∃ i j : Fin (N + 1), (cycleGraph (N + 1)).Adj i j ∧ s i = 2 ∧ s j = 1 ∧
      s' = tJSpinSwap s i j)

/-- **A step preserves the ↑-electron count.** -/
theorem tJStep_up_count (s s' : Fin (N + 1) → Fin 3) (h : TJStep N s s') :
    (Finset.univ.filter (fun k => s' k = 1)).card
      = (Finset.univ.filter (fun k => s k = 1)).card := by
  rcases h with ⟨a, b, _, _, hb, rfl⟩ | ⟨i, j, _, _, _, rfl⟩
  · exact tJSiteHop_up_count s a b hb
  · exact tJSpinSwap_count s i j 1

/-- **A step preserves the ↓-electron count.** -/
theorem tJStep_down_count (s s' : Fin (N + 1) → Fin 3) (h : TJStep N s s') :
    (Finset.univ.filter (fun k => s' k = 2)).card
      = (Finset.univ.filter (fun k => s k = 2)).card := by
  rcases h with ⟨a, b, _, _, hb, rfl⟩ | ⟨i, j, _, _, _, rfl⟩
  · exact tJSiteHop_down_count s a b hb
  · exact tJSpinSwap_count s i j 2

/-- **A step keeps the `N̂ = Ne`, `Ŝ³ = ½` sector conditions.**  Since both `#↑` and `#↓` are
preserved, the sector predicate (`#↑ = #↓ + 1 ∧ #↑ + #↓ = Ne`) transfers from `s` to `s'`. -/
theorem tJStep_preserves_sector (Ne : ℕ) (s s' : Fin (N + 1) → Fin 3) (h : TJStep N s s')
    (hs : (Finset.univ.filter (fun k => s k = 1)).card
          = (Finset.univ.filter (fun k => s k = 2)).card + 1 ∧
        (Finset.univ.filter (fun k => s k = 1)).card
          + (Finset.univ.filter (fun k => s k = 2)).card = Ne) :
    (Finset.univ.filter (fun k => s' k = 1)).card
        = (Finset.univ.filter (fun k => s' k = 2)).card + 1 ∧
      (Finset.univ.filter (fun k => s' k = 1)).card
        + (Finset.univ.filter (fun k => s' k = 2)).card = Ne := by
  rw [tJStep_up_count s s' h, tJStep_down_count s s' h]
  exact hs

end LatticeSystem.Fermion
