import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis

/-!
# Tasaki 11.5: the site-hop move and sector preservation (Prop 11.24 PR3c-1)

The nearest-neighbour hop of the t-J model moves one electron between two sites without changing its
spin.  On a site-state `s : Fin (N+1) → Fin 3` this is `tJSiteHop s a b`: empty site `a`, occupy
site `b` with `a`'s spin.  For an allowed hop (`a` occupied, `b` empty) this preserves the up- and
down-electron counts, hence keeps the basis state in the same `N̂` and `S^z_tot` sector.  This
prepares the off-diagonal (hop) matrix elements of the sector Hamiltonian.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), 11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open scoped BigOperators

variable {N : ℕ}

/-- The hop move on site-states: the electron at `a` moves to `b` (empty `a`, set `b` to `a`'s
spin); other sites are unchanged. -/
def tJSiteHop (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) : Fin (N + 1) → Fin 3 :=
  fun i => if i = a then 0 else if i = b then s a else s i

/-- When `b` is empty, the hop move is precomposition with the transposition `swap a b`:
`tJSiteHop s a b = s ∘ Equiv.swap a b`. -/
theorem tJSiteHop_eq_comp_swap (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (hsb : s b = 0) :
    tJSiteHop s a b = fun i => s (Equiv.swap a b i) := by
  funext i
  rw [tJSiteHop]
  by_cases hia : i = a
  · subst hia; rw [if_pos rfl, Equiv.swap_apply_left, hsb]
  · rw [if_neg hia]
    by_cases hib : i = b
    · subst hib; rw [if_pos rfl, Equiv.swap_apply_right]
    · rw [if_neg hib, Equiv.swap_apply_of_ne_of_ne hia hib]

/-- An allowed hop (`b` empty) preserves the count of sites in **any** state `v`: the move is a
transposition, which is a bijection of the sites. -/
theorem tJSiteHop_count (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (hsb : s b = 0) (v : Fin 3) :
    (Finset.univ.filter (fun i => tJSiteHop s a b i = v)).card
      = (Finset.univ.filter (fun i => s i = v)).card := by
  rw [tJSiteHop_eq_comp_swap s a b hsb]
  refine Finset.card_bij' (fun i _ => Equiv.swap a b i) (fun j _ => Equiv.swap a b j) ?_ ?_ ?_ ?_
  · intro i hi; simpa using hi
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [Equiv.swap_apply_self]; exact hj
  · intro i _; exact Equiv.swap_apply_self a b i
  · intro j _; exact Equiv.swap_apply_self a b j

/-- An allowed hop preserves the number of ↑ electrons. -/
theorem tJSiteHop_up_count (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (hsb : s b = 0) :
    (Finset.univ.filter (fun i => tJSiteHop s a b i = 1)).card
      = (Finset.univ.filter (fun i => s i = 1)).card :=
  tJSiteHop_count s a b hsb 1

/-- An allowed hop preserves the number of ↓ electrons. -/
theorem tJSiteHop_down_count (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (hsb : s b = 0) :
    (Finset.univ.filter (fun i => tJSiteHop s a b i = 2)).card
      = (Finset.univ.filter (fun i => s i = 2)).card :=
  tJSiteHop_count s a b hsb 2

end LatticeSystem.Fermion
