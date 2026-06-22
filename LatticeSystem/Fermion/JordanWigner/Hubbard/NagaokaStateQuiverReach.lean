import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaStateQuiverReachCore

/-!
# Tasaki §11.2.2: the one-hole state quiver of `−M` and the proof of Lemma 11.9

The connectivity condition (Definition 11.6, `nagaokaConnectivity`) is irreducibility of the
sector-restricted `−M`, i.e. strong connectivity of the quiver whose edges are the *positive*
entries of `−M`.  This file builds Tasaki's "15-puzzle" hole-motion argument in full, proving the
capstone `nagaokaConnectivity_of_connectedByExchangeBonds` behind **Lemma 11.9**
(`nagaoka_lemma_11_9`, stated at its original path in
`NagaokaConnectivityClassification.lean`, formerly an axiom there).  The layers:

* **Edges** — `−M_{(y,τ),(x,σ)} > 0` iff the hole hops `x → y` along a present bond
  (`neg_tasakiEffReMatrix_pos_iff`, `holeHopHom`/`holeHopHom'`), giving the reachability relation
  `StateReach` with `refl`/`trans`/`symm`.
* **Loop trips** — circling a length-3 loop transposes the two passed spins
  (`StateReach.transposition`); a length-4 loop 3-cycles them, and the footnote-14 once/twice
  Boolean trip turns that into a transposition of either the diagonal or an adjacent pair
  (`landing_swap_quad`, `landing_swap_quad_adj`).
* **Controlled transport** — the hole travels to a loop, performs the in-place swap, and returns
  along the reversed walk restoring everything else (`holeWalkTransport`,
  `swap_via_landing_walk`); the route avoiding the swapped pair exists by E2
  (`exists_avoiding_walk_of_induce_connected`).
* **Exchange-bond bridge** — every exchange bond (length-3 or length-4 loop + E2) yields a
  `ReachSwap`, a spin swap available from *every* hole position
  (`reachSwap_of_isExchangeBond`).
* **Generation** — swaps propagate along exchange-bond walks by the conjugation
  `(y z) = (y w)(w z)(y w)` with explicit avoid-set bookkeeping (`ReachSwapOff.of_walk`,
  Tasaki footnote 13); parking the hole at a *farthest* vertex of the exchange-bond graph makes
  every pair swappable (`exists_vertex_walks_avoid`, the parking lemma).
* **Assembly** — same-magnetization configurations at the parked hole are connected by the
  mismatch-reduction induction (`StateReach.of_swaps_of_holeSpinMag_eq`); hole mobility aligns
  arbitrary states (`StateReach.exists_hole_at`), and an out-and-back hop supplies the
  positive-length diagonal (`exists_pos_selfPath`).  The sector quiver half
  (`nagaokaConnectivity_of_reach`) converts reachability into irreducibility, giving the
  zero-diagonal capstone; the diagonal-zeroing transfer (`tasakiEffReMatrix_zeroDiag`,
  `nagaokaBondGraph_zeroDiag`) then yields `nagaoka_lemma_11_9` verbatim in
  `NagaokaConnectivityClassification.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Lemma 11.9, Figs. 11.8–11.9, footnotes 13–14, pp. 386–388.
-/

namespace LatticeSystem.Fermion

open Matrix

/-- **Swap reachable from every hole avoiding a finite set `S`.**  Generalises `ReachSwap`
(the case `S = ∅`) by tracking the set of *auxiliary* sites a composed swap must steer the hole
clear of.  When two exchange-bond swaps `{y, w}` and `{w, z}` are chained by the conjugation
`(y z) = (y w)(w z)(y w)` (`ReachSwapOff.comp_via`), the intermediate `w` joins the avoid-set, so a
swap propagated along an exchange-bond path is valid precisely for holes off the path's interior.
This is the bookkeeping device of the distance-induction generation argument (Tasaki fn. 13). -/
def ReachSwapOff (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) (S : Finset (Fin (N + 1)))
    (y z : Fin (N + 1)) : Prop :=
  ∀ (p : Fin (N + 1)) (hpy : p ≠ y) (hpz : p ≠ z), p ∉ S → ∀ σ : HoleSpin N p,
    StateReach N t ⟨p, σ⟩ ⟨p, swapHoleSpin N p y z hpy hpz σ⟩

/-- A full `ReachSwap` (valid for every hole `∉ {y, z}`) is in particular a `ReachSwapOff` for any
avoid-set `S`: ignoring the extra constraint `p ∉ S` only discards admissible holes. -/
theorem ReachSwap.toOff {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ} {S : Finset (Fin (N + 1))}
    {y z : Fin (N + 1)} (h : ReachSwap N t y z) : ReachSwapOff N t S y z :=
  fun p hpy hpz _ σ => h p hpy hpz σ

/-- `ReachSwapOff` is monotone in the avoid-set: enlarging `S` only removes admissible holes, so a
swap valid off `S` is a fortiori valid off any `S' ⊇ S`. -/
theorem ReachSwapOff.mono {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ}
    {S S' : Finset (Fin (N + 1))} {y z : Fin (N + 1)} (hSS : S ⊆ S')
    (h : ReachSwapOff N t S y z) : ReachSwapOff N t S' y z :=
  fun p hpy hpz hpS' σ => h p hpy hpz (fun hpS => hpS' (hSS hpS)) σ

/-- **Composition through an intermediate site, with avoid-set bookkeeping.**  The conjugation
`(y z) = (y w)(w z)(y w)`: if `{y, w}` is reachable off `S₁` and `{w, z}` is reachable off `S₂`,
then `{y, z}` is reachable off `insert w (S₁ ∪ S₂)` — the new avoid-set adds the intermediate `w`
(the hole must differ from it to perform the inner swaps) and the union of the two component
avoid-sets.  This is the avoid-set-tracking form of `ReachSwap.comp_via`. -/
theorem ReachSwapOff.comp_via {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ}
    {S₁ S₂ : Finset (Fin (N + 1))} {y w z : Fin (N + 1)}
    (hyw : ReachSwapOff N t S₁ y w) (hwz : ReachSwapOff N t S₂ w z)
    (hyw_ne : y ≠ w) (hwz_ne : w ≠ z) (hyz_ne : y ≠ z) :
    ReachSwapOff N t (insert w (S₁ ∪ S₂)) y z := by
  intro p hpy hpz hpS σ
  rw [Finset.mem_insert, not_or, Finset.mem_union, not_or] at hpS
  obtain ⟨hpw, hpS₁, hpS₂⟩ := hpS
  rw [swapHoleSpin_conj N p y w z hpy hpw hpz hyw_ne hwz_ne hyz_ne]
  exact (hyw p hpy hpw hpS₁ σ).trans
    ((hwz p hpw hpz hpS₂ _).trans (hyw p hpy hpw hpS₁ _))

/-- **Distance-induction generation: a swap propagates along a path of unit swaps.**  If every edge
`a — b` of a graph `H` already yields a full `ReachSwap N t a b`, then for any `H`-walk `x → y`
between distinct endpoints the swap `{x, y}` is reachable off the walk's support: the hole need only
avoid the (finitely many) vertices visited along the way.  Proved by induction on the walk, chaining
the unit swaps with `ReachSwapOff.comp_via`.  With `H = exchangeBondGraph (nagaokaBondGraph N t)`
this is Tasaki's "connected by exchange bonds ⟹ every transposition is generated" (footnote 13). -/
theorem ReachSwapOff.of_walk {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ}
    {H : SimpleGraph (Fin (N + 1))} (hedge : ∀ {a b}, H.Adj a b → ReachSwap N t a b)
    {x y : Fin (N + 1)} (W : H.Walk x y) (hxy : x ≠ y) :
    ReachSwapOff N t W.support.toFinset x y := by
  induction W with
  | nil => exact absurd rfl hxy
  | @cons x v y h W' ih =>
    by_cases hvy : v = y
    · subst hvy
      exact (hedge h).toOff
    · have key := ReachSwapOff.comp_via (S₁ := W'.support.toFinset) (S₂ := W'.support.toFinset)
        (hedge h).toOff (ih hvy) h.ne hvy hxy
      refine ReachSwapOff.mono ?_ key
      rw [Finset.union_self, SimpleGraph.Walk.support_cons, List.toFinset_cons,
        Finset.insert_subset_iff]
      exact ⟨Finset.mem_insert_of_mem (List.mem_toFinset.mpr W'.start_mem_support),
        Finset.subset_insert _ _⟩

/-- **An exchange-bond-graph edge gives a full `ReachSwap`.**  An edge `a — b` of the exchange-bond
graph is, by definition, an exchange bond `{a, b}` (or `{b, a}`); either way
`reachSwap_of_isExchangeBond` (plus `ReachSwap.symm` in the reversed case) exchanges the spins at
`a, b` from every hole `∉ {a, b}`.
This is the `hedge` hypothesis specialising `ReachSwapOff.of_walk` to the exchange-bond graph. -/
theorem reachSwap_of_exchangeBondAdj (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a b : Fin (N + 1)} (h : (exchangeBondGraph (nagaokaBondGraph N t)).Adj a b) :
    ReachSwap N t a b := by
  obtain ⟨hne, hor⟩ := h
  rcases hor with hab | hba
  · exact reachSwap_of_isExchangeBond N t htsym htdiag hpos hne hab
  · exact (reachSwap_of_isExchangeBond N t htsym htdiag hpos hne.symm hba).symm hne.symm

/-- **Distance-induction generation for the bond graph (Tasaki footnote 13).**  If two sites `x ≠ y`
are joined in the exchange-bond graph, the spin swap `{x, y}` is reachable off the (finite) support
of the connecting exchange-bond walk: from every hole avoiding that support, `(p, σ)` reaches
`(p, swap_{x,y} σ)`.  This combines `reachSwap_of_exchangeBondAdj` (each exchange bond swaps its
endpoints) with `ReachSwapOff.of_walk` (conjugation along the walk).  Under
`ConnectedByExchangeBonds` the hypothesis holds for *every* pair `x ≠ y`, generating all
transpositions of the occupied sites. -/
theorem reachSwapOff_of_exchangeReachable (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {x y : Fin (N + 1)} (hxy : x ≠ y)
    (hreach : (exchangeBondGraph (nagaokaBondGraph N t)).Reachable x y) :
    ∃ S : Finset (Fin (N + 1)), ReachSwapOff N t S x y := by
  obtain ⟨W⟩ := hreach
  exact ⟨W.support.toFinset,
    ReachSwapOff.of_walk (fun h => reachSwap_of_exchangeBondAdj N t htsym htdiag hpos h) W hxy⟩

/-- **An exchange bond's endpoints are bond-connected.**  An exchange-bond edge `x — y` puts `x` and
`y` on a common loop of the bond graph, so they are joined by a walk *in the bond graph itself* (the
loop arc).  Hence every exchange-bond-graph edge lifts to bond-graph reachability. -/
theorem bondReachable_of_exchangeBondAdj (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    {x y : Fin (N + 1)} (h : (exchangeBondGraph (nagaokaBondGraph N t)).Adj x y) :
    (nagaokaBondGraph N t).Reachable x y := by
  obtain ⟨z', c, hx, hy⟩ :
      ∃ (z' : Fin (N + 1)) (c : (nagaokaBondGraph N t).Walk z' z'),
        x ∈ c.support ∧ y ∈ c.support := by
    obtain ⟨_, hor⟩ := h
    rcases hor with ⟨⟨z', c, _, _, hx, hy⟩, _⟩ | ⟨⟨z', c, _, _, hy, hx⟩, _⟩
    · exact ⟨z', c, hx, hy⟩
    · exact ⟨z', c, hx, hy⟩
  exact ((c.takeUntil x hx).reachable).symm.trans (c.takeUntil y hy).reachable

/-- **Bond-graph reachability from exchange-bond reachability.**  Composing
`bondReachable_of_exchangeBondAdj` along an exchange-bond walk: if `x, y` are joined in the
exchange-bond graph, they are joined in the bond graph. -/
theorem bondReachable_of_exchangeReachable (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    {x y : Fin (N + 1)} (h : (exchangeBondGraph (nagaokaBondGraph N t)).Reachable x y) :
    (nagaokaBondGraph N t).Reachable x y := by
  obtain ⟨W⟩ := h
  induction W with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h _ ih => exact (bondReachable_of_exchangeBondAdj N t h).trans ih

/-- **Hole mobility: connected by exchange bonds ⟹ the bond graph is connected.**  Every exchange
bond's endpoints are bond-connected (through its loop), so connectivity of the exchange-bond graph
transfers to the bond graph.  This supplies the hole-relocation ingredient (`exists_hole_at` needs
bond-graph reachability) for the final sector-connectivity assembly of Lemma 11.9. -/
theorem nagaokaBondGraph_connected_of_connectedByExchangeBonds (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (h : ConnectedByExchangeBonds (nagaokaBondGraph N t)) :
    (nagaokaBondGraph N t).Connected :=
  { preconnected := fun u v => bondReachable_of_exchangeReachable N t (h.preconnected u v)
    nonempty := h.nonempty }

end LatticeSystem.Fermion
