import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaMagnetizationSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaBondGraph
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaStateQuiverCore

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

/-- **The 15-puzzle exchange (Lemma 11.9, key step): an exchange bond gives a reachable spin swap
from any hole position.**  Suppose `a, y, z` form a triangle of bonds and the hole, starting at
position `p`, can travel to `a` along a walk `W` that avoids both `y` and `z` (this is what the
exchange-bond condition E2 — connectedness of `Λ ∖ {y, z}` — provides).  Then `(p, σ)` reaches
`(p, swap σ)`, where `swap` exchanges the spins at `y` and `z` and leaves everything else (including
the hole at `p`) unchanged.  The hole is routed to the triangle without disturbing `y, z`, the spins
at `y, z` are swapped by circling the triangle (`transposition_of_triangle`), and the reversed walk
restores all other spins (`holeWalkTransport_reverse` + `holeWalkTransport_val_congr`). -/
theorem StateReach.swap_via_landing_walk (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a y z p : Fin (N + 1)} (hay_ne : a ≠ y) (hza_ne : a ≠ z)
    (W : (nagaokaBondGraph N t).Walk p a) (hyW : y ∉ W.support) (hzW : z ∉ W.support)
    (σ : HoleSpin N p)
    (rmid : StateReach N t ⟨a, holeWalkTransport N W σ⟩
      ⟨a, swapHoleSpin N a y z hay_ne hza_ne (holeWalkTransport N W σ)⟩) :
    StateReach N t ⟨p, σ⟩
      ⟨p, swapHoleSpin N p y z
        (fun h => hyW (h ▸ W.start_mem_support)) (fun h => hzW (h ▸ W.start_mem_support)) σ⟩ := by
  -- supports of W and its reverse coincide
  have hyWr : y ∉ W.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]; simpa using hyW
  have hzWr : z ∉ W.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]; simpa using hzW
  set σa := holeWalkTransport N W σ with hσa
  set C := swapHoleSpin N a y z hay_ne hza_ne σa with hC
  -- the three legs: hole p→a, the landing swap at a, hole a→p
  have r1 : StateReach N t ⟨p, σ⟩ ⟨a, σa⟩ := StateReach.ofBondWalk N t htsym htdiag hpos W σ
  have r2 : StateReach N t ⟨a, σa⟩ ⟨a, C⟩ := rmid
  have r3 : StateReach N t ⟨a, C⟩ ⟨p, holeWalkTransport N W.reverse C⟩ :=
    StateReach.ofBondWalk N t htsym htdiag hpos W.reverse C
  -- σa agrees with σ at y and z (the walk avoids them)
  have hσay : σa.val y = σ.val y := holeWalkTransport_apply_of_notMem_support N W σ hyW
  have hσaz : σa.val z = σ.val z := holeWalkTransport_apply_of_notMem_support N W σ hzW
  -- the net transported configuration is exactly the (y z) swap of σ
  have hnet : holeWalkTransport N W.reverse C
      = swapHoleSpin N p y z (fun h => hyW (h ▸ W.start_mem_support))
          (fun h => hzW (h ▸ W.start_mem_support)) σ := by
    apply Subtype.ext
    funext s
    rw [swapHoleSpin_val_apply]
    by_cases hsy : s = y
    · subst hsy
      rw [holeWalkTransport_apply_of_notMem_support N W.reverse C hyWr, hC,
        swapHoleSpin_val_apply, if_pos rfl, hσaz, if_pos rfl]
    · by_cases hsz : s = z
      · subst hsz
        rw [holeWalkTransport_apply_of_notMem_support N W.reverse C hzWr, hC,
          swapHoleSpin_val_apply, if_neg hsy, if_pos rfl, hσay, if_neg hsy, if_pos rfl]
      · rw [if_neg hsy, if_neg hsz]
        by_cases hsW : s ∈ W.reverse.support
        · -- on-path: use congruence + round trip (C and σa agree on the path)
          have hagree : ∀ u ∈ W.reverse.support, C.val u = σa.val u := by
            intro u hu
            have huy : u ≠ y := fun h => hyWr (h ▸ hu)
            have huz : u ≠ z := fun h => hzWr (h ▸ hu)
            rw [hC, swapHoleSpin_val_apply, if_neg huy, if_neg huz]
          rw [← holeWalkTransport_val_congr N W.reverse σa C
            (fun u hu => (hagree u hu).symm) s hsW, hσa, holeWalkTransport_reverse N W σ]
        · -- off-path: both untouched, C agrees with σa, σa agrees with σ
          rw [holeWalkTransport_apply_of_notMem_support N W.reverse C hsW, hC,
            swapHoleSpin_val_apply, if_neg hsy, if_neg hsz,
            holeWalkTransport_apply_of_notMem_support N W σ
              (fun h => hsW (by rw [SimpleGraph.Walk.support_reverse]; simpa using h))]
  rw [← hnet]
  exact (r1.trans r2).trans r3

/-- **The 15-puzzle exchange (length-3 loop): an exchange via a triangle from any hole position.**
The triangle `{a, y, z}` instance of `swap_via_landing_walk`, where the landing swap is one trip
around the triangle (`transposition_of_triangle`). -/
theorem StateReach.swap_via_triangle_walk (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a y z p : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (hyz : (nagaokaBondGraph N t).Adj y z) (hza : (nagaokaBondGraph N t).Adj z a)
    (W : (nagaokaBondGraph N t).Walk p a) (hyW : y ∉ W.support) (hzW : z ∉ W.support)
    (σ : HoleSpin N p) :
    StateReach N t ⟨p, σ⟩
      ⟨p, swapHoleSpin N p y z
        (fun h => hyW (h ▸ W.start_mem_support)) (fun h => hzW (h ▸ W.start_mem_support)) σ⟩ :=
  StateReach.swap_via_landing_walk N t htsym htdiag hpos hay.ne hza.ne.symm W hyW hzW σ
    (StateReach.transposition_of_triangle N t htsym htdiag hpos hay hyz hza _)

/-- **Length-4 landing swap (Tasaki Fig. 11.9).**  On a 4-loop `a → y → w → z → a` with the hole at
the corner `a` and the exchanged pair `y, z` on the opposite diagonal (auxiliary site `w`), the
spins at `y` and `z` can be exchanged in place: one trip around the loop if `σ(w) = σ(z)`, two trips
if `σ(w) = σ(y)` (and a no-op if `σ(y) = σ(z)`).  Because spins are Boolean, one of these always
applies.  Combines `threeCyclePerm_of_quad` with the footnote-14 identities. -/
theorem StateReach.landing_swap_quad (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a y w z : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (hyw : (nagaokaBondGraph N t).Adj y w) (hwz : (nagaokaBondGraph N t).Adj w z)
    (hza : (nagaokaBondGraph N t).Adj z a) (haw : a ≠ w) (hyz : y ≠ z) (τ : HoleSpin N a) :
    StateReach N t ⟨a, τ⟩ ⟨a, swapHoleSpin N a y z hay.ne hza.ne.symm τ⟩ := by
  have hwy : w ≠ y := hyw.ne.symm
  have hwz_ne : w ≠ z := hwz.ne
  have hzy : z ≠ y := hyz.symm
  by_cases hyzval : τ.val y = τ.val z
  · -- swapping two equal spins is the identity
    have hid : swapHoleSpin N a y z hay.ne hza.ne.symm τ = τ := by
      apply Subtype.ext; funext s
      rw [swapHoleSpin_val_apply]
      by_cases h1 : s = y <;> by_cases h2 : s = z <;> simp_all
    rw [hid]; exact StateReach.refl N t _
  · -- opposite spins: Boolean dichotomy on σ(w)
    have hbool : τ.val w = τ.val z ∨ τ.val w = τ.val y :=
      (by decide : ∀ b c d : Bool, b ≠ c → (d = c ∨ d = b)) _ _ _ hyzval
    rcases hbool with hwzv | hwyv
    · -- one trip
      have h := StateReach.threeCyclePerm_of_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz τ
      rwa [cyc3HoleSpin_eq_swap_of_val_eq N a y w z hay.ne haw hza.ne.symm hwy hwz_ne hzy τ hwzv]
        at h
    · -- two trips
      have h1 := StateReach.threeCyclePerm_of_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz τ
      have h2 := StateReach.threeCyclePerm_of_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz
        (cyc3HoleSpin N a y w z hay.ne haw hza.ne.symm τ)
      have h := h1.trans h2
      rwa [cyc3HoleSpin_twice_eq_swap_of_val_eq N a y w z hay.ne haw hza.ne.symm hwy hwz_ne hzy τ
        hwyv] at h

/-- **Length-4 exchange of an ADJACENT pair, one trip (Tasaki Fig. 11.9, the `y,z` pair).**  On the
loop `a — y — w — z — a` (hole at `a`), the spins at the *adjacent* corners `y` and `w` (the first
two cycle sites — `y` a hole-neighbour, `w` the corner opposite the hole) are exchanged by one
trip when the *other* hole-neighbour `z` carries the same spin as `y`.  This is the footnote-14
once/twice dichotomy applied to a pair that is NOT the hole's two neighbours — exactly Tasaki's
"`y` and `z` exchanged when the hole hops once in the opposite orientation". -/
theorem cyc3HoleSpin_eq_swap_pair_of_val_eq (N : ℕ) (a y w z : Fin (N + 1)) (hay : a ≠ y)
    (haw : a ≠ w) (haz : a ≠ z) (hwy : w ≠ y) (_hwz : w ≠ z) (hzy : z ≠ y) (σ : HoleSpin N a)
    (hval : σ.val y = σ.val z) :
    cyc3HoleSpin N a y w z hay haw haz σ = swapHoleSpin N a y w hay haw σ := by
  apply Subtype.ext; funext s
  rw [cyc3HoleSpin_val_apply, swapHoleSpin_val_apply]
  by_cases h1 : s = y <;> by_cases h2 : s = w <;> by_cases h3 : s = z <;>
    simp_all

/-- **Length-4 exchange of an ADJACENT pair, two trips (Tasaki Fig. 11.9).**  The second branch of
the Boolean dichotomy for the adjacent pair `{y, w}`: when the other hole-neighbour `z` carries the
same spin as `w`, going around the loop *twice* exchanges the spins at `y` and `w`. -/
theorem cyc3HoleSpin_twice_eq_swap_pair_of_val_eq (N : ℕ) (a y w z : Fin (N + 1)) (hay : a ≠ y)
    (haw : a ≠ w) (haz : a ≠ z) (hwy : w ≠ y) (hwz : w ≠ z) (hzy : z ≠ y) (σ : HoleSpin N a)
    (hval : σ.val w = σ.val z) :
    cyc3HoleSpin N a y w z hay haw haz (cyc3HoleSpin N a y w z hay haw haz σ)
      = swapHoleSpin N a y w hay haw σ := by
  apply Subtype.ext; funext s
  -- explicit values of the inner 3-cycle at the three corners (`simp_all` blows up here)
  have ey : (cyc3HoleSpin N a y w z hay haw haz σ).val y = σ.val w := by
    rw [cyc3HoleSpin_val_apply, if_pos rfl]
  have ew : (cyc3HoleSpin N a y w z hay haw haz σ).val w = σ.val z := by
    rw [cyc3HoleSpin_val_apply, if_neg hwy, if_pos rfl]
  have ez : (cyc3HoleSpin N a y w z hay haw haz σ).val z = σ.val y := by
    rw [cyc3HoleSpin_val_apply, if_neg hzy, if_neg (Ne.symm hwz), if_pos rfl]
  have es : ∀ u, u ≠ y → u ≠ w → u ≠ z →
      (cyc3HoleSpin N a y w z hay haw haz σ).val u = σ.val u := by
    intro u h1 h2 h3; rw [cyc3HoleSpin_val_apply, if_neg h1, if_neg h2, if_neg h3]
  rw [cyc3HoleSpin_val_apply, swapHoleSpin_val_apply]
  by_cases h1 : s = y
  · subst h1; rw [if_pos rfl, ew, if_pos rfl]; exact hval.symm
  · by_cases h2 : s = w
    · subst h2; rw [if_neg h1, if_pos rfl, ez, if_neg h1, if_pos rfl]
    · by_cases h3 : s = z
      · subst h3; rw [if_neg h1, if_neg h2, if_pos rfl, ey, if_neg h1, if_neg h2]; exact hval
      · rw [if_neg h1, if_neg h2, if_neg h3, es s h1 h2 h3, if_neg h1, if_neg h2]

/-- **Length-4 landing swap of an ADJACENT pair (Tasaki Fig. 11.9).**  On a 4-loop
`a → y → w → z → a` with the hole at the corner `a`, the spins at the *adjacent* corners `y` and `w`
(an edge of the loop — `y` a hole-neighbour, `w` the corner opposite the hole) can be exchanged in
place: one trip if the other hole-neighbour `z` carries `y`'s spin, two trips if it carries `w`'s
spin (a no-op if `σ(y) = σ(w)`).  Because spins are Boolean one of these always applies.  This is
the adjacent-pair sibling of `landing_swap_quad`; together they exchange *any* two of the occupied
corners, matching Tasaki's claim that a length-4 loop exchanges any pair on it. -/
theorem StateReach.landing_swap_quad_adj (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a y w z : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (hyw : (nagaokaBondGraph N t).Adj y w) (hwz : (nagaokaBondGraph N t).Adj w z)
    (hza : (nagaokaBondGraph N t).Adj z a) (haw : a ≠ w) (hyw_ne : y ≠ w) (hyz : y ≠ z)
    (τ : HoleSpin N a) :
    StateReach N t ⟨a, τ⟩ ⟨a, swapHoleSpin N a y w hay.ne haw τ⟩ := by
  by_cases hval : τ.val y = τ.val w
  · have hid : swapHoleSpin N a y w hay.ne haw τ = τ := by
      apply Subtype.ext; funext s
      rw [swapHoleSpin_val_apply]
      by_cases h1 : s = y <;> by_cases h2 : s = w <;> simp_all
    rw [hid]; exact StateReach.refl N t ⟨a, τ⟩
  · have hbool : τ.val z = τ.val y ∨ τ.val z = τ.val w :=
      (by decide : ∀ b c d : Bool, b ≠ c → (d = b ∨ d = c)) _ _ _ hval
    have hzy : z ≠ y := hyz.symm
    have hwz_ne : w ≠ z := hwz.ne
    have hwy : w ≠ y := hyw_ne.symm
    rcases hbool with hzyv | hzwv
    · have h := StateReach.threeCyclePerm_of_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz τ
      rwa [cyc3HoleSpin_eq_swap_pair_of_val_eq N a y w z hay.ne haw hza.ne.symm hwy hwz_ne hzy τ
        hzyv.symm] at h
    · have h1 := StateReach.threeCyclePerm_of_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz τ
      have h2 := StateReach.threeCyclePerm_of_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz
        (cyc3HoleSpin N a y w z hay.ne haw hza.ne.symm τ)
      have h := h1.trans h2
      rwa [cyc3HoleSpin_twice_eq_swap_pair_of_val_eq N a y w z hay.ne haw hza.ne.symm hwy hwz_ne hzy
        τ hzwv.symm] at h

/-- **The 15-puzzle exchange (length-4 loop): an exchange via an opposite-corner 4-loop from any
hole position.**  The 4-loop `{a, y, w, z}` instance of `swap_via_landing_walk`, where the landing
swap is the Boolean once/twice trip of `landing_swap_quad`. -/
theorem StateReach.swap_via_quad_walk (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a y w z p : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (hyw : (nagaokaBondGraph N t).Adj y w) (hwz : (nagaokaBondGraph N t).Adj w z)
    (hza : (nagaokaBondGraph N t).Adj z a) (haw : a ≠ w) (hyz : y ≠ z)
    (W : (nagaokaBondGraph N t).Walk p a) (hyW : y ∉ W.support) (hzW : z ∉ W.support)
    (σ : HoleSpin N p) :
    StateReach N t ⟨p, σ⟩
      ⟨p, swapHoleSpin N p y z
        (fun h => hyW (h ▸ W.start_mem_support)) (fun h => hzW (h ▸ W.start_mem_support)) σ⟩ :=
  StateReach.swap_via_landing_walk N t htsym htdiag hpos hay.ne hza.ne.symm W hyW hzW σ
    (StateReach.landing_swap_quad N t htsym htdiag hpos hay hyw hwz hza haw hyz _)

/-- The inclusion `G.induce s →g G` sending a vertex of the induced subgraph to the underlying
vertex.  (Induced adjacency is just the ambient adjacency restricted to `s`.) -/
def induceValHom {V : Type*} (G : SimpleGraph V) (s : Set V) : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => h

/-- **E2 routing: a walk avoiding two sites.**  If the subgraph induced on `Λ ∖ {y, z}` is connected
and `p, a` both avoid `y, z`, then there is a walk `p → a` in the full graph whose support avoids
both `y` and `z`.  This realises Tasaki's exchange-bond condition E2 (deleting the two exchanged
sites keeps the lattice connected) as a concrete hole route that never touches `y` or `z`, feeding
`StateReach.swap_via_triangle_walk`. -/
theorem exists_avoiding_walk_of_induce_connected {V : Type*} (G : SimpleGraph V) {y z : V}
    (hconn : (G.induce {w | w ≠ y ∧ w ≠ z}).Connected) {p a : V}
    (hp : p ≠ y ∧ p ≠ z) (ha : a ≠ y ∧ a ≠ z) :
    ∃ W : G.Walk p a, y ∉ W.support ∧ z ∉ W.support := by
  obtain ⟨W'⟩ := hconn.preconnected ⟨p, hp⟩ ⟨a, ha⟩
  have hsupp : ∀ x ∈ (W'.map (induceValHom G {w | w ≠ y ∧ w ≠ z})).support,
      x ≠ y ∧ x ≠ z := by
    intro x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨v, hv⟩, _, rfl⟩ := hx
    exact hv
  exact ⟨W'.map (induceValHom G _), fun hy => (hsupp y hy).1 rfl, fun hz => (hsupp z hz).2 rfl⟩

/-- **A triangle gives a common neighbour for any two of its vertices.**  If `w, α, β` are pairwise
adjacent (a complete triangle) and `y, z` are two distinct vertices among them, then the third
vertex `a` is a common neighbour and `y, z` are themselves adjacent — exactly the data
(`Adj a y`, `Adj y z`, `Adj z a`) that `StateReach.swap_via_triangle_walk` needs to swap the spins
at `y` and `z`.  (The triangle is complete, so every directed pair among `w, α, β` is an edge.) -/
theorem exists_common_neighbor_of_triangle {V : Type*} (G : SimpleGraph V) {w α β : V}
    (hwα : G.Adj w α) (hαβ : G.Adj α β) (hβw : G.Adj β w)
    {y z : V} (hy : y = w ∨ y = α ∨ y = β) (hz : z = w ∨ z = α ∨ z = β) (hyz : y ≠ z) :
    ∃ a : V, G.Adj a y ∧ G.Adj y z ∧ G.Adj z a := by
  rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
  · exact absurd rfl hyz
  · exact ⟨β, hβw, hwα, hαβ⟩
  · exact ⟨α, hwα.symm, hβw.symm, hαβ.symm⟩
  · exact ⟨β, hαβ.symm, hwα.symm, hβw.symm⟩
  · exact absurd rfl hyz
  · exact ⟨w, hwα, hαβ, hβw⟩
  · exact ⟨α, hαβ, hβw, hwα⟩
  · exact ⟨w, hβw.symm, hαβ.symm, hwα.symm⟩
  · exact absurd rfl hyz

/-- **A length-3 closed walk: its three bonds and that its support is exactly the three vertices.**
Refines `exists_triangle_adj_of_walk_length_three` by also certifying that every vertex on the walk
is one of the three triangle vertices `z', a, b` — needed to place the exchange-bond endpoints
`y, z` among them. -/
theorem walk_length_three_support_mem {V : Type*} (G : SimpleGraph V) {z' : V}
    (c : G.Walk z' z') (hlen : c.length = 3) :
    ∃ a b : V, G.Adj z' a ∧ G.Adj a b ∧ G.Adj b z' ∧
      ∀ x ∈ c.support, x = z' ∨ x = a ∨ x = b := by
  match c, hlen with
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ =>
    refine ⟨_, _, h1, h2, h3, fun x hx => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    tauto

/-- **A length-4 cycle: its four bonds, the pairwise-distinctness of its four corners, and that its
support is exactly those four vertices.**  From `IsCycle` (whose `support.tail` is `Nodup`) the four
corners `z', a, b, d` of the loop `z' — a — b — d — z'` are pairwise distinct, giving both the
adjacency data and the *diagonal* inequalities `z' ≠ b`, `a ≠ d` that the four edges alone do not
supply.  This is the length-4 analogue of `walk_length_three_support_mem`, feeding the exchange-bond
length-4 bridge (which must place the endpoints `y, z` among the four corners and tell whether they
are opposite or adjacent on the loop). -/
theorem cycle_length_four_data {V : Type*} (G : SimpleGraph V) {z' : V}
    (c : G.Walk z' z') (hcyc : c.IsCycle) (hlen : c.length = 4) :
    ∃ a b d : V, G.Adj z' a ∧ G.Adj a b ∧ G.Adj b d ∧ G.Adj d z' ∧
      z' ≠ a ∧ z' ≠ b ∧ z' ≠ d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      (∀ x ∈ c.support, x = z' ∨ x = a ∨ x = b ∨ x = d) := by
  match c, hlen, hcyc with
  | .cons h1 (.cons h2 (.cons h3 (.cons h4 .nil))), _, hcyc' =>
    have hnd := hcyc'.support_nodup
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, and_true,
      not_false_iff, List.nodup_nil] at hnd
    obtain ⟨⟨hab, had, haz⟩, ⟨hbd, hbz⟩, hdz⟩ := hnd
    refine ⟨_, _, _, h1, h2, h3, h4, (Ne.symm haz), (Ne.symm hbz), (Ne.symm hdz), hab, had, hbd,
      fun x hx => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    tauto

/-- **Lemma 11.9, exchange-bond step (length-3 loop): an exchange bond yields a reachable spin
swap.**  If `y, z` lie on a common triangle of bonds (E1, length 3) and deleting `y, z` keeps the
lattice connected (E2), then from any hole position `p ∉ {y, z}` the state `(p, σ)` reaches
`(p, swapHoleSpin y z σ)`.  This combines the triangle extraction, the common-neighbour, the E2
route, and the 15-puzzle exchange `StateReach.swap_via_triangle_walk`. -/
theorem StateReach.swap_of_exchange_len3 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {y z : Fin (N + 1)} (hyz : y ≠ z)
    {z' : Fin (N + 1)} (c : (nagaokaBondGraph N t).Walk z' z') (hlen : c.length = 3)
    (hyc : y ∈ c.support) (hzc : z ∈ c.support)
    (hE2 : ((nagaokaBondGraph N t).induce {w | w ≠ y ∧ w ≠ z}).Connected)
    {p : Fin (N + 1)} (hpy : p ≠ y) (hpz : p ≠ z) (σ : HoleSpin N p) :
    StateReach N t ⟨p, σ⟩ ⟨p, swapHoleSpin N p y z hpy hpz σ⟩ := by
  obtain ⟨a, b, h1, h2, h3, hmem⟩ := walk_length_three_support_mem _ c hlen
  obtain ⟨a3, ha3y, hyz_adj, hza3⟩ :=
    exists_common_neighbor_of_triangle _ h1 h2 h3 (hmem y hyc) (hmem z hzc) hyz
  obtain ⟨W, hyW, hzW⟩ :=
    exists_avoiding_walk_of_induce_connected (nagaokaBondGraph N t) hE2 ⟨hpy, hpz⟩
      ⟨ha3y.ne, hza3.ne.symm⟩
  exact StateReach.swap_via_triangle_walk N t htsym htdiag hpos ha3y hyz_adj hza3 W hyW hzW σ

/-- **A positive-length self-loop in the state quiver.**  If the hole at `p` has a bond-neighbour
`q`, then hopping `p → q → p` is a length-2 closed path that returns to the same state `(p, σ)` (the
round trip restores the configuration).  This supplies the diagonal `i = i` case of
`IsSStronglyConnected`, which demands a path of *positive* length even from a state to itself. -/
theorem exists_pos_selfPath (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) {p q : Fin (N + 1)}
    (σ : HoleSpin N p) (hpq : p ≠ q) (ht : 0 < t p q) :
    ∃ path : @Quiver.Path _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) ⟨p, σ⟩ ⟨p, σ⟩,
      0 < @Quiver.Path.length _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) _ _ path := by
  letI : Quiver _ := Matrix.toQuiver (-tasakiEffReMatrix N t)
  refine ⟨(holeHopHom' N t htsym htdiag p q σ hpq ht).toPath.comp
    (holeHopHom N t p q σ hpq ht).toPath, ?_⟩
  simp [Quiver.Path.length_toPath]

/-- **The spin swap of two sites is reachable from any hole position.**  The abstract relation that
Lemma 11.9's generation step: from *every* hole position `p ∉ {y, z}` the state `(p, σ)` reaches the
state with the spins at `y, z` exchanged.  Exchange bonds give the base instances
(`swap_of_exchange_len3`), and `ReachSwap.comp_via` propagates it along paths. -/
def ReachSwap (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) (y z : Fin (N + 1)) : Prop :=
  ∀ (p : Fin (N + 1)) (hpy : p ≠ y) (hpz : p ≠ z) (σ : HoleSpin N p),
    StateReach N t ⟨p, σ⟩ ⟨p, swapHoleSpin N p y z hpy hpz σ⟩

/-- `ReachSwap` is symmetric in the two sites. -/
theorem ReachSwap.symm {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ} {y z : Fin (N + 1)}
    (h : ReachSwap N t y z) (hyz : y ≠ z) : ReachSwap N t z y := by
  intro p hpz hpy σ
  rw [← swapHoleSpin_comm N p y z hpy hpz hyz]
  exact h p hpy hpz σ

/-- **Composition through an intermediate site** (the conjugation `(y z) = (y w)(w z)(y w)`): if the
swaps `{y, w}` and `{w, z}` are reachable, then so is `{y, z}`, *for holes also avoiding the
intermediate* `w`.  This is the inductive step of the distance generation argument. -/
theorem ReachSwap.comp_via {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ} {y w z : Fin (N + 1)}
    (hyw : ReachSwap N t y w) (hwz : ReachSwap N t w z)
    (hyw_ne : y ≠ w) (hwz_ne : w ≠ z) (hyz_ne : y ≠ z) :
    ∀ (p : Fin (N + 1)) (hpy : p ≠ y) (_hpw : p ≠ w) (hpz : p ≠ z) (σ : HoleSpin N p),
      StateReach N t ⟨p, σ⟩ ⟨p, swapHoleSpin N p y z hpy hpz σ⟩ := by
  intro p hpy hpw hpz σ
  rw [swapHoleSpin_conj N p y w z hpy hpw hpz hyw_ne hwz_ne hyz_ne]
  exact (hyw p hpy hpw σ).trans ((hwz p hpw hpz _).trans (hyw p hpy hpw _))

/-- **Base case of the generation: a length-3 exchange bond gives `ReachSwap`.**  Packages
`StateReach.swap_of_exchange_len3` (valid from every hole position avoiding `y, z`) as a `ReachSwap`
fact — the direct-edge instances from which `ReachSwap.comp_via` propagates the swap along
exchange-bond paths. -/
theorem reachSwap_of_exchange_len3 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {y z : Fin (N + 1)} (hyz : y ≠ z) {z' : Fin (N + 1)}
    (c : (nagaokaBondGraph N t).Walk z' z') (hlen : c.length = 3)
    (hyc : y ∈ c.support) (hzc : z ∈ c.support)
    (hE2 : ((nagaokaBondGraph N t).induce {w | w ≠ y ∧ w ≠ z}).Connected) :
    ReachSwap N t y z :=
  fun _p hpy hpz σ =>
    StateReach.swap_of_exchange_len3 N t htsym htdiag hpos hyz c hlen hyc hzc hE2 hpy hpz σ

/-- **Lemma 11.9, exchange-bond step (length-4 loop, opposite corners): an exchange bond yields a
reachable spin swap.**  If `y, z` are the *opposite corners* of a 4-loop — i.e. they have two
distinct common bond-neighbours `a, w` (so the loop is `a — y — w — z — a`, with `a, w` on the other
diagonal) — and deleting `y, z` keeps the lattice connected (E2), then from any hole `p ∉ {y, z}`
the state `(p, σ)` reaches `(p, swapHoleSpin y z σ)`.  This is the faithful length-4 analogue of
`StateReach.swap_of_exchange_len3`: Tasaki's Fig. 11.9 exchange always places the swapped pair on
one diagonal and the hole/auxiliary on the other.  It combines the E2 route with the footnote-14
once/twice trip `StateReach.swap_via_quad_walk`. -/
theorem StateReach.swap_of_exchange_len4 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {y z a w : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (haz : (nagaokaBondGraph N t).Adj a z) (hwy : (nagaokaBondGraph N t).Adj w y)
    (hwz : (nagaokaBondGraph N t).Adj w z) (haw : a ≠ w) (hyz : y ≠ z)
    (hE2 : ((nagaokaBondGraph N t).induce {v | v ≠ y ∧ v ≠ z}).Connected)
    {p : Fin (N + 1)} (hpy : p ≠ y) (hpz : p ≠ z) (σ : HoleSpin N p) :
    StateReach N t ⟨p, σ⟩ ⟨p, swapHoleSpin N p y z hpy hpz σ⟩ := by
  obtain ⟨W, hyW, hzW⟩ :=
    exists_avoiding_walk_of_induce_connected (nagaokaBondGraph N t) hE2 ⟨hpy, hpz⟩
      ⟨hay.ne, haz.ne⟩
  exact StateReach.swap_via_quad_walk N t htsym htdiag hpos hay hwy.symm hwz haz.symm haw hyz
    W hyW hzW σ

/-- **Base case of the generation (length-4 opposite corners): a 4-loop diagonal gives a swap.**
Packages `StateReach.swap_of_exchange_len4` as a `ReachSwap` fact (valid from every hole avoiding
`y, z`), the length-4 sibling of `reachSwap_of_exchange_len3`. -/
theorem reachSwap_of_exchange_len4 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {y z a w : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (haz : (nagaokaBondGraph N t).Adj a z) (hwy : (nagaokaBondGraph N t).Adj w y)
    (hwz : (nagaokaBondGraph N t).Adj w z) (haw : a ≠ w) (hyz : y ≠ z)
    (hE2 : ((nagaokaBondGraph N t).induce {v | v ≠ y ∧ v ≠ z}).Connected) :
    ReachSwap N t y z :=
  fun _p hpy hpz σ =>
    StateReach.swap_of_exchange_len4 N t htsym htdiag hpos hay haz hwy hwz haw hyz hE2 hpy hpz σ

/-- **Base case of the generation (length-4 adjacent corners): a 4-loop edge gives a swap.**
If `y, z` are *adjacent* corners of a 4-loop `a — y — z — b — a` (so `{y, z}` is a loop edge, with
`a, b` the other two corners) and deleting `y, z` keeps the lattice connected (E2), then `ReachSwap
N t y z`.  This is the adjacent-pair sibling of `reachSwap_of_exchange_len4`: the hole is routed to
the corner `a` (avoiding `y, z`) and the spins at `y, z` are exchanged in place by the once/twice
Boolean trip `StateReach.landing_swap_quad_adj` (Tasaki Fig. 11.9, the two-trip case). -/
theorem reachSwap_of_exchange_len4_adj (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {y z a b : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (hyz : (nagaokaBondGraph N t).Adj y z) (hzb : (nagaokaBondGraph N t).Adj z b)
    (hba : (nagaokaBondGraph N t).Adj b a) (haz : a ≠ z) (hyz_ne : y ≠ z) (hyb : y ≠ b)
    (hE2 : ((nagaokaBondGraph N t).induce {v | v ≠ y ∧ v ≠ z}).Connected) :
    ReachSwap N t y z := by
  intro p hpy hpz σ
  obtain ⟨W, hyW, hzW⟩ :=
    exists_avoiding_walk_of_induce_connected (nagaokaBondGraph N t) hE2 ⟨hpy, hpz⟩ ⟨hay.ne, haz⟩
  exact StateReach.swap_via_landing_walk N t htsym htdiag hpos hay.ne haz W hyW hzW σ
    (StateReach.landing_swap_quad_adj N t htsym htdiag hpos hay hyz hzb hba haz hyz_ne hyb _)

/-- **Lemma 11.9, the exchange-bond bridge (every exchange bond gives a reachable swap).**  If
`{y, z}` is an exchange bond of the bond graph (E1: `y, z` lie on a common loop of length 3 or 4;
E2: deleting `y, z` keeps the lattice connected), then `ReachSwap N t y z` — from every hole `p`
`p ∉ {y, z}` the spins at `y` and `z` can be exchanged.  The length-3 loop is the triangle case
(`reachSwap_of_exchange_len3`); the length-4 loop is dispatched on whether `y, z` are *opposite*
corners (`reachSwap_of_exchange_len4`, common-neighbour diagonal) or *adjacent* corners
(`reachSwap_of_exchange_len4_adj`, the footnote-14 once/twice trip) — Tasaki notes a length-4 loop
exchanges *any* pair on it because spins are Boolean.  This is the single edge fact feeding
`ReachSwapOff.of_walk`. -/
theorem reachSwap_of_isExchangeBond (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {y z : Fin (N + 1)} (hyz : y ≠ z)
    (h : IsExchangeBond (nagaokaBondGraph N t) y z) :
    ReachSwap N t y z := by
  obtain ⟨⟨z', c, _hcyc, hlen, hyc, hzc⟩, hE2⟩ := h
  rcases hlen with h3 | h4
  · exact reachSwap_of_exchange_len3 N t htsym htdiag hpos hyz c h3 hyc hzc hE2
  · obtain ⟨a, b, d, h1, h2, h3', h4', hZa, hZb, hZd, hab, had, hbd, hmem⟩ :=
      cycle_length_four_data (nagaokaBondGraph N t) c _hcyc h4
    have hy := hmem y hyc
    have hz := hmem z hzc
    rcases hy with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl
    · exact absurd rfl hyz
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h4' h1 h2 h3' had.symm hZa hZb hE2
    · exact reachSwap_of_exchange_len4 N t htsym htdiag hpos h1.symm h2 h4' h3'.symm had hZb hE2
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h1.symm h4'.symm h3'.symm h2.symm
        had hZd hZb hE2
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h2.symm h1.symm h4'.symm h3'.symm
        hZb.symm hZa.symm had hE2
    · exact absurd rfl hyz
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h1 h2 h3' h4' hZb hab had hE2
    · exact reachSwap_of_exchange_len4 N t htsym htdiag hpos h1 h4'.symm h2.symm h3' hZb had hE2
    · exact reachSwap_of_exchange_len4 N t htsym htdiag hpos h2 h1.symm h3'.symm h4' had hZb.symm
        hE2
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h3'.symm h2.symm h1.symm h4'.symm
        had.symm hab.symm hZb.symm hE2
    · exact absurd rfl hyz
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h2 h3' h4' h1 had hbd hZb.symm hE2
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h3' h4' h1 h2 hZb.symm hZd.symm
        had.symm hE2
    · exact reachSwap_of_exchange_len4 N t htsym htdiag hpos h4'.symm h1 h3' h2.symm hZb had.symm
        hE2
    · exact reachSwap_of_exchange_len4_adj N t htsym htdiag hpos h4'.symm h3'.symm h2.symm h1.symm
        hZb hbd.symm had.symm hE2
    · exact absurd rfl hyz

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

/-- **Equal magnetization at a common hole = equal occupied up-spin count.**  The doubled
magnetization at a fixed hole is `2·(#↑ among occupied sites) − N`
(`holeSpinMag_eq_two_mul_upCount_sub`), so two configurations at the same hole have the same
magnetization exactly when they carry the same number of up-spins on the occupied (non-hole) sites.
This is the counting input of the mismatch-reduction induction. -/
theorem occUpCount_eq_of_holeSpinMag_eq {N : ℕ} {q : Fin (N + 1)} (σ σ' : HoleSpin N q)
    (h : holeSpinMag N ⟨q, σ⟩ = holeSpinMag N ⟨q, σ'⟩) :
    (Finset.univ.filter (fun i => i ≠ q ∧ σ.val i = true)).card
      = (Finset.univ.filter (fun i => i ≠ q ∧ σ'.val i = true)).card := by
  have h1 : holeSpinMag N ⟨q, σ⟩
      = 2 * ((Finset.univ.filter (fun i => i ≠ q ∧ σ.val i = true)).card : ℤ) - N :=
    holeSpinMag_eq_two_mul_upCount_sub N ⟨q, σ⟩
  have h2 : holeSpinMag N ⟨q, σ'⟩
      = 2 * ((Finset.univ.filter (fun i => i ≠ q ∧ σ'.val i = true)).card : ℤ) - N :=
    holeSpinMag_eq_two_mul_upCount_sub N ⟨q, σ'⟩
  rw [h1, h2] at h
  omega

/-- **A spin swap preserves the magnetization.**  Exchanging the spins at two (non-hole) sites
permutes the occupied values by the involution `Equiv.swap x y`, so the up-count — and hence
`holeSpinMag` — is unchanged. -/
theorem holeSpinMag_swapHoleSpin (N : ℕ) (q x y : Fin (N + 1)) (hqx : q ≠ x) (hqy : q ≠ y)
    (σ : HoleSpin N q) :
    holeSpinMag N ⟨q, swapHoleSpin N q x y hqx hqy σ⟩ = holeSpinMag N ⟨q, σ⟩ := by
  have hval : ∀ w, (swapHoleSpin N q x y hqx hqy σ).val w = σ.val (Equiv.swap x y w) := by
    intro w
    rw [swapHoleSpin_val_apply, Equiv.swap_apply_def]
    rcases eq_or_ne w x with rfl | h1
    · simp
    · rcases eq_or_ne w y with rfl | h2
      · simp [h1]
      · simp [h1, h2]
  have h1 : holeSpinMag N ⟨q, swapHoleSpin N q x y hqx hqy σ⟩
      = 2 * ((Finset.univ.filter
          (fun i => i ≠ q ∧ (swapHoleSpin N q x y hqx hqy σ).val i = true)).card : ℤ) - N :=
    holeSpinMag_eq_two_mul_upCount_sub N _
  have h2 : holeSpinMag N ⟨q, σ⟩
      = 2 * ((Finset.univ.filter (fun i => i ≠ q ∧ σ.val i = true)).card : ℤ) - N :=
    holeSpinMag_eq_two_mul_upCount_sub N _
  suffices hc : (Finset.univ.filter
      (fun i => i ≠ q ∧ (swapHoleSpin N q x y hqx hqy σ).val i = true)).card
      = (Finset.univ.filter (fun i => i ≠ q ∧ σ.val i = true)).card by
    rw [h1, h2, hc]
  refine Finset.card_bij' (fun i _ => Equiv.swap x y i) (fun i _ => Equiv.swap x y i) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨haq, hav⟩ := ha
    refine ⟨fun h => haq ?_, by rw [← hval a]; exact hav⟩
    have h' := congrArg (Equiv.swap x y) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hqx hqy] at h'
    exact h'
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨hbq, hbv⟩ := hb
    refine ⟨fun h => hbq ?_, ?_⟩
    · have h' := congrArg (Equiv.swap x y) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hqx hqy] at h'
      exact h'
    · rw [hval, Equiv.swap_apply_self]
      exact hbv
  · intro a _
    exact Equiv.swap_apply_self x y a
  · intro b _
    exact Equiv.swap_apply_self x y b

/-- **Mismatch reduction (the generation Proposition; Tasaki footnote 13 → p. 41, "Proof of
Property (iii)").**  If from the hole `q` *every* pair of distinct occupied sites can be
spin-swapped (hypothesis `hswap`, to be supplied by the exchange-bond generation), then any two
configurations at hole `q` with equal magnetization are joined by `StateReach`: pick a site `x`
where `σ` is down but `σ'` is up and a site `y` where `σ` is up but `σ'` is down (both exist, in
equal numbers, by the up-count `upCount_eq_of_holeSpinMag_eq`), swap them — the number of
disagreeing sites drops by exactly `2` — and induct down to zero disagreement. -/
theorem StateReach.of_swaps_of_holeSpinMag_eq (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    {q : Fin (N + 1)}
    (hswap : ∀ (x y : Fin (N + 1)) (hqx : q ≠ x) (hqy : q ≠ y), x ≠ y →
      ∀ τ : HoleSpin N q, StateReach N t ⟨q, τ⟩ ⟨q, swapHoleSpin N q x y hqx hqy τ⟩)
    (σ σ' : HoleSpin N q)
    (hmag : holeSpinMag N ⟨q, σ⟩ = holeSpinMag N ⟨q, σ'⟩) :
    StateReach N t ⟨q, σ⟩ ⟨q, σ'⟩ := by
  suffices H : ∀ (k : ℕ) (σ : HoleSpin N q),
      holeSpinMag N ⟨q, σ⟩ = holeSpinMag N ⟨q, σ'⟩ →
      (Finset.univ.filter (fun s => σ.val s ≠ σ'.val s)).card = k →
      StateReach N t ⟨q, σ⟩ ⟨q, σ'⟩ from H _ σ hmag rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro σ hmagσ hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- no disagreement: the configurations coincide
    subst hk0
    have hall : ∀ s, σ.val s = σ'.val s := by
      intro s
      by_contra hne
      have hmem : s ∈ Finset.univ.filter (fun s => σ.val s ≠ σ'.val s) := by simp [hne]
      have hpos := Finset.card_pos.mpr ⟨s, hmem⟩
      omega
    have : σ = σ' := Subtype.ext (funext hall)
    rw [this]
    exact StateReach.refl N t _
  · -- a disagreement exists; locate an opposite pair and swap it away
    -- the full up-sets (hole included — the hole carries `true`) have equal size
    have hTins : ∀ τ : HoleSpin N q,
        Finset.univ.filter (fun i => τ.val i = true)
          = insert q (Finset.univ.filter (fun i => i ≠ q ∧ τ.val i = true)) := by
      intro τ
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hiq : i = q
      · subst hiq
        simp [τ.2]
      · simp [hiq]
    have hcardTT : (Finset.univ.filter (fun i => σ.val i = true)).card
        = (Finset.univ.filter (fun i => σ'.val i = true)).card := by
      have hnotmem : ∀ τ : HoleSpin N q,
          q ∉ Finset.univ.filter (fun i => i ≠ q ∧ τ.val i = true) := by
        intro τ
        simp
      rw [hTins σ, hTins σ', Finset.card_insert_of_notMem (hnotmem σ),
        Finset.card_insert_of_notMem (hnotmem σ'),
        occUpCount_eq_of_holeSpinMag_eq σ σ' hmagσ]
    have hMsplit : Finset.univ.filter (fun s => σ.val s ≠ σ'.val s)
        = Finset.univ.filter (fun s => σ.val s = false ∧ σ'.val s = true)
          ∪ Finset.univ.filter (fun s => σ.val s = true ∧ σ'.val s = false) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      cases hσs : σ.val s <;> cases hσ's : σ'.val s <;> simp
    have hABcard : (Finset.univ.filter (fun s => σ.val s = false ∧ σ'.val s = true)).card
        = (Finset.univ.filter (fun s => σ.val s = true ∧ σ'.val s = false)).card := by
      have e1 : Finset.univ.filter (fun s => σ.val s = false ∧ σ'.val s = true)
          = Finset.univ.filter (fun i => σ'.val i = true)
            \ Finset.univ.filter (fun i => σ.val i = true) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        cases hσs : σ.val s <;> simp
      have e2 : Finset.univ.filter (fun s => σ.val s = true ∧ σ'.val s = false)
          = Finset.univ.filter (fun i => σ.val i = true)
            \ Finset.univ.filter (fun i => σ'.val i = true) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        cases hσ's : σ'.val s <;> simp
      rw [e1, e2]
      have h1 := Finset.card_sdiff_add_card_inter
        (Finset.univ.filter (fun i => σ'.val i = true))
        (Finset.univ.filter (fun i => σ.val i = true))
      have h2 := Finset.card_sdiff_add_card_inter
        (Finset.univ.filter (fun i => σ.val i = true))
        (Finset.univ.filter (fun i => σ'.val i = true))
      rw [Finset.inter_comm] at h1
      omega
    have hMne : (Finset.univ.filter (fun s => σ.val s ≠ σ'.val s)).Nonempty :=
      Finset.card_pos.mp (by rw [hk]; exact hkpos)
    -- both directions of disagreement are realized
    obtain ⟨⟨x, hx⟩, y, hy⟩ :
        (Finset.univ.filter (fun s => σ.val s = false ∧ σ'.val s = true)).Nonempty ∧
          (Finset.univ.filter (fun s => σ.val s = true ∧ σ'.val s = false)).Nonempty := by
      obtain ⟨s, hs⟩ := hMne
      rw [hMsplit, Finset.mem_union] at hs
      rcases hs with hs | hs
      · exact ⟨⟨s, hs⟩, Finset.card_pos.mp
          (by rw [← hABcard]; exact Finset.card_pos.mpr ⟨s, hs⟩)⟩
      · exact ⟨Finset.card_pos.mp (by rw [hABcard]; exact Finset.card_pos.mpr ⟨s, hs⟩), ⟨s, hs⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    obtain ⟨hxσ, hxσ'⟩ := hx
    obtain ⟨hyσ, hyσ'⟩ := hy
    -- the hole carries `true`, so a `false`-valued site is never the hole
    have hqx : q ≠ x := by rintro rfl; rw [σ.2] at hxσ; exact absurd hxσ (by decide)
    have hqy : q ≠ y := by rintro rfl; rw [σ'.2] at hyσ'; exact absurd hyσ' (by decide)
    have hxy : x ≠ y := by rintro rfl; rw [hxσ] at hyσ; exact Bool.false_ne_true hyσ
    -- swap the pair and recurse on the strictly smaller disagreement set
    have hstep := hswap x y hqx hqy hxy σ
    set σ₂ := swapHoleSpin N q x y hqx hqy σ with hσ₂
    have hMnew : Finset.univ.filter (fun s => σ₂.val s ≠ σ'.val s)
        = ((Finset.univ.filter (fun s => σ.val s ≠ σ'.val s)).erase x).erase y := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hσ₂,
        swapHoleSpin_val_apply]
      by_cases h1 : s = x
      · subst h1; simp [hyσ, hxσ']
      · by_cases h2 : s = y
        · subst h2; simp [Ne.symm hxy, hxσ, hyσ']
        · simp [h1, h2]
    have hxM : x ∈ Finset.univ.filter (fun s => σ.val s ≠ σ'.val s) := by
      simp [hxσ, hxσ']
    have hyM : y ∈ (Finset.univ.filter (fun s => σ.val s ≠ σ'.val s)).erase x := by
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hxy, by simp [hyσ, hyσ']⟩
    have hknew : (Finset.univ.filter (fun s => σ₂.val s ≠ σ'.val s)).card = k - 2 := by
      rw [hMnew, Finset.card_erase_of_mem hyM, Finset.card_erase_of_mem hxM, hk]
      omega
    have hmag₂ : holeSpinMag N ⟨q, σ₂⟩ = holeSpinMag N ⟨q, σ'⟩ := by
      rw [hσ₂, holeSpinMag_swapHoleSpin]; exact hmagσ
    exact hstep.trans (ih (k - 2) (by omega) σ₂ hmag₂ hknew)

/-- **The parking lemma: a farthest vertex obstructs no connection.**  In a connected graph on a
nonempty finite vertex type there is a vertex `q` such that any two *other* vertices are joined by
a walk avoiding `q`.  Take `q` at maximum distance from a fixed root `r`: a geodesic from `r` to
any `v ≠ q` cannot pass through `q` (the leg beyond `q` would make `v` strictly farther than the
maximum), so routing `x ⤳ r ⤳ y` along two geodesics avoids `q`.  This replaces any cut-vertex
analysis: parking the hole at `q` leaves every other pair exchange-connected. -/
theorem exists_vertex_walks_avoid {V : Type*} [Finite V] (G : SimpleGraph V)
    (hconn : G.Connected) :
    ∃ q : V, ∀ x y : V, x ≠ q → y ≠ q → ∃ W : G.Walk x y, q ∉ W.support := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨r⟩ : Nonempty V := hconn.nonempty
  obtain ⟨q, -, hq⟩ := Finset.exists_max_image (Finset.univ : Finset V) (fun v => G.dist r v)
    ⟨r, Finset.mem_univ r⟩
  refine ⟨q, fun x y hx hy => ?_⟩
  -- a geodesic from the root to any vertex `v ≠ q` avoids `q`
  have key : ∀ v : V, v ≠ q → ∃ W : G.Walk r v, q ∉ W.support := by
    intro v hv
    obtain ⟨W, hWlen⟩ := hconn.exists_walk_length_eq_dist r v
    refine ⟨W, fun hqW => ?_⟩
    have hlen : (W.takeUntil q hqW).length + (W.dropUntil q hqW).length = W.length := by
      conv_rhs => rw [← SimpleGraph.Walk.take_spec W hqW]
      rw [SimpleGraph.Walk.length_append]
    have h1 : G.dist r q ≤ (W.takeUntil q hqW).length := SimpleGraph.dist_le _
    have h2 : G.dist q v ≤ (W.dropUntil q hqW).length := SimpleGraph.dist_le _
    have h3 : 0 < G.dist q v := (hconn.preconnected q v).pos_dist_of_ne (Ne.symm hv)
    have h4 : G.dist r v ≤ G.dist r q := hq v (Finset.mem_univ v)
    omega
  obtain ⟨W₁, h₁⟩ := key x hx
  obtain ⟨W₂, h₂⟩ := key y hy
  refine ⟨W₁.reverse.append W₂, fun hmem => ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff] at hmem
  rcases hmem with h | h
  · rw [SimpleGraph.Walk.support_reverse] at h
    exact h₁ (List.mem_reverse.mp h)
  · exact h₂ h

/-- **Reachability preserves magnetization.**  Every edge of the `−M` quiver stays in one
magnetization sector (`neg_tasakiEffReMatrix_pos_holeSpinMag_eq`), so any path — and hence
`StateReach` — does too. -/
theorem StateReach.holeSpinMag_eq {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ}
    {a b : (z : Fin (N + 1)) × HoleSpin N z} (h : StateReach N t a b) :
    holeSpinMag N a = holeSpinMag N b := by
  letI := Matrix.toQuiver (-tasakiEffReMatrix N t)
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons _ e ih => exact ih.trans (neg_tasakiEffReMatrix_pos_holeSpinMag_eq N t _ _ e.down)

/-- **Lemma 11.9, generation at the parked hole: every pair is swappable.**  If `q` is a vertex
that no pair needs (every two other sites are joined by an exchange-bond walk avoiding `q` — as
supplied by the parking lemma `exists_vertex_walks_avoid`), then with the hole at `q` *every* pair
of distinct occupied sites can be spin-swapped: propagate the exchange-bond swaps along the avoiding
walk (`ReachSwapOff.of_walk`); the hole `q` is off the walk's support, so the composed swap applies
at `q`. -/
theorem hswap_of_walks_avoid (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {q : Fin (N + 1)}
    (havoid : ∀ x y : Fin (N + 1), x ≠ q → y ≠ q →
      ∃ W : (exchangeBondGraph (nagaokaBondGraph N t)).Walk x y, q ∉ W.support)
    (x y : Fin (N + 1)) (hqx : q ≠ x) (hqy : q ≠ y) (hxy : x ≠ y) (τ : HoleSpin N q) :
    StateReach N t ⟨q, τ⟩ ⟨q, swapHoleSpin N q x y hqx hqy τ⟩ := by
  obtain ⟨W, hW⟩ := havoid x y (Ne.symm hqx) (Ne.symm hqy)
  exact ReachSwapOff.of_walk
    (fun h => reachSwap_of_exchangeBondAdj N t htsym htdiag hpos h) W hxy q hqx hqy
    (fun hmem => hW (List.mem_toFinset.mp hmem)) τ

/-- **Lemma 11.9, full sector reachability: any two same-magnetization one-hole states are
joined.**  The complete 15-puzzle assembly, for symmetric `t ≥ 0` with zero diagonal and an
exchange-bond-connected bond graph: park both holes at a farthest vertex `q` of the exchange-bond
graph (mobility through the connected bond graph), where every spin pair is exchangeable (the
parking lemma + the exchange-bond generation), then convert one configuration into the other by
the mismatch-reduction induction. -/
theorem StateReach.of_holeSpinMag_eq_of_connectedByExchangeBonds (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : ConnectedByExchangeBonds (nagaokaBondGraph N t))
    (a b : (z : Fin (N + 1)) × HoleSpin N z) (hmag : holeSpinMag N a = holeSpinMag N b) :
    StateReach N t a b := by
  -- the bond graph is connected, so holes are mobile
  have hbond := nagaokaBondGraph_connected_of_connectedByExchangeBonds N t hconn
  -- park position: a farthest vertex of the exchange-bond graph
  obtain ⟨q, havoid⟩ := exists_vertex_walks_avoid (exchangeBondGraph (nagaokaBondGraph N t)) hconn
  -- relocate both holes to `q`
  obtain ⟨τ, hτ⟩ := StateReach.exists_hole_at N t htsym htdiag hpos a.2 q
    (hbond.preconnected a.1 q)
  obtain ⟨τ', hτ'⟩ := StateReach.exists_hole_at N t htsym htdiag hpos b.2 q
    (hbond.preconnected b.1 q)
  -- the parked configurations share the magnetization
  have hmagτ : holeSpinMag N ⟨q, τ⟩ = holeSpinMag N ⟨q, τ'⟩ := by
    have h1 : holeSpinMag N (⟨a.1, a.2⟩ : (z : Fin (N + 1)) × HoleSpin N z)
        = holeSpinMag N ⟨q, τ⟩ := hτ.holeSpinMag_eq
    have h2 : holeSpinMag N (⟨b.1, b.2⟩ : (z : Fin (N + 1)) × HoleSpin N z)
        = holeSpinMag N ⟨q, τ'⟩ := hτ'.holeSpinMag_eq
    calc holeSpinMag N ⟨q, τ⟩ = holeSpinMag N a := by rw [← h1]
      _ = holeSpinMag N b := hmag
      _ = holeSpinMag N ⟨q, τ'⟩ := by rw [← h2]
  -- connect the parked configurations by pairwise swaps and compose
  have hmid : StateReach N t ⟨q, τ⟩ ⟨q, τ'⟩ :=
    StateReach.of_swaps_of_holeSpinMag_eq N t
      (fun x y hqx hqy hxy σ =>
        hswap_of_walks_avoid N t htsym htdiag hpos havoid x y hqx hqy hxy σ) τ τ' hmagτ
  have ha : StateReach N t a ⟨q, τ⟩ := by
    have : a = ⟨a.1, a.2⟩ := rfl
    rw [this]; exact hτ
  have hb : StateReach N t ⟨q, τ'⟩ b := by
    have : b = ⟨b.1, b.2⟩ := rfl
    rw [this]; exact (hτ'.symm N t htsym htdiag)
  exact (ha.trans hmid).trans hb

/-- **Lemma 11.9 capstone (zero-diagonal form): exchange-bond connectivity implies the
connectivity condition.**  For symmetric `t ≥ 0` with zero diagonal on at least two sites, if the
bond graph is connected by exchange bonds then every magnetization sector of `−M` is irreducible
(Definition 11.6).  Sector reachability is
`StateReach.of_holeSpinMag_eq_of_connectedByExchangeBonds`; the positive-length requirement is met
by an out-and-back hole hop on the diagonal (`exists_pos_selfPath`) and automatically off it. -/
theorem nagaokaConnectivity_of_connectedByExchangeBonds (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (hN : 1 ≤ N)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : ConnectedByExchangeBonds (nagaokaBondGraph N t)) :
    nagaokaConnectivity N t := by
  apply nagaokaConnectivity_of_reach N t hpos
  intro m i j
  letI := Matrix.toQuiver (-tasakiEffReMatrix N t)
  have hbond := nagaokaBondGraph_connected_of_connectedByExchangeBonds N t hconn
  have hmag : holeSpinMag N i.val = holeSpinMag N j.val := i.2.trans j.2.symm
  have hreach := StateReach.of_holeSpinMag_eq_of_connectedByExchangeBonds N t htsym htdiag hpos
    hconn i.val j.val hmag
  by_cases hij : i.val = j.val
  · -- diagonal: an out-and-back hole hop is a positive-length self-loop
    obtain ⟨v, hvne⟩ : ∃ v : Fin (N + 1), v ≠ i.val.1 := by
      have : Nontrivial (Fin (N + 1)) :=
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
      exact exists_ne i.val.1
    obtain ⟨W⟩ := hbond.preconnected i.val.1 v
    obtain ⟨u, hadj⟩ : ∃ u, (nagaokaBondGraph N t).Adj i.val.1 u := by
      cases W with
      | nil => exact absurd rfl hvne
      | cons h _ => exact ⟨_, h⟩
    obtain ⟨path, hlen⟩ := exists_pos_selfPath N t htsym htdiag i.val.2 hadj.ne
      (nagaokaBondGraph_adj_pos N t htsym hpos hadj)
    rw [← hij]
    exact ⟨path, hlen⟩
  · -- distinct states: any connecting path has positive length
    obtain ⟨p⟩ := hreach
    refine ⟨p, ?_⟩
    rcases Nat.eq_zero_or_pos p.length with h0 | hposlen
    · exact absurd (Quiver.Path.eq_of_length_zero p h0) hij
    · exact hposlen

/-- Zeroing the diagonal of the hopping does not change the Tasaki matrix: the matrix is `0` on the
diagonal block *by definition* and reads `t` only at off-diagonal pairs. -/
theorem tasakiEffReMatrix_zeroDiag (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) :
    tasakiEffReMatrix N (fun i j => if i = j then 0 else t i j) = tasakiEffReMatrix N t := by
  ext q p
  unfold tasakiEffReMatrix
  by_cases h : p.1 = q.1 <;> simp [h]

/-- Zeroing the diagonal of the hopping does not change the bond graph: adjacency requires
`x ≠ y` and reads `t` only there. -/
theorem nagaokaBondGraph_zeroDiag (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) :
    nagaokaBondGraph N (fun i j => if i = j then 0 else t i j) = nagaokaBondGraph N t := by
  ext x y
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    simpa only [if_neg hne, if_neg (Ne.symm hne)] using h
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    simpa only [if_neg hne, if_neg (Ne.symm hne)] using h

end LatticeSystem.Fermion

