import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaMagnetizationSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaBondGraph
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaStateQuiverCore

/-!
# Nagaoka state quiver: spin-swap reachability (foundation)

Foundational layer extracted from `NagaokaStateQuiverReach.lean` for build speed
(Tasaki §11.2, Lemma 11.9 15-puzzle exchange).  This file develops the on-state
exchange/swap reachability `StateReach.swap_of_exchange_len*`, the `ReachSwap` relation
(symmetry, composition, exchange-bond and length-3/4 walk witnesses) used by the
hole-avoiding `ReachSwapOff` bookkeeping and the bond-graph connectivity capstone kept
in the module `NagaokaStateQuiverReach.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.2, Lemma 11.9 (footnote 13).
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

end LatticeSystem.Fermion
