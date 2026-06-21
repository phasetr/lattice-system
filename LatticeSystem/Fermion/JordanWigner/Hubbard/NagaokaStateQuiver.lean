import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaStateQuiverReach

/-!
# Nagaoka per-sector quiver: holeSpin-magnetization connectivity — capstone

Continued from `NagaokaStateQuiverReach.lean`, which builds the swap-walk and
graph-reachability foundation (`StateReach.swap_via_*`, `ReachSwap` /
`ReachSwapOff`, the generic `SimpleGraph` reachability lemmas, and
`nagaokaBondGraph_connected_*`).  This file carries the holeSpin-magnetization
connectivity layer used to discharge Tasaki Lemma 11.9: the counting bridge
`occUpCount_eq_of_holeSpinMag_eq`, the mismatch-reduction
`StateReach.of_swaps_of_holeSpinMag_eq` / `StateReach.holeSpinMag_eq`, the
strong-connectivity conclusion `nagaokaConnectivity_of_connectedByExchangeBonds`,
and the zero-diagonal facts `tasakiEffReMatrix_zeroDiag` /
`nagaokaBondGraph_zeroDiag`.
-/

namespace LatticeSystem.Fermion

open Matrix

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

