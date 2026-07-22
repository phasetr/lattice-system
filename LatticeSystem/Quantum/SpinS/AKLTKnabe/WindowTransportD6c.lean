import LatticeSystem.Quantum.SpinS.AKLTKnabe.BondProjectionAlgebraD6b
import LatticeSystem.Quantum.SpinS.AKLTKnabe.BlockDischargeE6

/-!
# Gate D6c Stage B: transport of the Knabe window certificate along the chain

This module belongs to Issue #5094 (Tasaki §7.1.4, Knabe's argument, pp. 188–190).
Gate E6 established the four-site certificate

  `akltWindow3HKnabePosSemidefE6 : (ĥ * ĥ − (2/5) • ĥ).PosSemidef`,   i.e. `ε₃ ≥ 2/5`,

for the *one* open three-bond window `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` living on the four-site chain `Fin 4`
(Tasaki eq. (7.1.30) with `ℓ = 3`).  Stage B carries that single certificate to **every** window
`ĥ_x` of a chain `Fin L` of arbitrary length, by exhibiting `ĥ_x` as the block embedding of `ĥ`
along the four window sites `x, x+1, x+2, x+3` and pushing positive semidefiniteness through the
embedding with `onEmbS_posSemidef` (Gate D6b item B5f).

The chain of the transport is
`akltWindowAt x = onEmbS (windowEmb x) akltWindow3H` (`akltWindowAt_eq_onEmbS`), then
`onEmbS_mul` / `onEmbS_smul` / `onEmbS_add` to move the whole quadratic expression
`ĥ² − (2/5) ĥ` inside the embedding, then `onEmbS_posSemidef`.  No `Matrix.PosSemidef` is ever
re-derived from entries here: the only certificate consumed is the Gate D5b Stage 4 one.

## Periodic ring versus open window (design risk R3 — this file is on the OPEN side)

Gate D6b Stage A was deliberately on *neither* side of the periodic/open distinction (all its
lemmas speak about arbitrary bonds under distinctness hypotheses only).  **Stage B is on the
`open` side**, and it is the file that has to get that side right:

* `akltWindowAt x` (Tasaki eq. (7.1.30), `ℓ = 3`) is the Hamiltonian of the **open** chain on the
  four sites `x, x+1, x+2, x+3`, i.e. it has **exactly three** bonds
  `{x,x+1}`, `{x+1,x+2}`, `{x+2,x+3}` — **never a fourth**.  It is written as three explicit
  `ringBond` applications, never as a sum over `Fin 4` and never through `akltHamiltonianS 4`
  (whose `ringCoupling` would close the window into a ring).
* The wrap bond belongs to the *other* object, `Ĥ'_AKLT = Σ_{y : Fin L} P̂_{y,y+1}` of
  eq. (7.1.7), which is **not defined in this file at all**; it is Stage C's responsibility, and
  it must include the wrap bond `{L−1, 0}`.
* The window at `x = L−1` (or `L−2`, `L−3`) does wrap *around* the ring — its four sites are
  `L−1, 0, 1, 2` — and that is correct and required, because Tasaki sums `x` over all `L` values.
  Wrapping around is not the same as adding a fourth bond: the four sites stay pairwise distinct
  as long as `4 ≤ L`, which is exactly the hypothesis carried below.

`ringBond` uses the **group** successor `y + 1` of `Fin L`, not the production `ringSucc`; the two
agree for `2 ≤ L` but no bridge lemma is needed in Stage B, because no statement here mentions
`ringSucc`.

## Hypothesis strength

The design sheet uses `5 ≤ L` throughout the three stages, that being what Stage C's five distinct
offsets `0, 1, 2, −1, −2` require.  Stage B needs only the four window sites to be distinct, i.e.
**`4 ≤ L`**, and is stated under that weaker hypothesis (weakest-hypothesis discipline, as in
Gate D6b item A5).  Stage C's `5 ≤ L` implies it.  The `4 ≤ L` boundary is not vacuous: the exact
rational contrast run before this file was written confirms the transport identity and the
transported certificate at `L = 4`, and confirms that both fail at `L = 3`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4, eqs. (7.1.7), (7.1.30), pp. 188–190.
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open scoped ComplexOrder

/-! ## B3: a bond projection of a subchain is the block embedding of a bond projection -/

/-- **Transport of a bond projection along an injective site list** (design item B3).  If
`ι : Fin m → Fin L` lists `m` distinct sites of the chain `Fin L`, then the bond projection of the
big chain on the two sites `ι i`, `ι j` is the block embedding along `ι` of the bond projection of
the small chain on the sites `i`, `j`.

Both sides are read off entrywise through `bondSpin2ProjectionS_apply_eq_sector2P2Entry`, so the
whole content is the equivalence of the two spectator guards: the single guard
`∀ k, k ≠ ι i → k ≠ ι j → σ' k = σ k` of the big chain versus the conjunction of the `onEmbS`
guard `∀ k ∉ range ι, σ' k = σ k` with the small-chain guard
`∀ p, p ≠ i → p ≠ j → σ' (ι p) = σ (ι p)`.  Injectivity of `ι` is what makes the sites `ι p` for
`p ≠ i, j` genuinely different from `ι i` and `ι j`. -/
theorem bondSpin2ProjectionS_onEmbS_transport {L m : ℕ} {ι : Fin m → Fin L}
    (hι : Function.Injective ι) {i j : Fin m} (hij : i ≠ j) :
    (bondSpin2ProjectionS (ι i) (ι j) : ManyBodyOpS (Fin L) 2)
      = onEmbS ι (bondSpin2ProjectionS i j) := by
  ext σ' σ
  rw [bondSpin2ProjectionS_apply_eq_sector2P2Entry (hι.ne hij) σ' σ, onEmbS_apply,
    bondSpin2ProjectionS_apply_eq_sector2P2Entry hij (σ' ∘ ι) (σ ∘ ι)]
  simp only [Function.comp_apply]
  have hfwd : (∀ k, k ≠ ι i → k ≠ ι j → σ' k = σ k) →
      (∀ k, (∀ p, ι p ≠ k) → σ' k = σ k) := by
    intro h k hk
    exact h k (fun he => hk i he.symm) (fun he => hk j he.symm)
  have hfwd' : (∀ k, k ≠ ι i → k ≠ ι j → σ' k = σ k) →
      (∀ p, p ≠ i → p ≠ j → σ' (ι p) = σ (ι p)) := by
    intro h p hpi hpj
    exact h (ι p) (fun he => hpi (hι he)) (fun he => hpj (hι he))
  have hbwd : (∀ k, (∀ p, ι p ≠ k) → σ' k = σ k) →
      (∀ p, p ≠ i → p ≠ j → σ' (ι p) = σ (ι p)) →
      (∀ k, k ≠ ι i → k ≠ ι j → σ' k = σ k) := by
    intro h1 h2 k hki hkj
    by_cases hk : ∃ p, ι p = k
    · obtain ⟨p, rfl⟩ := hk
      exact h2 p (fun hp => hki (congrArg ι hp)) (fun hp => hkj (congrArg ι hp))
    · exact h1 k (fun p hp => hk ⟨p, hp⟩)
  by_cases hg : ∀ k, k ≠ ι i → k ≠ ι j → σ' k = σ k
  · rw [if_pos hg, if_pos (hfwd hg), if_pos (hfwd' hg)]
  · rw [if_neg hg]
    by_cases h1 : ∀ k, (∀ p, ι p ≠ k) → σ' k = σ k
    · rw [if_pos h1, if_neg (fun h2 => hg (hbwd h1 h2))]
    · rw [if_neg h1]

/-! ## B1–B2: the four sites of a window, and their embedding -/

section Window

variable {L : ℕ} [NeZero L]

/-- The **window site list** `windowEmb x = (x, x+1, x+2, x+3)`, i.e. the four sites carrying the
open three-bond window `ĥ_{x,x+3}` of Tasaki eq. (7.1.30).  It is written as `i ↦ x + ofNat i`
rather than as the literal `![x, x+1, x+2, x+3]` of the design sheet: the two are the same
function (see `windowEmb_apply_*` below), but this form makes injectivity a one-line cancellation
and avoids the `Matrix.cons_val_one` normal-form hazard of `![·]` entirely.

`Fin.ofNat L` is used rather than the coercion `(· : ℕ) → Fin L`, because in this import context
the coercion is unavailable: mathlib makes `Fin.instAddMonoidWithOne` a *scoped* instance
(`Fin.NatCast`) to avoid coercion loops, so `Fin L` carries no `NatCast` unless that scope is
opened.  All `Fin L` arithmetic below is therefore done at the level of `Fin.val`. -/
def windowEmb (x : Fin L) : Fin 4 → Fin L := fun i => x + Fin.ofNat L i.val

/-- Unfolding a component of the window site list. -/
private theorem windowEmb_apply (x : Fin L) (i : Fin 4) :
    windowEmb x i = x + Fin.ofNat L i.val := rfl

/-- **The four window sites are distinct** (design item B2).  As soon as the chain has at least
four sites, `x, x+1, x+2, x+3` are pairwise distinct, so the window site list is injective and
`onEmbS_mul` / `onEmbS_posSemidef` apply along it.  At `L = 3` the statement is false (the exact
rational contrast confirms that the transport identity itself fails there). -/
theorem windowEmb_injective (hL : 4 ≤ L) (x : Fin L) : Function.Injective (windowEmb x) := by
  intro i j hij
  rw [windowEmb_apply, windowEmb_apply] at hij
  have h : Fin.ofNat L i.val = Fin.ofNat L j.val := add_left_cancel hij
  have hv : i.val % L = j.val % L := congrArg Fin.val h
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hL),
    Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt hL)] at hv
  exact Fin.ext hv

/-- The window site of index `0` is `x` itself. -/
private theorem windowEmb_apply_zero (x : Fin L) : windowEmb x 0 = x := by
  refine Fin.ext ?_
  change (x.val + 0 % L) % L = x.val
  rw [Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

/-- The window site of index `1` is `x + 1`. -/
private theorem windowEmb_apply_one (x : Fin L) : windowEmb x 1 = x + 1 := rfl

/-- The window site of index `2` is `x + 2`. -/
private theorem windowEmb_apply_two (x : Fin L) : windowEmb x 2 = x + 2 := rfl

/-- The window site of index `3` is `x + 3`. -/
private theorem windowEmb_apply_three (x : Fin L) : windowEmb x 3 = x + 3 := rfl

/-- Associativity of the window offsets, `(x + 1) + 1 = x + 2`, on a chain with at least four
sites.  Proved at the level of `Fin.val` because `Fin L` has no `AddMonoidWithOne` instance in
this import context (see `windowEmb`), so `one_add_one_eq_two` is unavailable. -/
private theorem shift_one_one (hL : 4 ≤ L) (x : Fin L) : x + 1 + 1 = x + 2 := by
  have h1 : ((1 : Fin L)).val = 1 := by
    change 1 % L = 1
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : ((2 : Fin L)).val = 2 := by
    change 2 % L = 2
    exact Nat.mod_eq_of_lt (by omega)
  refine Fin.ext ?_
  rw [Fin.val_add, Fin.val_add, Fin.val_add, h1, h2, Nat.mod_add_mod]

/-- Associativity of the window offsets, `(x + 2) + 1 = x + 3`, on a chain with at least four
sites. -/
private theorem shift_two_one (hL : 4 ≤ L) (x : Fin L) : x + 2 + 1 = x + 3 := by
  have h1 : ((1 : Fin L)).val = 1 := by
    change 1 % L = 1
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : ((2 : Fin L)).val = 2 := by
    change 2 % L = 2
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : ((3 : Fin L)).val = 3 := by
    change 3 % L = 3
    exact Nat.mod_eq_of_lt (by omega)
  refine Fin.ext ?_
  rw [Fin.val_add, Fin.val_add, Fin.val_add, h1, h2, h3, Nat.mod_add_mod]

/-! ## D-1 / D-3: the ring bond and the open window at an arbitrary site -/

/-- The **bond projection of the ring bond** `{y, y+1}` of the chain `Fin L`, Tasaki's
`P̂_{x,x+1}` of eq. (7.1.7).  The successor is the group successor of `Fin L`, so for `y = L−1`
this is the wrap bond `{L−1, 0}`. -/
noncomputable def ringBond (y : Fin L) : ManyBodyOpS (Fin L) 2 :=
  bondSpin2ProjectionS y (y + 1)

/-- The **open three-bond AKLT window at site `x`**, Tasaki `ĥ_{x,x+ℓ}` of eq. (7.1.30) with
`ℓ = 3`: the Hamiltonian of the *open* chain on the four sites `x, x+1, x+2, x+3`.  It has
**exactly three** bonds — the fourth ring bond `{x+3, x+4}` is *not* present, and neither is the
bond `{x+3, x}` that would close the window into a ring.  For `x` near the end of the chain the
four sites wrap around the ring, which is correct: Tasaki sums `x` over all `L` values. -/
noncomputable def akltWindowAt (x : Fin L) : ManyBodyOpS (Fin L) 2 :=
  ringBond x + ringBond (x + 1) + ringBond (x + 2)

/-! ## B4: the window is the block embedding of the four-site window -/

/-- **The window at `x` is the block embedding of the four-site window** (design item B4).  The
three bonds of `akltWindowAt x` are the images under `windowEmb x` of the three bonds
`{0,1}, {1,2}, {2,3}` of `akltWindow3H`, so `akltWindowAt x` is `akltWindow3H` embedded along the
four window sites.  This is the exact point at which the *open* character of the window is used:
`akltWindow3H` has no bond `{3, 0}`, hence neither has `akltWindowAt x`. -/
theorem akltWindowAt_eq_onEmbS (hL : 4 ≤ L) (x : Fin L) :
    akltWindowAt x = onEmbS (windowEmb x) akltWindow3H := by
  have hι : Function.Injective (windowEmb x) := windowEmb_injective hL x
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp only [akltWindowAt, ringBond, akltWindow3H, onEmbS_add]
  rw [shift_one_one hL x, shift_two_one hL x,
    ← bondSpin2ProjectionS_onEmbS_transport hι h01,
    ← bondSpin2ProjectionS_onEmbS_transport hι h12,
    ← bondSpin2ProjectionS_onEmbS_transport hι h23,
    windowEmb_apply_zero, windowEmb_apply_one, windowEmb_apply_two, windowEmb_apply_three]

/-! ## B5: the transported Knabe certificate -/

/-- **Stage B capstone: the Knabe window certificate holds at every site of every chain.**  For
every site `x` of a chain `Fin L` with at least four sites,

  `ĥ_x² − (2/5) ĥ_x ≥ 0`,   i.e.   `ε₃ ≥ 2/5`,

where `ĥ_x = akltWindowAt x` is the *open* three-bond AKLT window of Tasaki eq. (7.1.30) with
`ℓ = 3`.  There is no hypothesis beyond `4 ≤ L`: the constant `2/5` is a literal, uniform in `L`
and in `x`.

The proof is pure transport, with no new spectral input: the whole quadratic expression is moved
inside the block embedding (`onEmbS_mul` for the square, `onEmbS_smul` and `onEmbS_add` for the
affine part, `neg_one_smul` to express the subtraction without a dedicated `onEmbS_sub` lemma),
and then `onEmbS_posSemidef` (Gate D6b item B5f) applies the four-site certificate
`akltWindow3HKnabePosSemidefE6` of Gate E6 (the `sl₂` route; it replaces the withdrawn
`81 × 81` rational certificate of Gate D5b Stage 4, whose statement it reproduces verbatim).

Normalisation (pitfall R4): `2/5` belongs to the normalisation `ĥ = Σ P̂` built from the bond
projectors themselves.  It becomes `1/10` for Tasaki's `Ĥ'` of eq. (7.1.7) — that conversion is
Knabe's aggregation and belongs to Stage C — and `1/5` for the (7.1.1)-normalised
`akltHamiltonianS`.  Nothing here performs either conversion. -/
theorem akltWindowAt_knabe_posSemidef (hL : 4 ≤ L) (x : Fin L) :
    Matrix.PosSemidef (akltWindowAt x * akltWindowAt x - ((2 : ℂ) / 5) • akltWindowAt x) := by
  have hι : Function.Injective (windowEmb x) := windowEmb_injective hL x
  have hw : akltWindowAt x = onEmbS (windowEmb x) akltWindow3H := akltWindowAt_eq_onEmbS hL x
  have hmul : (akltWindowAt x * akltWindowAt x : ManyBodyOpS (Fin L) 2)
      = onEmbS (windowEmb x) (akltWindow3H * akltWindow3H) := by
    rw [hw, onEmbS_mul hι]
  have hsmul : (((2 : ℂ) / 5) • akltWindowAt x : ManyBodyOpS (Fin L) 2)
      = onEmbS (windowEmb x) (((2 : ℂ) / 5) • akltWindow3H) := by
    rw [hw, onEmbS_smul]
  have hneg : (onEmbS (windowEmb x) (-(((2 : ℂ) / 5) • akltWindow3H)) : ManyBodyOpS (Fin L) 2)
      = -(onEmbS (windowEmb x) (((2 : ℂ) / 5) • akltWindow3H)) := by
    rw [← neg_one_smul ℂ (((2 : ℂ) / 5) • akltWindow3H), onEmbS_smul, neg_one_smul]
  have key : (akltWindowAt x * akltWindowAt x - ((2 : ℂ) / 5) • akltWindowAt x :
        ManyBodyOpS (Fin L) 2)
      = onEmbS (windowEmb x) (akltWindow3H * akltWindow3H - ((2 : ℂ) / 5) • akltWindow3H) := by
    rw [hmul, hsmul,
      sub_eq_add_neg (akltWindow3H * akltWindow3H) (((2 : ℂ) / 5) • akltWindow3H),
      onEmbS_add, hneg, ← sub_eq_add_neg]
  rw [key]
  exact onEmbS_posSemidef hι
    LatticeSystem.Quantum.AKLTSl2BlockDischargeE6.akltWindow3HKnabePosSemidefE6

end Window

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
