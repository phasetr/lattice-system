import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrder
import LatticeSystem.Math.PerronFrobeniusSymmetric
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank

/-!
# Tasaki §6.3 Proposition 6.5: Perron–Frobenius uniqueness route (kink ergodicity)

The Perron–Frobenius development toward the unique-ground-state clause of Proposition 6.5, split off
from `HiddenAntiferromagneticOrder.lean` for build speed.  Starting from the dressed restricted
matrix and its off-diagonal sign structure (in the base module), this file builds the kink-reduction
moves (`slidePM`, `annihPM`) and their hidden-AFM preservation, the open-arc combinatorics, the
balanced-sector connectivity (`hhaf_reachable_canonical`), the balanced-sector block irreducibility
and its Perron–Frobenius ground-state bound (`hhafDressedMatrix0_ground_finrank_le_one`), and the
Marshall-gauge transfer to the undressed real block
(`hhafRestrictedMatrixReal0_ground_finrank_le_one`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.3, Proposition 6.5; A. Gómez-Santos, Phys. Rev. Lett. **63**, 790 (1989).
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-! ## Canonical configuration and the `±`-spin count -/

/-- The **canonical** all-`0`-spin hidden-AFM configuration (`σ ≡ 1`, every site spin `0`), the base
case of the kink reduction. -/
def hhafCanonical (L : ℕ) : hhafConfig L := ⟨fun _ => 1, fun _ _ h => (h.2.1 rfl).elim⟩

/-- A site is never in its own (left-endpoint) open cyclic arc. -/
theorem not_inCyclicOpen_self_left {L : ℕ} (x y : Fin L) : ¬ InCyclicOpen x y x := by
  simp only [InCyclicOpen]; split_ifs <;> omega

/-- A site is never in its own (right-endpoint) open cyclic arc. -/
theorem not_inCyclicOpen_self_right {L : ℕ} (x y : Fin L) : ¬ InCyclicOpen x y y := by
  simp only [InCyclicOpen]; split_ifs <;> omega

/-- The cyclic successor's value is `a.val + 1` (no wrap) or `0` (wrap at `a.val + 1 = L`). -/
private theorem succ_val_cases {L : ℕ} {a b : Fin L} (hb : b.val = (a.val + 1) % L) :
    b.val = a.val + 1 ∨ (b.val = 0 ∧ a.val + 1 = L) := by
  rcases Nat.lt_or_ge (a.val + 1) L with hlt | hge
  · exact Or.inl (by rw [hb, Nat.mod_eq_of_lt hlt])
  · have heq : a.val + 1 = L := by have := a.isLt; omega
    exact Or.inr ⟨by rw [hb, heq, Nat.mod_self], heq⟩

/-- **Arc decomposition** (left endpoint successor): if `b` is the cyclic successor of `a` and
`b ≠ y`, then any site in the open arc `(a, y)` is either `b` itself or in the open arc `(b, y)`. -/
theorem inCyclicOpen_succ_left_imp {L : ℕ} {a b y z : Fin L}
    (hb : b.val = (a.val + 1) % L) (hby : b ≠ y) (h : InCyclicOpen a y z) :
    z = b ∨ InCyclicOpen b y z := by
  have hbyv : b.val ≠ y.val := fun hc => hby (Fin.ext hc)
  have ha := a.isLt; have hbv := b.isLt; have hyv := y.isLt; have hzv := z.isLt
  rw [Fin.ext_iff]
  simp only [InCyclicOpen] at h ⊢
  rcases succ_val_cases hb with hbe | ⟨hbe, hL⟩ <;> split_ifs at h ⊢ <;> omega

/-- **Arc inclusion** (right endpoint successor): if `b` is the cyclic successor of `a`, the open
arc `(x, a)` is contained in the open arc `(x, b)`. -/
theorem inCyclicOpen_succ_right_imp {L : ℕ} {a b x z : Fin L}
    (hb : b.val = (a.val + 1) % L) (hxa : x ≠ a) (h : InCyclicOpen x a z) :
    InCyclicOpen x b z := by
  have hxav : x.val ≠ a.val := fun hc => hxa (Fin.ext hc)
  have ha := a.isLt; have hbv := b.isLt; have hxv := x.isLt; have hzv := z.isLt
  simp only [InCyclicOpen] at h ⊢
  rcases succ_val_cases hb with hbe | ⟨hbe, hL⟩ <;> split_ifs at h ⊢ <;> omega

/-- **Successor non-membership**: if `b` (the cyclic successor of `a`, with `b ≠ y`) is not in the
open arc `(x, y)`, then neither is `a`. -/
theorem notInCyclicOpen_succ {L : ℕ} {a b x y : Fin L}
    (hb : b.val = (a.val + 1) % L) (hby : b ≠ y) (hnb : ¬ InCyclicOpen x y b) :
    ¬ InCyclicOpen x y a := by
  have hbyv : b.val ≠ y.val := fun hc => hby (Fin.ext hc)
  have ha := a.isLt; have hbv := b.isLt; have hxv := x.isLt; have hyv := y.isLt
  simp only [InCyclicOpen] at hnb ⊢
  rcases succ_val_cases hb with hbe | ⟨hbe, hL⟩ <;> split_ifs at hnb ⊢ <;> omega

/-- **Successor membership equivalence**: if `b` is the cyclic successor of `a` and both differ from
the endpoints `x, y`, then `a` and `b` are in the open arc `(x, y)` together or not at all. -/
theorem inCyclicOpen_succ_iff_mem {L : ℕ} {a b x y : Fin L}
    (hb : b.val = (a.val + 1) % L) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) :
    InCyclicOpen x y a ↔ InCyclicOpen x y b := by
  have haxv : a.val ≠ x.val := fun hc => hax (Fin.ext hc)
  have hayv : a.val ≠ y.val := fun hc => hay (Fin.ext hc)
  have hbxv : b.val ≠ x.val := fun hc => hbx (Fin.ext hc)
  have hbyv : b.val ≠ y.val := fun hc => hby (Fin.ext hc)
  have ha := a.isLt; have hbv := b.isLt; have hxv := x.isLt; have hyv := y.isLt
  simp only [InCyclicOpen]
  rcases succ_val_cases hb with hbe | ⟨hbe, hL⟩ <;> split_ifs <;> omega

/-- **Sub-arc inclusion** (shared left endpoint): if `a` is in the open arc `(x, y)`, then the open
arc `(x, a)` is contained in `(x, y)`. -/
theorem inCyclicOpen_sub_left {L : ℕ} {a x y z : Fin L}
    (ha : InCyclicOpen x y a) (h : InCyclicOpen x a z) : InCyclicOpen x y z := by
  have hav := a.isLt; have hxv := x.isLt; have hyv := y.isLt; have hzv := z.isLt
  simp only [InCyclicOpen] at ha h ⊢
  split_ifs at ha h ⊢ <;> omega

/-- **Sub-arc inclusion** (shared right endpoint): if `b` is in the open arc `(x, y)`, then the open
arc `(b, y)` is contained in `(x, y)`. -/
theorem inCyclicOpen_sub_right {L : ℕ} {b x y z : Fin L}
    (hb : InCyclicOpen x y b) (h : InCyclicOpen b y z) : InCyclicOpen x y z := by
  have hbv := b.isLt; have hxv := x.isLt; have hyv := y.isLt; have hzv := z.isLt
  simp only [InCyclicOpen] at hb h ⊢
  split_ifs at hb h ⊢ <;> omega

/-- The cyclic successor of the right endpoint is not in the open arc `(x, a)`. -/
theorem notInCyclicOpen_succ_right {L : ℕ} {a b x : Fin L}
    (hb : b.val = (a.val + 1) % L) (hax : x ≠ a) : ¬ InCyclicOpen x a b := by
  have hxav : x.val ≠ a.val := fun hc => hax (Fin.ext hc)
  have ha := a.isLt; have hbv := b.isLt; have hxv := x.isLt
  simp only [InCyclicOpen]
  rcases succ_val_cases hb with hbe | ⟨hbe, hL⟩ <;> split_ifs <;> omega

/-- The cyclic predecessor of the left endpoint is not in the open arc `(b, y)`. -/
theorem notInCyclicOpen_pred_left {L : ℕ} {a b y : Fin L}
    (hb : b.val = (a.val + 1) % L) (hyb : y ≠ b) : ¬ InCyclicOpen b y a := by
  have hybv : y.val ≠ b.val := fun hc => hyb (Fin.ext hc)
  have ha := a.isLt; have hbv := b.isLt; have hyv := y.isLt
  simp only [InCyclicOpen]
  rcases succ_val_cases hb with hbe | ⟨hbe, hL⟩ <;> split_ifs <;> omega

/-- **Slide move** (raw configuration): move the spin at site `a` onto the site `b`, leaving a `0`
behind at `a`.  When `a` carries a `±` spin and `b` (its cyclic neighbour) carries a `0`, this
slides the `±` spin one step along the ring. -/
def slidePM {L : ℕ} (σ : Fin L → Fin 3) (a b : Fin L) : Fin L → Fin 3 :=
  Function.update (Function.update σ a 1) b (σ a)

/-- The slide move's value: `0` at `a`, the moved spin at `b`, unchanged elsewhere. -/
theorem slidePM_apply {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b) (k : Fin L) :
    slidePM σ a b k = if k = b then σ a else if k = a then 1 else σ k := by
  rw [slidePM]
  by_cases hkb : k = b
  · subst hkb; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hkb, if_neg hkb]
    by_cases hka : k = a
    · subst hka; rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne hka, if_neg hka]

/-- The slide move is a single raise/lower (ladder) step on the ring-graph bond `{a, b}` when `b` is
the cyclic successor of `a` carrying a `0`-spin. -/
theorem slidePM_isRaiseLowerStep {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b)
    (hb : b.val = (a.val + 1) % L) (ha : σ a ≠ 1) (hb1 : σ b = 1) :
    RaiseLowerStepS (hhafRingGraph L) σ (slidePM σ a b) := by
  refine ⟨a, b, ⟨hab, Or.inl hb.symm⟩, ?_, ?_⟩
  · -- shift data: a and b change, value `σ a ∈ {0, 2}`
    have haa : slidePM σ a b a = 1 := by rw [slidePM_apply σ hab a, if_neg hab, if_pos rfl]
    have hbb : slidePM σ a b b = σ a := by rw [slidePM_apply σ hab b, if_pos rfl]
    rw [haa, hbb, hb1]
    -- σ a is 0 or 2 (a `±` spin)
    have : (σ a).val = 0 ∨ (σ a).val = 2 := by omega
    rcases this with h | h
    · left; constructor <;> simp [h]
    · right; constructor <;> simp [h]
  · intro k hka hkb
    rw [slidePM_apply σ hab k, if_neg hkb, if_neg hka]

/-- **The slide move preserves hidden antiferromagnetic order** — the heart of the kink-ergodicity
argument.  Sliding a `±` spin at `a` onto its `0`-carrying cyclic successor `b` keeps the strict
`+,−,…` alternation: the `±`-sign sequence in cyclic order is unchanged (only the position of one
`±` spin shifts by one past a `0`).  The proof transfers each `IsNextPM` pair of the moved
configuration back to an `IsNextPM` pair of `σ` (relabelling `b ↦ a`), using the arc-decomposition
lemmas `inCyclicOpen_succ_left_imp` / `inCyclicOpen_succ_right_imp` / `notInCyclicOpen_succ`. -/
theorem slidePM_isHiddenAFM {L : ℕ} {σ : Fin L → Fin 3} (hσ : IsHiddenAFMConfig σ)
    {a b : Fin L} (hab : a ≠ b) (hb : b.val = (a.val + 1) % L)
    (ha : σ a ≠ 1) (hb1 : σ b = 1) :
    IsHiddenAFMConfig (slidePM σ a b) := by
  intro x y hxy
  obtain ⟨hxny, hpmx, hpmy, harc⟩ := hxy
  simp only [IsPM] at hpmx hpmy
  have hτa : slidePM σ a b a = 1 := by rw [slidePM_apply σ hab a, if_neg hab, if_pos rfl]
  have hxa : x ≠ a := fun h => hpmx (by rw [h, hτa])
  have hya : y ≠ a := fun h => hpmy (by rw [h, hτa])
  have hvb : slidePM σ a b b = σ a := by rw [slidePM_apply σ hab b, if_pos rfl]
  have hvo : ∀ w, w ≠ a → w ≠ b → slidePM σ a b w = σ w := fun w hwa hwb => by
    rw [slidePM_apply σ hab w, if_neg hwb, if_neg hwa]
  have hbnotarc : ¬ InCyclicOpen x y b := fun hbarc => by
    have h := harc b hbarc; rw [hvb] at h; exact ha h
  by_cases hxb : x = b
  · by_cases hyb : y = b
    · exact absurd (hxb.trans hyb.symm) hxny
    · -- x = b, y ≠ b: transfer to the pair (a, y)
      have hby : b ≠ y := hxb ▸ hxny
      have hpy : σ y ≠ 1 := by have h := hpmy; rwa [hvo y hya hyb] at h
      rw [hxb, hvb, hvo y hya hyb]
      refine hσ a y ⟨fun h => hya h.symm, ha, hpy, ?_⟩
      intro z hz
      rcases inCyclicOpen_succ_left_imp hb hby hz with hzb | hzin
      · rw [hzb]; exact hb1
      · have hz1 := harc z (by rw [hxb]; exact hzin)
        have hzna : z ≠ a := fun h => not_inCyclicOpen_self_left a y (h ▸ hz)
        have hznb : z ≠ b := fun h => not_inCyclicOpen_self_left b y (h ▸ hzin)
        rw [← hvo z hzna hznb]; exact hz1
  · by_cases hyb : y = b
    · -- x ≠ b, y = b: transfer to the pair (x, a)
      have hpx : σ x ≠ 1 := by have h := hpmx; rwa [hvo x hxa hxb] at h
      rw [hvo x hxa hxb, hyb, hvb]
      refine hσ x a ⟨hxa, hpx, ha, ?_⟩
      intro z hz
      have hzx := inCyclicOpen_succ_right_imp hb hxa hz
      have hz1 := harc z (by rw [hyb]; exact hzx)
      have hzna : z ≠ a := fun h => not_inCyclicOpen_self_right x a (h ▸ hz)
      have hznb : z ≠ b := fun h => not_inCyclicOpen_self_right x b (h ▸ hzx)
      rw [← hvo z hzna hznb]; exact hz1
    · -- x ≠ b, y ≠ b: transfer to the pair (x, y)
      have hpx : σ x ≠ 1 := by have h := hpmx; rwa [hvo x hxa hxb] at h
      have hpy : σ y ≠ 1 := by have h := hpmy; rwa [hvo y hya hyb] at h
      rw [hvo x hxa hxb, hvo y hya hyb]
      refine hσ x y ⟨hxny, hpx, hpy, ?_⟩
      intro z hz
      have hanotarc : ¬ InCyclicOpen x y a := notInCyclicOpen_succ hb (Ne.symm hyb) hbnotarc
      have hzna : z ≠ a := fun h => hanotarc (h ▸ hz)
      have hznb : z ≠ b := fun h => hbnotarc (h ▸ hz)
      rw [← hvo z hzna hznb]; exact harc z hz

/-- The slide move, as a single step on the hidden-AFM subtype `RaiseLowerStepSHhaf`. -/
theorem slidePM_isRaiseLowerStepSHhaf {L : ℕ} (σ : hhafConfig L) {a b : Fin L} (hab : a ≠ b)
    (hb : b.val = (a.val + 1) % L) (ha : σ.1 a ≠ 1) (hb1 : σ.1 b = 1) :
    RaiseLowerStepSHhaf L σ ⟨slidePM σ.1 a b, slidePM_isHiddenAFM σ.2 hab hb ha hb1⟩ :=
  slidePM_isRaiseLowerStep σ.1 hab hb ha hb1

/-! ## Kink-reduction move: annihilating an adjacent `+,−` pair -/

/-- **Annihilation move** (raw configuration): set both `a` and `b` to `0`-spins.  When `a`, `b` are
adjacent and carry opposite `±` spins, this annihilates the `+,−` pair into two `0`s. -/
def annihPM {L : ℕ} (σ : Fin L → Fin 3) (a b : Fin L) : Fin L → Fin 3 :=
  Function.update (Function.update σ a 1) b 1

/-- The annihilation move's value: `0` at `a` and `b`, unchanged elsewhere. -/
theorem annihPM_apply {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b) (k : Fin L) :
    annihPM σ a b k = if k = a ∨ k = b then 1 else σ k := by
  rw [annihPM]
  by_cases hkb : k = b
  · subst hkb; rw [Function.update_self, if_pos (Or.inr rfl)]
  · rw [Function.update_of_ne hkb]
    by_cases hka : k = a
    · subst hka; rw [Function.update_self, if_pos (Or.inl rfl)]
    · rw [Function.update_of_ne hka, if_neg (by tauto)]

/-- The annihilation move is a single raise/lower (ladder) step on the ring-graph bond `{a, b}` when
`a`, `b` are adjacent and carry opposite `±` spins. -/
theorem annihPM_isRaiseLowerStep {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b)
    (hbv : b.val = (a.val + 1) % L) (ha : σ a ≠ 1) (hb1 : σ b ≠ 1) (hne : σ a ≠ σ b) :
    RaiseLowerStepS (hhafRingGraph L) σ (annihPM σ a b) := by
  refine ⟨a, b, ⟨hab, Or.inl hbv.symm⟩, ?_, ?_⟩
  · have haa : annihPM σ a b a = 1 := by rw [annihPM_apply σ hab a, if_pos (Or.inl rfl)]
    have hbb : annihPM σ a b b = 1 := by rw [annihPM_apply σ hab b, if_pos (Or.inr rfl)]
    rw [haa, hbb]
    -- σ a and σ b are opposite `±` values: {0, 2}
    have hva : (σ a).val = 0 ∨ (σ a).val = 2 := by omega
    have hvb : (σ b).val = 0 ∨ (σ b).val = 2 := by omega
    have hvne : (σ a).val ≠ (σ b).val := fun h => hne (Fin.ext h)
    rcases hva with hva | hva <;> rcases hvb with hvb | hvb <;> simp_all
  · intro k hka hkb
    rw [annihPM_apply σ hab k, if_neg (by tauto)]

/-- **The annihilation move preserves hidden antiferromagnetic order.**  Removing an adjacent,
opposite-sign `+,−` pair keeps the strict alternation: each `IsNextPM` pair of the annihilated
configuration either lies entirely off the removed pair (so it is already an `IsNextPM` pair of
`σ`), or straddles it, in which case the removed `a`, `b` are the only `±` sites between the
endpoints, and the endpoints inherit opposite signs through the chain `x, a, b, y`. -/
theorem annihPM_isHiddenAFM {L : ℕ} {σ : Fin L → Fin 3} (hσ : IsHiddenAFMConfig σ)
    {a b : Fin L} (hab : a ≠ b) (hbv : b.val = (a.val + 1) % L)
    (ha : σ a ≠ 1) (hb1 : σ b ≠ 1) (hne : σ a ≠ σ b) :
    IsHiddenAFMConfig (annihPM σ a b) := by
  intro x y hxy
  obtain ⟨hxny, hpmx, hpmy, harc⟩ := hxy
  simp only [IsPM] at hpmx hpmy
  have hτa : annihPM σ a b a = 1 := by rw [annihPM_apply σ hab a, if_pos (Or.inl rfl)]
  have hτb : annihPM σ a b b = 1 := by rw [annihPM_apply σ hab b, if_pos (Or.inr rfl)]
  have hxa : x ≠ a := fun h => hpmx (by rw [h, hτa])
  have hxb : x ≠ b := fun h => hpmx (by rw [h, hτb])
  have hya : y ≠ a := fun h => hpmy (by rw [h, hτa])
  have hyb : y ≠ b := fun h => hpmy (by rw [h, hτb])
  have hvo : ∀ w, w ≠ a → w ≠ b → annihPM σ a b w = σ w := fun w hwa hwb => by
    rw [annihPM_apply σ hab w, if_neg (by tauto)]
  have hpx : σ x ≠ 1 := by have h := hpmx; rw [hvo x hxa hxb] at h; exact h
  have hpy : σ y ≠ 1 := by have h := hpmy; rw [hvo y hya hyb] at h; exact h
  rw [hvo x hxa hxb, hvo y hya hyb]
  by_cases hain : InCyclicOpen x y a
  · -- a (hence b) lies between x and y: the chain x, a, b, y
    have hbin : InCyclicOpen x y b :=
      (inCyclicOpen_succ_iff_mem hbv hxa.symm hya.symm hxb.symm hyb.symm).mp hain
    have hxsa : σ x ≠ σ a := by
      refine hσ x a ⟨hxa, hpx, ha, ?_⟩
      intro z hz
      have hzna : z ≠ a := fun h => not_inCyclicOpen_self_right x a (h ▸ hz)
      have hznb : z ≠ b := fun h => notInCyclicOpen_succ_right hbv hxa (h ▸ hz)
      rw [← hvo z hzna hznb]; exact harc z (inCyclicOpen_sub_left hain hz)
    have hbsy : σ b ≠ σ y := by
      refine hσ b y ⟨fun h => hyb h.symm, hb1, hpy, ?_⟩
      intro z hz
      have hznb : z ≠ b := fun h => not_inCyclicOpen_self_left b y (h ▸ hz)
      have hzna : z ≠ a := fun h => notInCyclicOpen_pred_left hbv hyb (h ▸ hz)
      rw [← hvo z hzna hznb]; exact harc z (inCyclicOpen_sub_right hbin hz)
    intro heq
    have h1 : (σ x).val ≠ 1 := fun h => hpx (Fin.ext h)
    have h2 : (σ a).val ≠ 1 := fun h => ha (Fin.ext h)
    have h3 : (σ b).val ≠ 1 := fun h => hb1 (Fin.ext h)
    have h4 : (σ y).val ≠ 1 := fun h => hpy (Fin.ext h)
    have e1 : (σ x).val ≠ (σ a).val := fun h => hxsa (Fin.ext h)
    have e2 : (σ b).val ≠ (σ y).val := fun h => hbsy (Fin.ext h)
    have e3 : (σ a).val ≠ (σ b).val := fun h => hne (Fin.ext h)
    have e4 : (σ x).val = (σ y).val := congrArg Fin.val heq
    have := (σ x).isLt; have := (σ a).isLt; have := (σ b).isLt; have := (σ y).isLt
    omega
  · -- neither a nor b is between x and y: directly an `IsNextPM` pair of `σ`
    have hbout : ¬ InCyclicOpen x y b := fun hbi =>
      hain ((inCyclicOpen_succ_iff_mem hbv hxa.symm hya.symm hxb.symm hyb.symm).mpr hbi)
    refine hσ x y ⟨hxny, hpx, hpy, ?_⟩
    intro z hz
    have hzna : z ≠ a := fun h => hain (h ▸ hz)
    have hznb : z ≠ b := fun h => hbout (h ▸ hz)
    rw [← hvo z hzna hznb]; exact harc z hz

/-- The **number of `±` (nonzero) spins** in a hidden-AFM configuration — the induction measure for
the kink reduction (each annihilation removes a `+,−` pair, decreasing it by `2`). -/
def pmCount (L : ℕ) (σ : hhafConfig L) : ℕ :=
  (Finset.univ.filter (fun x => σ.1 x ≠ 1)).card

/-- A configuration has no `±` spins iff it is the canonical all-`0` configuration. -/
theorem pmCount_eq_zero_iff (L : ℕ) (σ : hhafConfig L) :
    pmCount L σ = 0 ↔ σ = hhafCanonical L := by
  rw [pmCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    apply Subtype.ext
    funext x
    have hx := h (Finset.mem_univ x)
    simpa [hhafCanonical] using hx
  · intro h x _
    rw [h]
    simp [hhafCanonical]

/-- The annihilation move as a single step on the hidden-AFM subtype. -/
theorem annihPM_isRaiseLowerStepSHhaf {L : ℕ} (σ : hhafConfig L) {a b : Fin L} (hab : a ≠ b)
    (hbv : b.val = (a.val + 1) % L) (ha : σ.1 a ≠ 1) (hb1 : σ.1 b ≠ 1) (hne : σ.1 a ≠ σ.1 b) :
    RaiseLowerStepSHhaf L σ ⟨annihPM σ.1 a b, annihPM_isHiddenAFM σ.2 hab hbv ha hb1 hne⟩ :=
  annihPM_isRaiseLowerStep σ.1 hab hbv ha hb1 hne

/-- Sliding a `±` spin onto an adjacent `0` preserves the number of `±` spins (the `±` at `p` is
removed, but a new one appears at `s`). -/
theorem slidePM_pmCount_card {L : ℕ} (σ : Fin L → Fin 3) {p s : Fin L} (hps : p ≠ s)
    (hp : σ p ≠ 1) (hs : σ s = 1) :
    (Finset.univ.filter (fun x => slidePM σ p s x ≠ 1)).card =
      (Finset.univ.filter (fun x => σ x ≠ 1)).card := by
  have hpmem : p ∈ Finset.univ.filter (fun x => σ x ≠ 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
  have hsnotmem : s ∉ (Finset.univ.filter (fun x => σ x ≠ 1)).erase p := by
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, hs]
    tauto
  have hset : (Finset.univ.filter (fun x => slidePM σ p s x ≠ 1)) =
      insert s ((Finset.univ.filter (fun x => σ x ≠ 1)).erase p) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
    rw [slidePM_apply σ hps x]
    by_cases hxs : x = s
    · subst hxs; simp [hp, Ne.symm hps]
    · by_cases hxp : x = p
      · subst hxp; simp [hps]
      · simp [hxs, hxp]
  rw [hset, Finset.card_insert_of_notMem hsnotmem, Finset.card_erase_of_mem hpmem]
  have : 1 ≤ (Finset.univ.filter (fun x => σ x ≠ 1)).card := Finset.card_pos.mpr ⟨p, hpmem⟩
  omega

/-- Annihilating a `±` pair strictly decreases the number of `±` spins. -/
theorem annihPM_pmCount_card_lt {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b)
    (ha : σ a ≠ 1) :
    (Finset.univ.filter (fun x => annihPM σ a b x ≠ 1)).card <
      (Finset.univ.filter (fun x => σ x ≠ 1)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    rw [annihPM_apply σ hab a, if_pos (Or.inl rfl)]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [annihPM_apply σ hab x] at hx
    by_cases h : x = a ∨ x = b
    · simp [h] at hx
    · rw [if_neg h] at hx; exact hx

/-! ## Kink-reduction measure and connectivity -/

/-- The **reduction measure** `Σ_{x : ± spin} (L − x)` — strictly decreasing under both kink moves
(sliding a `±` spin rightward and annihilating an adjacent pair), and `0` exactly on the canonical
configuration. -/
def hhafS {L : ℕ} (σ : Fin L → Fin 3) : ℕ :=
  ∑ x ∈ Finset.univ.filter (fun x => σ x ≠ 1), (L - x.val)

/-- The `±`-spin set after a slide: `p` removed, `s` inserted. -/
theorem slidePM_filter_eq {L : ℕ} (σ : Fin L → Fin 3) {p s : Fin L} (hps : p ≠ s)
    (hp : σ p ≠ 1) (hs : σ s = 1) :
    (Finset.univ.filter (fun x => slidePM σ p s x ≠ 1)) =
      insert s ((Finset.univ.filter (fun x => σ x ≠ 1)).erase p) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
  rw [slidePM_apply σ hps x]
  by_cases hxs : x = s
  · subst hxs; simp [hp, Ne.symm hps]
  · by_cases hxp : x = p
    · subst hxp; simp [hps]
    · simp [hxs, hxp]

/-- Sliding a `±` spin onto its non-wrapping successor strictly decreases the reduction measure. -/
theorem slidePM_hhafS_lt {L : ℕ} (σ : Fin L → Fin 3) {p s : Fin L} (hps : p ≠ s)
    (hsv : s.val = p.val + 1) (hp : σ p ≠ 1) (hs : σ s = 1) :
    hhafS (slidePM σ p s) < hhafS σ := by
  have hpmem : p ∈ Finset.univ.filter (fun x => σ x ≠ 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
  have hsnotmem : s ∉ (Finset.univ.filter (fun x => σ x ≠ 1)).erase p := by
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, hs]; tauto
  rw [hhafS, hhafS, slidePM_filter_eq σ hps hp hs, Finset.sum_insert hsnotmem,
    ← Finset.add_sum_erase _ (fun x => L - x.val) hpmem]
  apply Nat.add_lt_add_right
  have := s.isLt; have := p.isLt; omega

/-- The `±`-spin set after an annihilation: `a` and `b` removed. -/
theorem annihPM_filter_eq {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b) :
    (Finset.univ.filter (fun x => annihPM σ a b x ≠ 1)) =
      ((Finset.univ.filter (fun x => σ x ≠ 1)).erase a).erase b := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [annihPM_apply σ hab x]
  by_cases h : x = a ∨ x = b
  · rcases h with h | h <;> subst h <;> simp [hab, Ne.symm hab]
  · rw [if_neg h]; push Not at h; tauto

/-- Annihilating a `±` pair strictly decreases the reduction measure. -/
theorem annihPM_hhafS_lt {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b)
    (ha : σ a ≠ 1) : hhafS (annihPM σ a b) < hhafS σ := by
  have hamem : a ∈ Finset.univ.filter (fun x => σ x ≠ 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
  have hsub : (Finset.univ.filter (fun x => annihPM σ a b x ≠ 1)) ⊆
      (Finset.univ.filter (fun x => σ x ≠ 1)).erase a := by
    rw [annihPM_filter_eq σ hab]
    exact Finset.erase_subset _ _
  rw [hhafS, hhafS]
  calc ∑ x ∈ Finset.univ.filter (fun x => annihPM σ a b x ≠ 1), (L - x.val)
      ≤ ∑ x ∈ (Finset.univ.filter (fun x => σ x ≠ 1)).erase a, (L - x.val) :=
        Finset.sum_le_sum_of_subset hsub
    _ < ∑ x ∈ Finset.univ.filter (fun x => σ x ≠ 1), (L - x.val) := by
        rw [← Finset.add_sum_erase _ (fun x => L - x.val) hamem]
        have := a.isLt
        omega

/-- Annihilating a `±` pair removes exactly two `±` spins. -/
theorem annihPM_pmCount_eq {L : ℕ} (σ : Fin L → Fin 3) {a b : Fin L} (hab : a ≠ b)
    (ha : σ a ≠ 1) (hb1 : σ b ≠ 1) :
    (Finset.univ.filter (fun x => annihPM σ a b x ≠ 1)).card =
      (Finset.univ.filter (fun x => σ x ≠ 1)).card - 2 := by
  have hamem : a ∈ Finset.univ.filter (fun x => σ x ≠ 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
  have hbmem : b ∈ (Finset.univ.filter (fun x => σ x ≠ 1)).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb1⟩⟩
  rw [annihPM_filter_eq σ hab, Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem hamem]
  omega

/-- The open arc between a site and its (non-wrapping) cyclic successor is empty. -/
theorem not_inCyclicOpen_adjacent {L : ℕ} {p s z : Fin L} (hsv : s.val = p.val + 1) :
    ¬ InCyclicOpen p s z := by
  have := p.isLt; have := s.isLt; have := z.isLt
  simp only [InCyclicOpen]; split_ifs <;> omega

/-- **Single reduction step**: a balanced (even-`pmCount`), non-canonical hidden-AFM configuration
admits a single HAF ladder move to another balanced configuration with strictly smaller reduction
measure — either sliding the first `±` spin past an adjacent `0`, or annihilating it against an
adjacent `±` of opposite sign. -/
theorem hhaf_single_step {L : ℕ} (σ : hhafConfig L) (hpos : 0 < pmCount L σ)
    (heven : Even (pmCount L σ)) :
    ∃ σ' : hhafConfig L, RaiseLowerStepSHhaf L σ σ' ∧ Even (pmCount L σ') ∧
      hhafS σ'.1 < hhafS σ.1 := by
  classical
  set F := Finset.univ.filter (fun x => σ.1 x ≠ 1) with hF
  have hcardF : F.card = pmCount L σ := rfl
  have hFne : F.Nonempty := Finset.card_pos.mp (by rw [hcardF]; exact hpos)
  set p := F.min' hFne with hp
  have hpF : p ∈ F := F.min'_mem hFne
  have hpval : σ.1 p ≠ 1 := (Finset.mem_filter.mp hpF).2
  have hcard2 : 2 ≤ F.card := by
    obtain ⟨k, hk⟩ := heven; rw [hcardF]; omega
  have hpLe : p.val + 1 < L := by
    obtain ⟨q, hqF, hqp⟩ :=
      (Finset.one_lt_card_iff_nontrivial.mp (by omega : 1 < F.card)).exists_ne p
    have hle : p ≤ q := F.min'_le q hqF
    have : p.val < q.val := lt_of_le_of_ne hle (fun h => hqp (Fin.ext h).symm)
    have := q.isLt; omega
  set s : Fin L := ⟨p.val + 1, hpLe⟩ with hs
  have hsv : s.val = p.val + 1 := rfl
  have hps : p ≠ s := fun h => by simp [hs, Fin.ext_iff] at h
  have hbv : s.val = (p.val + 1) % L := by rw [hsv, Nat.mod_eq_of_lt hpLe]
  by_cases hsspin : σ.1 s = 1
  · refine ⟨⟨slidePM σ.1 p s, slidePM_isHiddenAFM σ.2 hps hbv hpval hsspin⟩,
      slidePM_isRaiseLowerStepSHhaf σ hps hbv hpval hsspin, ?_,
      slidePM_hhafS_lt σ.1 hps hsv hpval hsspin⟩
    have hpc : pmCount L ⟨slidePM σ.1 p s, slidePM_isHiddenAFM σ.2 hps hbv hpval hsspin⟩ =
        pmCount L σ := slidePM_pmCount_card σ.1 hps hpval hsspin
    rw [hpc]; exact heven
  · have hnext : IsNextPM σ.1 p s :=
      ⟨hps, hpval, hsspin, fun z hz => absurd hz (not_inCyclicOpen_adjacent hsv)⟩
    have hopp : σ.1 p ≠ σ.1 s := σ.2 p s hnext
    refine ⟨⟨annihPM σ.1 p s, annihPM_isHiddenAFM σ.2 hps hbv hpval hsspin hopp⟩,
      annihPM_isRaiseLowerStepSHhaf σ hps hbv hpval hsspin hopp, ?_,
      annihPM_hhafS_lt σ.1 hps hpval⟩
    have hpc : pmCount L ⟨annihPM σ.1 p s, annihPM_isHiddenAFM σ.2 hps hbv hpval hsspin hopp⟩ =
        pmCount L σ - 2 := annihPM_pmCount_eq σ.1 hps hpval hsspin
    rw [hpc]
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩

/-- HAF-internal reachability is symmetric (each ladder move is reversible). -/
theorem RaiseLowerReachableSHhaf_symm {L : ℕ} {σ τ : hhafConfig L}
    (h : RaiseLowerReachableSHhaf L σ τ) : RaiseLowerReachableSHhaf L τ σ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    have hstep' : RaiseLowerStepSHhaf L _ _ := RaiseLowerStepS.symm hstep
    exact (Relation.ReflTransGen.single hstep').trans ih

/-- **Connectivity (to canonical)**: every balanced (even-`pmCount`) hidden-AFM configuration is
HAF-reachable from the canonical all-`0` configuration.  The reduction inducts on the measure
`hhafS`, peeling one slide or annihilation at a time. -/
theorem hhaf_reachable_to_canonical {L : ℕ} (σ : hhafConfig L) (heven : Even (pmCount L σ)) :
    RaiseLowerReachableSHhaf L σ (hhafCanonical L) := by
  suffices h : ∀ n (τ : hhafConfig L), hhafS τ.1 = n → Even (pmCount L τ) →
      RaiseLowerReachableSHhaf L τ (hhafCanonical L) from h _ σ rfl heven
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro τ hn heven'
    by_cases hpos : 0 < pmCount L τ
    · obtain ⟨τ', hstep, heven'', hlt⟩ := hhaf_single_step τ hpos heven'
      exact (Relation.ReflTransGen.single hstep).trans (IH (hhafS τ'.1) (hn ▸ hlt) τ' rfl heven'')
    · have hz : pmCount L τ = 0 := by omega
      rw [(pmCount_eq_zero_iff L τ).mp hz]
      exact Relation.ReflTransGen.refl

/-- **Connectivity (from canonical)**: the canonical configuration reaches every balanced hidden-AFM
configuration — the symmetric form of `hhaf_reachable_to_canonical`. -/
theorem hhaf_reachable_canonical {L : ℕ} (σ : hhafConfig L) (heven : Even (pmCount L σ)) :
    RaiseLowerReachableSHhaf L (hhafCanonical L) σ :=
  RaiseLowerReachableSHhaf_symm (hhaf_reachable_to_canonical σ heven)

/-! ## Balanced (charge-`0`) sector block and its Perron–Frobenius irreducibility -/

/-- The **balanced sector**: hidden-AFM configurations with an even number of `±` spins (equal
numbers of `+` and `−` — magnetization `0`), the sector containing the antiferromagnetic ground
state and on which the dressed matrix is irreducible. -/
abbrev hhafConfig0 (L : ℕ) : Type := {σ : hhafConfig L // Even (pmCount L σ)}

/-- The canonical all-`0` configuration is balanced (`pmCount = 0`). -/
def hhafCanonical0 (L : ℕ) : hhafConfig0 L :=
  ⟨hhafCanonical L, by rw [(pmCount_eq_zero_iff L (hhafCanonical L)).mpr rfl]; exact ⟨0, rfl⟩⟩

instance hhafConfig0_nonempty (L : ℕ) : Nonempty (hhafConfig0 L) := ⟨hhafCanonical0 L⟩

/-- A single HAF ladder step on the balanced sector. -/
abbrev RaiseLowerStepSHhaf0 (L : ℕ) (σ τ : hhafConfig0 L) : Prop :=
  RaiseLowerStepSHhaf L σ.1 τ.1

/-- Balanced-sector HAF reachability. -/
abbrev RaiseLowerReachableSHhaf0 (L : ℕ) : hhafConfig0 L → hhafConfig0 L → Prop :=
  Relation.ReflTransGen (RaiseLowerStepSHhaf0 L)

/-- Every balanced configuration reaches the canonical one within the balanced sector. -/
theorem hhaf_reachable_to_canonical0 {L : ℕ} (σ : hhafConfig0 L) :
    RaiseLowerReachableSHhaf0 L σ (hhafCanonical0 L) := by
  suffices h : ∀ n (τ : hhafConfig0 L), hhafS τ.1.1 = n →
      RaiseLowerReachableSHhaf0 L τ (hhafCanonical0 L) from h _ σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro τ hn
    by_cases hpos : 0 < pmCount L τ.1
    · obtain ⟨σ'', hstep, heven'', hlt⟩ := hhaf_single_step τ.1 hpos τ.2
      have hstep0 : RaiseLowerStepSHhaf0 L τ ⟨σ'', heven''⟩ := hstep
      exact (Relation.ReflTransGen.single hstep0).trans
        (IH (hhafS σ''.1) (hn ▸ hlt) ⟨σ'', heven''⟩ rfl)
    · have hz : pmCount L τ.1 = 0 := by omega
      have hτc : τ = hhafCanonical0 L := Subtype.ext ((pmCount_eq_zero_iff L τ.1).mp hz)
      rw [hτc]

/-- Balanced-sector reachability is symmetric. -/
theorem RaiseLowerReachableSHhaf0_symm {L : ℕ} {σ τ : hhafConfig0 L}
    (h : RaiseLowerReachableSHhaf0 L σ τ) : RaiseLowerReachableSHhaf0 L τ σ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    have hstep' : RaiseLowerStepSHhaf0 L _ _ := RaiseLowerStepS.symm hstep
    exact (Relation.ReflTransGen.single hstep').trans ih

/-- The **balanced-sector shifted dressed matrix** `c·I − M` restricted to `hhafConfig0`. -/
noncomputable def hhafShiftedMatrix0 (L : ℕ) (c : ℝ) :
    Matrix (hhafConfig0 L) (hhafConfig0 L) ℝ :=
  (c • (1 : Matrix (hhafConfig L) (hhafConfig L) ℝ) - hhafDressedMatrix L).submatrix
    Subtype.val Subtype.val

/-- Balanced-sector walk-to-power positivity (mirror of the `hhafReachable` version on the balanced
subtype). -/
theorem exists_matrixPow_apply_pos_of_hhafReachable0 (L : ℕ)
    {B : Matrix (hhafConfig0 L) (hhafConfig0 L) ℝ}
    (hB_nn : ∀ σ τ, 0 ≤ B σ τ)
    (hB_step : ∀ {σ τ : hhafConfig0 L}, RaiseLowerStepSHhaf0 L σ τ → 0 < B τ σ)
    {σ σ' : hhafConfig0 L} (hreach : RaiseLowerReachableSHhaf0 L σ σ') :
    ∃ k : ℕ, 0 < (B ^ k) σ' σ := by
  induction hreach with
  | refl => exact ⟨0, by simp [Matrix.one_apply_eq]⟩
  | tail _h₁ h₂ ih =>
    obtain ⟨k, hpos⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (hB_nn _ _) (Matrix.pow_apply_nonneg hB_nn _ _ _)
    · exact ⟨_, Finset.mem_univ _, mul_pos (hB_step h₂) hpos⟩

/-- **Irreducibility of the balanced-sector shifted matrix.**  For an even ring and a shift `c`
strictly above the restricted max energy, `c·I − M` restricted to the balanced sector is
Perron–Frobenius irreducible: nonnegative (`hhafShifted_entry_nonneg`) and entrywise-positive in
some power (connectivity + per-step positivity). -/
theorem hhafShiftedMatrix0_isIrreducible (L : ℕ) (hLeven : Even L)
    {c : ℝ} (hc : hhafMaxEnergy L < c) :
    (hhafShiftedMatrix0 L c).IsIrreducible := by
  have hnn : ∀ σ τ : hhafConfig0 L, 0 ≤ hhafShiftedMatrix0 L c σ τ := fun σ τ =>
    hhafShifted_entry_nonneg L hLeven (le_of_lt hc) σ.1 τ.1
  rw [Matrix.isIrreducible_iff_exists_pow_pos hnn]
  intro σ τ
  by_cases hστ : σ = τ
  · subst hστ
    refine ⟨1, Nat.one_pos, ?_⟩
    have hdiag : hhafShiftedMatrix0 L c σ σ = c - hhafDressedMatrix L σ.1 σ.1 := by
      rw [hhafShiftedMatrix0, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [pow_one, hdiag]
    have := hhafDressedMatrix_diag_le_hhafMaxEnergy L σ.1
    linarith
  · have hreach : RaiseLowerReachableSHhaf0 L τ σ :=
      (hhaf_reachable_to_canonical0 τ).trans
        (RaiseLowerReachableSHhaf0_symm (hhaf_reachable_to_canonical0 σ))
    obtain ⟨k, hk⟩ := exists_matrixPow_apply_pos_of_hhafReachable0 L hnn
      (fun {a b} hstep => by
        have h := hhafShifted_pos_of_stepHhaf L hLeven (c := c)
          (σ := a.1) (τ := b.1) hstep
        simpa only [hhafShiftedMatrix0, Matrix.submatrix_apply] using h) hreach
    refine ⟨k, ?_, hk⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [pow_zero, Matrix.one_apply_ne hστ] at hk
      exact absurd hk (lt_irrefl 0)
    · exact hkpos

/-- The **dressed restricted matrix on the balanced sector** (the submatrix of `hhafDressedMatrix`
on `hhafConfig0`). -/
noncomputable def hhafDressedMatrix0 (L : ℕ) : Matrix (hhafConfig0 L) (hhafConfig0 L) ℝ :=
  (hhafDressedMatrix L).submatrix Subtype.val Subtype.val

/-- The balanced-sector dressed matrix is symmetric. -/
theorem hhafDressedMatrix0_isSymm (L : ℕ) : (hhafDressedMatrix0 L).IsSymm :=
  (hhafDressedMatrix_isSymm L).submatrix Subtype.val

/-- The balanced-sector shifted matrix is `c·I − M₀` (the identity restricts since `Subtype.val` is
injective). -/
theorem hhafShiftedMatrix0_eq (L : ℕ) (c : ℝ) :
    hhafShiftedMatrix0 L c =
      c • (1 : Matrix (hhafConfig0 L) (hhafConfig0 L) ℝ) - hhafDressedMatrix0 L := by
  ext σ τ
  simp only [hhafShiftedMatrix0, hhafDressedMatrix0, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Subtype.val_inj]

/-- **Unique balanced-sector ground state (Perron–Frobenius).**  For an even ring, the
balanced-sector dressed matrix has a strictly positive lowest eigenvector with a one-dimensional
eigenspace — the unique ground state of the antiferromagnetic chain within the balanced (charge-`0`)
sector of `H_HAF`. -/
theorem hhafDressedMatrix0_ground_finrank_le_one (L : ℕ) (hLeven : Even L) :
    ∃ (μ : ℝ) (v : hhafConfig0 L → ℝ), (∀ i, 0 < v i) ∧
      (hhafDressedMatrix0 L).mulVec v = μ • v ∧
      (∀ (lam : ℝ) (w : hhafConfig0 L → ℝ), w ≠ 0 →
        (hhafDressedMatrix0 L).mulVec w = lam • w → μ ≤ lam) ∧
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (hhafDressedMatrix0 L)) μ) ≤ 1 := by
  apply LatticeSystem.Math.perronFrobenius_real_symmetric (hhafDressedMatrix0 L)
    (hhafDressedMatrix0_isSymm L) (hhafMaxEnergy L + 1)
  rw [← hhafShiftedMatrix0_eq]
  exact hhafShiftedMatrix0_isIrreducible L hLeven (by linarith)

/-! ## Marshall-gauge transfer to the undressed balanced block -/

/-- The **real (undressed) restricted matrix on the balanced sector**. -/
noncomputable def hhafRestrictedMatrixReal0 (L : ℕ) : Matrix (hhafConfig0 L) (hhafConfig0 L) ℝ :=
  (hhafRestrictedMatrixReal L).submatrix Subtype.val Subtype.val

/-- The **balanced-sector Marshall sign diagonal** `Θ` (entries `±1`). -/
noncomputable def hhafMarshallDiag0 (L : ℕ) : Matrix (hhafConfig0 L) (hhafConfig0 L) ℝ :=
  Matrix.diagonal (fun σ : hhafConfig0 L => (marshallSignS (ringSublattice L) σ.1.1).re)

/-- The Marshall sign diagonal squares to the identity (each entry is `±1`). -/
theorem hhafMarshallDiag0_mul_self (L : ℕ) :
    hhafMarshallDiag0 L * hhafMarshallDiag0 L = 1 := by
  rw [hhafMarshallDiag0, Matrix.diagonal_mul_diagonal]
  have h1 : (fun σ : hhafConfig0 L => (marshallSignS (ringSublattice L) σ.1.1).re *
      (marshallSignS (ringSublattice L) σ.1.1).re) = fun _ => 1 := by
    funext σ
    have h := congrArg Complex.re (marshallSignS_sq (ringSublattice L) σ.1.1)
    rwa [Complex.mul_re, marshallSignS_im, mul_zero, sub_zero, Complex.one_re] at h
  rw [h1, Matrix.diagonal_one]

/-- The balanced dressed block is the Marshall conjugate of the undressed real block:
`M₀ = Θ · M_real₀ · Θ`. -/
theorem hhafDressedMatrix0_eq_conj (L : ℕ) :
    hhafDressedMatrix0 L =
      hhafMarshallDiag0 L * hhafRestrictedMatrixReal0 L * hhafMarshallDiag0 L := by
  ext σ τ
  rw [hhafDressedMatrix0, Matrix.submatrix_apply, hhafDressedMatrix_eq, Matrix.mul_assoc,
    hhafMarshallDiag0, Matrix.diagonal_mul, Matrix.mul_diagonal, hhafRestrictedMatrixReal0,
    Matrix.submatrix_apply]
  ring

/-- **Unique balanced-sector ground state (undressed real form).**  Transferring the full
Perron–Frobenius data through the Marshall similarity `M₀ = Θ M_real₀ Θ`, the undressed real
restricted matrix on the balanced sector has a nonzero lowest eigenvector (`Θ` on the dressed Perron
vector), the same minimal eigenvalue, and a one-dimensional ground eigenspace. -/
theorem hhafRestrictedMatrixReal0_ground_finrank_le_one (L : ℕ) (hLeven : Even L) :
    ∃ (μ : ℝ) (w : hhafConfig0 L → ℝ), w ≠ 0 ∧
      (hhafRestrictedMatrixReal0 L).mulVec w = μ • w ∧
      (∀ (lam : ℝ) (u : hhafConfig0 L → ℝ), u ≠ 0 →
        (hhafRestrictedMatrixReal0 L).mulVec u = lam • u → μ ≤ lam) ∧
      Module.finrank ℝ
        (Module.End.eigenspace (Matrix.toLin' (hhafRestrictedMatrixReal0 L)) μ) ≤ 1 := by
  obtain ⟨μ, v, hvpos, hMv, hmin, hfin⟩ := hhafDressedMatrix0_ground_finrank_le_one L hLeven
  have hΘsq : ∀ u, (hhafMarshallDiag0 L).mulVec ((hhafMarshallDiag0 L).mulVec u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, hhafMarshallDiag0_mul_self, Matrix.one_mulVec]
  -- `M_real₀ (Θ u) = Θ (M₀ u)` and the symmetric `M₀ (Θ u) = Θ (M_real₀ u)`.
  have hconj : ∀ u, (hhafRestrictedMatrixReal0 L).mulVec ((hhafMarshallDiag0 L).mulVec u) =
      (hhafMarshallDiag0 L).mulVec ((hhafDressedMatrix0 L).mulVec u) := fun u => by
    conv_rhs => rw [hhafDressedMatrix0_eq_conj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hΘsq]
  have hconj' : ∀ u, (hhafDressedMatrix0 L).mulVec ((hhafMarshallDiag0 L).mulVec u) =
      (hhafMarshallDiag0 L).mulVec ((hhafRestrictedMatrixReal0 L).mulVec u) := fun u => by
    conv_lhs => rw [hhafDressedMatrix0_eq_conj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hΘsq]
  have hΘinj : Function.Injective (hhafMarshallDiag0 L).mulVec := fun a b hab => by
    have := congrArg (hhafMarshallDiag0 L).mulVec hab; rwa [hΘsq, hΘsq] at this
  refine ⟨μ, (hhafMarshallDiag0 L).mulVec v, ?_, ?_, ?_, ?_⟩
  · intro h
    have hv0 : v = 0 := hΘinj (by rw [h, Matrix.mulVec_zero])
    obtain ⟨i⟩ := (inferInstance : Nonempty (hhafConfig0 L))
    exact absurd (hv0 ▸ hvpos i) (lt_irrefl 0)
  · rw [hconj, hMv, Matrix.mulVec_smul]
  · intro lam u hu hMu
    have hu' : (hhafMarshallDiag0 L).mulVec u ≠ 0 :=
      fun h => hu (hΘinj (by rw [h, Matrix.mulVec_zero]))
    refine hmin lam ((hhafMarshallDiag0 L).mulVec u) hu' ?_
    rw [hconj', hMu, Matrix.mulVec_smul]
  · rw [← matrix_similar_eigenspace_finrank_eq (hhafMarshallDiag0_mul_self L)
      (hhafMarshallDiag0_mul_self L) (hhafDressedMatrix0_eq_conj L) μ]
    exact hfin

/-! ## The Néel configuration as a balanced ground-energy witness -/

/-- The **Néel configuration**: spin `+1` on even sites (`σ_x = 0`), `−1` on odd sites (`σ_x = 2`) —
the maximally antiferromagnetic balanced configuration. -/
def hhafNeel (L : ℕ) : Fin L → Fin 3 := fun x => if x.val % 2 = 0 then 0 else 2

/-- Every site of the Néel configuration carries a `±` spin. -/
theorem hhafNeel_isPM (L : ℕ) (x : Fin L) : hhafNeel L x ≠ 1 := by
  rw [hhafNeel]; split <;> decide

/-- If `y` is not the cyclic successor of `x`, then the successor lies in the open arc `(x, y)`. -/
theorem inCyclicOpen_succ_mem_of_ne {L : ℕ} (hL : 2 ≤ L) {x y : Fin L} (hxy : x ≠ y)
    (hne : y.val ≠ (x.val + 1) % L) :
    InCyclicOpen x y ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ := by
  have hxv := x.isLt; have hyv := y.isLt
  have hxyv : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  simp only [InCyclicOpen]
  rcases Nat.lt_or_ge (x.val + 1) L with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hne ⊢; split_ifs <;> omega
  · have heq : x.val + 1 = L := by omega
    rw [heq, Nat.mod_self] at hne ⊢; split_ifs <;> omega

/-- **The Néel configuration is hidden-AFM** (on an even ring): all sites carry `±` spins, so every
`IsNextPM` pair is cyclically adjacent, and adjacent sites have opposite parity hence opposite sign.
-/
theorem hhafNeel_isHiddenAFM (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L) :
    IsHiddenAFMConfig (hhafNeel L) := by
  intro x y hxy
  obtain ⟨hne, _, _, harc⟩ := hxy
  have h2 : (2 : ℕ) ∣ L := hLeven.two_dvd
  have hsucc : y.val = (x.val + 1) % L := by
    by_contra hns
    exact hhafNeel_isPM L _ (harc _ (inCyclicOpen_succ_mem_of_ne hL hne hns))
  have hpar : x.val % 2 ≠ y.val % 2 := by
    have hm : y.val % 2 = (x.val + 1) % 2 := by rw [hsucc]; exact Nat.mod_mod_of_dvd _ h2
    omega
  rw [hhafNeel, hhafNeel]
  split_ifs <;> first | rfl | (exfalso; omega) | decide

/-- Every site of the Néel configuration is a `±` spin, so its `±`-count is `L`. -/
theorem hhafNeel_pmCount (L : ℕ) :
    (Finset.univ.filter (fun x => hhafNeel L x ≠ 1)).card = L := by
  rw [Finset.filter_true_of_mem (fun x _ => hhafNeel_isPM L x), Finset.card_univ, Fintype.card_fin]

/-- The Néel configuration as a balanced (even-`pmCount`) hidden-AFM configuration. -/
def hhafNeelConfig0 (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L) : hhafConfig0 L :=
  ⟨⟨hhafNeel L, hhafNeel_isHiddenAFM L hLeven hL⟩, by
    have h : pmCount L ⟨hhafNeel L, hhafNeel_isHiddenAFM L hLeven hL⟩ = L := hhafNeel_pmCount L
    rw [h]; exact hLeven⟩

/-- The **Néel diagonal energy is `−L`**: every nearest-neighbour bond is antiferromagnetic
(`(+1)(−1) = −1`), so the sum over the `L` bonds is `−L`. -/
theorem hhafNeel_diag (L : ℕ) (hL : 2 ≤ L) (hLeven : Even L) :
    (hhafRestrictedMatrix L ⟨hhafNeel L, hhafNeel_isHiddenAFM L hLeven hL⟩
      ⟨hhafNeel L, hhafNeel_isHiddenAFM L hLeven hL⟩) = ((-(L : ℝ) : ℝ) : ℂ) := by
  rw [hhaf_diag_eq_succ_sum L hL]
  have h2 : (2 : ℕ) ∣ L := hLeven.two_dvd
  have hterm : ∀ x : Fin L, ((1 : ℂ) - ((hhafNeel L x).val : ℂ)) *
      (1 - ((hhafNeel L ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩).val : ℂ)) = -1 := by
    intro x
    have hpar : x.val % 2 ≠ ((x.val + 1) % L) % 2 := by
      have hm : ((x.val + 1) % L) % 2 = (x.val + 1) % 2 := Nat.mod_mod_of_dvd _ h2
      omega
    simp only [hhafNeel]
    split_ifs <;> first | (exfalso; omega) | (norm_num [Fin.val])
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast; ring

/-- **The global ground energy is at most `−L`** (Rayleigh quotient at the Néel configuration): the
balanced sector contains the maximally-antiferromagnetic Néel state of energy `−L`. -/
theorem hhafMinEnergy_le_neg_L (L : ℕ) (hL : 2 ≤ L) (hLeven : Even L) :
    hhafMinEnergy L ≤ -(L : ℝ) := by
  have h := hhafMinEnergy_le_diag L ⟨hhafNeel L, hhafNeel_isHiddenAFM L hLeven hL⟩
  rw [hhafNeel_diag L hL hLeven] at h
  simpa using h

/-! ## The magnetization-`±1` sectors and their energy lower bound -/

/-- A configuration with a single `±` spin has **vanishing diagonal energy**: every bond has at
least one `0`-spin endpoint (only one site is `±`), so each Ising term vanishes. -/
theorem hhaf_diag_eq_zero_of_pmCount_one (L : ℕ) (hL : 2 ≤ L) (σ : hhafConfig L)
    (hpm : pmCount L σ = 1) : (hhafRestrictedMatrix L) σ σ = 0 := by
  rw [hhaf_diag_eq_succ_sum L hL]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  -- at least one of `x`, `x+1` is a `0`-spin (`σ = 1`), since only one site is `±`
  set s := Finset.univ.filter (fun z => σ.1 z ≠ 1) with hs
  have hscard : s.card = 1 := hpm
  have hzero : σ.1 x = 1 ∨ σ.1 ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ = 1 := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hx, hx1⟩ := hcon
    have hxs : x ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hx1s : (⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L) ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1⟩
    have hne : x ≠ (⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L) := by
      intro h
      have hv : x.val = (x.val + 1) % L := congrArg Fin.val h
      have hxlt := x.isLt
      rcases Nat.lt_or_ge (x.val + 1) L with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hv; omega
      · rw [show x.val + 1 = L by omega, Nat.mod_self] at hv; omega
    have : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨x, hxs, _, hx1s, hne⟩
    omega
  rcases hzero with h | h <;> rw [h] <;> simp

/-- **Spin-1 ladder amplitude bound** (raising/lowering): the off-diagonal `Ŝ_x·Ŝ_y` matrix element
on a raise-at-`x`/lower-at-`y` step has real part of magnitude at most `1` (each `√` factor is at
most `√2` for `N = 2`). -/
theorem spinSDot_re_abs_le_one_raising_lowering {L : ℕ} {x y : Fin L} (hxy : x ≠ y)
    {σ' σ : Fin L → Fin 3} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val) (hy : (σ y).val + 1 = (σ' y).val) :
    |((spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ' σ).re| ≤ 1 := by
  have hA : ((σ x).val : ℝ) * ((2 : ℝ) - (σ x).val + 1) ≤ 2 := by
    have := (σ x).isLt; interval_cases hc : (σ x).val <;> norm_num
  have hB : ((2 : ℝ) - (σ y).val) * ((σ y).val + 1) ≤ 2 := by
    have := (σ y).isLt; interval_cases hc : (σ y).val <;> norm_num
  have hsqrtA : Real.sqrt (((σ x).val : ℝ) * ((2 : ℝ) - (σ x).val + 1)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hA
  have hsqrtB : Real.sqrt (((2 : ℝ) - (σ y).val) * ((σ y).val + 1)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hB
  have hre : ((spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ' σ).re =
      (1 / 2) * (Real.sqrt (((σ x).val : ℝ) * ((2 : ℝ) - (σ x).val + 1)) *
        Real.sqrt (((2 : ℝ) - (σ y).val) * ((σ y).val + 1))) := by
    rw [spinSDot_apply_eq_raising_lowering_explicit hxy 2 h hx hy]
    simp [Complex.mul_re]
  rw [hre, abs_of_nonneg (by positivity)]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (((σ x).val : ℝ) * ((2 : ℝ) - (σ x).val + 1)),
    Real.sqrt_nonneg (((2 : ℝ) - (σ y).val) * ((σ y).val + 1)), hsqrtA, hsqrtB]

/-- **Spin-1 ladder amplitude bound** (lowering/raising): the off-diagonal `Ŝ_x·Ŝ_y` matrix element
on a lower-at-`x`/raise-at-`y` step has real part of magnitude at most `1`. -/
theorem spinSDot_re_abs_le_one_lowering_raising {L : ℕ} {x y : Fin L} (hxy : x ≠ y)
    {σ' σ : Fin L → Fin 3} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) (hy : (σ' y).val + 1 = (σ y).val) :
    |((spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ' σ).re| ≤ 1 := by
  have hA : ((2 : ℝ) - (σ x).val) * ((σ x).val + 1) ≤ 2 := by
    have := (σ x).isLt; interval_cases hc : (σ x).val <;> norm_num
  have hB : ((σ y).val : ℝ) * ((2 : ℝ) - (σ y).val + 1) ≤ 2 := by
    have := (σ y).isLt; interval_cases hc : (σ y).val <;> norm_num
  have hsqrtA : Real.sqrt (((2 : ℝ) - (σ x).val) * ((σ x).val + 1)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hA
  have hsqrtB : Real.sqrt (((σ y).val : ℝ) * ((2 : ℝ) - (σ y).val + 1)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hB
  have hre : ((spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ' σ).re =
      (1 / 2) * (Real.sqrt (((2 : ℝ) - (σ x).val) * ((σ x).val + 1)) *
        Real.sqrt (((σ y).val : ℝ) * ((2 : ℝ) - (σ y).val + 1))) := by
    rw [spinSDot_apply_eq_lowering_raising_explicit hxy 2 h hx hy]
    simp [Complex.mul_re]
  rw [hre, abs_of_nonneg (by positivity)]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (((2 : ℝ) - (σ x).val) * ((σ x).val + 1)),
    Real.sqrt_nonneg (((σ y).val : ℝ) * ((2 : ℝ) - (σ y).val + 1)), hsqrtA, hsqrtB]

end LatticeSystem.Quantum
