import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrder
import LatticeSystem.Math.PerronFrobeniusSymmetric
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import Mathlib.LinearAlgebra.Matrix.Gershgorin

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

/-- **Per-step dressed off-diagonal bound**: for two hidden-AFM configurations related by a single
ladder move on the bond `{x, y}`, the dressed restricted matrix entry has magnitude at most the
symmetrized coupling `ringCouplingSym` there (the Marshall signs are `±1`, the Heisenberg element is
`ringCouplingSym · spinSDot`, and the spin-`1` ladder amplitude is `≤ 1`). -/
theorem hhafDressedMatrix_abs_le_ringCouplingSym {L : ℕ} {σ τ : hhafConfig L} {x y : Fin L}
    (hxy : x ≠ y)
    (hsh : ((τ.1 x).val + 1 = (σ.1 x).val ∧ (σ.1 y).val + 1 = (τ.1 y).val) ∨
      ((σ.1 x).val + 1 = (τ.1 x).val ∧ (τ.1 y).val + 1 = (σ.1 y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ.1 k = τ.1 k) :
    |hhafDressedMatrix L σ τ| ≤ (ringCouplingSym L x y).re := by
  -- The Heisenberg entry is `ringCouplingSym · spinSDot`.
  have hheis : (hhafRestrictedMatrix L) σ τ =
      (ringCoupling L x y + ringCoupling L y x) *
        (spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ.1 τ.1 := by
    rw [hhafRestrictedMatrix, Matrix.submatrix_apply, afmHeisenbergChainHamiltonianS]
    exact heisenbergHamiltonianS_apply_of_raiseLowerStepS_witness (ringCoupling L) 2
      (G := ⊤) ((SimpleGraph.top_adj x y).mpr hxy) hsh hagree
  have hsym_im : (ringCoupling L x y + ringCoupling L y x).im = 0 := by
    simp only [ringCoupling]; split <;> split <;> simp
  have hsd : |((spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ.1 τ.1).re| ≤ 1 := by
    rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact spinSDot_re_abs_le_one_lowering_raising hxy hagree h1 h2
    · exact spinSDot_re_abs_le_one_raising_lowering hxy hagree h1 h2
  have hsym_nonneg : 0 ≤ (ringCoupling L x y + ringCoupling L y x).re := by
    simp only [ringCoupling]; split <;> split <;> norm_num
  rw [hhafDressedMatrix_eq, hhafRestrictedMatrixReal, hheis]
  rw [Complex.mul_re, hsym_im, zero_mul, sub_zero]
  rw [abs_mul, abs_mul]
  have hmσ : |(marshallSignS (ringSublattice L) σ.1).re| = 1 := by
    have h := congrArg Complex.re (marshallSignS_sq (ringSublattice L) σ.1)
    rw [Complex.mul_re, marshallSignS_im, mul_zero, sub_zero, Complex.one_re] at h
    rw [abs_eq (by norm_num : (0:ℝ) ≤ 1)]; rcases mul_self_eq_one_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmτ : |(marshallSignS (ringSublattice L) τ.1).re| = 1 := by
    have h := congrArg Complex.re (marshallSignS_sq (ringSublattice L) τ.1)
    rw [Complex.mul_re, marshallSignS_im, mul_zero, sub_zero, Complex.one_re] at h
    rw [abs_eq (by norm_num : (0:ℝ) ≤ 1)]; rcases mul_self_eq_one_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  rw [hmσ, hmτ, one_mul, one_mul, ringCouplingSym, abs_mul, abs_of_nonneg hsym_nonneg]
  calc (ringCoupling L x y + ringCoupling L y x).re *
        |((spinSDot x y 2 : ManyBodyOpS (Fin L) 2) σ.1 τ.1).re|
      ≤ (ringCoupling L x y + ringCoupling L y x).re * 1 :=
        mul_le_mul_of_nonneg_left hsd hsym_nonneg
    _ = (ringCoupling L x y + ringCoupling L y x).re := mul_one _

/-- The **dressed** diagonal also vanishes for a single-`±` configuration: dressing only multiplies
the entry by the real Marshall phases (`ε(σ).re²`), and the undressed diagonal is zero. -/
theorem hhafDressedMatrix_diag_eq_zero_of_pmCount_one (L : ℕ) (hL : 2 ≤ L) (σ : hhafConfig L)
    (hpm : pmCount L σ = 1) : hhafDressedMatrix L σ σ = 0 := by
  rw [hhafDressedMatrix_eq, hhafRestrictedMatrixReal,
    hhaf_diag_eq_zero_of_pmCount_one L hL σ hpm, Complex.zero_re, mul_zero]

/-- The **magnetization-`±1` sector**: hidden-AFM configurations with exactly one `±` spin
(`pmCount = 1`).  These span the total-`Sz = ±1` blocks of `H_HAF` and form a single-kink
tight-binding problem. -/
abbrev hhafConfigPM1 (L : ℕ) : Type := {σ : hhafConfig L // pmCount L σ = 1}

/-- The **dressed restricted matrix on the magnetization-`±1` sector** (the submatrix of
`hhafDressedMatrix` on `hhafConfigPM1`). -/
noncomputable def hhafDressedMatrixPM1 (L : ℕ) :
    Matrix (hhafConfigPM1 L) (hhafConfigPM1 L) ℝ :=
  (hhafDressedMatrix L).submatrix Subtype.val Subtype.val

/-- The magnetization-`±1` sector dressed matrix is symmetric. -/
theorem hhafDressedMatrixPM1_isSymm (L : ℕ) : (hhafDressedMatrixPM1 L).IsSymm :=
  (hhafDressedMatrix_isSymm L).submatrix Subtype.val

/-- The magnetization-`±1` sector dressed matrix has **vanishing diagonal** (single-`±` Ising
energy is zero). -/
theorem hhafDressedMatrixPM1_diag_eq_zero (L : ℕ) (hL : 2 ≤ L) (σ : hhafConfigPM1 L) :
    hhafDressedMatrixPM1 L σ σ = 0 := by
  rw [hhafDressedMatrixPM1, Matrix.submatrix_apply]
  exact hhafDressedMatrix_diag_eq_zero_of_pmCount_one L hL σ.1 σ.2

/-- A vanishing undressed entry gives a vanishing dressed entry (dressing multiplies by the real
Marshall phases). -/
theorem hhafDressedMatrix_eq_zero_of_restricted_zero {L : ℕ} {σ τ : hhafConfig L}
    (h : (hhafRestrictedMatrix L) σ τ = 0) : hhafDressedMatrix L σ τ = 0 := by
  rw [hhafDressedMatrix_eq, hhafRestrictedMatrixReal, h, Complex.zero_re, mul_zero]

/-- The **unique `±` site** of a single-`±` configuration (`pmCount = 1`).  Defined computably as
the minimum of the (singleton) support so that `Finset.image`/`Finset.sum_image` reductions over the
`±`-site map do not force an opaque `Classical.choose`. -/
def hhafPM1Site {L : ℕ} (σ : hhafConfigPM1 L) : Fin L :=
  (Finset.univ.filter (fun x => σ.1.1 x ≠ 1)).min' (by
    rw [← Finset.card_pos]
    have hc : (Finset.univ.filter (fun x => σ.1.1 x ≠ 1)).card = 1 := σ.2
    omega)

/-- The `±` site indeed carries a `±` spin. -/
theorem hhafPM1Site_mem {L : ℕ} (σ : hhafConfigPM1 L) : σ.1.1 (hhafPM1Site σ) ≠ 1 := by
  have h : hhafPM1Site σ ∈ Finset.univ.filter (fun x => σ.1.1 x ≠ 1) := by
    rw [hhafPM1Site]; exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp h).2

/-- A site carries the `±` spin of a single-`±` configuration iff it is `hhafPM1Site`. -/
theorem hhafPM1Site_spec {L : ℕ} (σ : hhafConfigPM1 L) (z : Fin L) :
    σ.1.1 z ≠ 1 ↔ z = hhafPM1Site σ := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp σ.2
  have hsite : hhafPM1Site σ ∈ Finset.univ.filter (fun x => σ.1.1 x ≠ 1) := Finset.min'_mem _ _
  rw [ha, Finset.mem_singleton] at hsite
  constructor
  · intro hz
    have : z ∈ Finset.univ.filter (fun x => σ.1.1 x ≠ 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
    rw [ha, Finset.mem_singleton] at this
    rw [this, hsite]
  · intro hz; rw [hz]; exact hhafPM1Site_mem σ

/-- Off the `±` site, a single-`±` configuration is `1`. -/
theorem hhafPM1_eq_one_of_ne {L : ℕ} (σ : hhafConfigPM1 L) {z : Fin L}
    (hz : z ≠ hhafPM1Site σ) : σ.1.1 z = 1 := by
  by_contra h; exact hz ((hhafPM1Site_spec σ z).mp h)

/-- The `±` value at the `±` site is `0` or `2`. -/
theorem hhafPM1_site_val {L : ℕ} (σ : hhafConfigPM1 L) :
    (σ.1.1 (hhafPM1Site σ)).val = 0 ∨ (σ.1.1 (hhafPM1Site σ)).val = 2 := by
  have h : σ.1.1 (hhafPM1Site σ) ≠ 1 := (hhafPM1Site_spec σ (hhafPM1Site σ)).mpr rfl
  have := (σ.1.1 (hhafPM1Site σ)).isLt
  omega

/-- **Coupling characterization for the single-`±` sector.**  Two distinct single-`±`
configurations with a nonzero (undressed) matrix element differ at exactly their two `±` sites,
agree elsewhere, share their `±` value, and one is the other with the `±` spin slid to the new site
(`slidePM`). -/
theorem hhafPM1_coupling_imp {L : ℕ} (σ τ : hhafConfigPM1 L) (hne : τ ≠ σ)
    (hnz : (hhafRestrictedMatrix L) σ.1 τ.1 ≠ 0) :
    hhafPM1Site σ ≠ hhafPM1Site τ ∧
      (∀ k, k ≠ hhafPM1Site σ → k ≠ hhafPM1Site τ → σ.1.1 k = τ.1.1 k) ∧
      (((τ.1.1 (hhafPM1Site σ)).val + 1 = (σ.1.1 (hhafPM1Site σ)).val ∧
          (σ.1.1 (hhafPM1Site τ)).val + 1 = (τ.1.1 (hhafPM1Site τ)).val) ∨
        ((σ.1.1 (hhafPM1Site σ)).val + 1 = (τ.1.1 (hhafPM1Site σ)).val ∧
          (τ.1.1 (hhafPM1Site τ)).val + 1 = (σ.1.1 (hhafPM1Site τ)).val)) ∧
      τ.1.1 = slidePM σ.1.1 (hhafPM1Site σ) (hhafPM1Site τ) := by
  set s := hhafPM1Site σ with hsdef
  set t := hhafPM1Site τ with htdef
  -- entries are the Heisenberg matrix element
  have hH : (heisenbergHamiltonianS (ringCoupling L) 2) σ.1.1 τ.1.1 ≠ 0 := by
    rwa [hhafRestrictedMatrix, Matrix.submatrix_apply, afmHeisenbergChainHamiltonianS] at hnz
  -- agreement off `{s, t}`
  have hagree : ∀ k, k ≠ s → k ≠ t → σ.1.1 k = τ.1.1 k := fun k hks hkt => by
    rw [hhafPM1_eq_one_of_ne σ hks, hhafPM1_eq_one_of_ne τ hkt]
  -- `s ≠ t`
  have hst : s ≠ t := by
    intro h
    -- then `σ`, `τ` agree off the single site `s`
    have hagree' : ∀ k, k ≠ s → σ.1.1 k = τ.1.1 k := fun k hks =>
      hagree k hks (h ▸ hks)
    by_cases hval : σ.1.1 s = τ.1.1 s
    · exact hne (Subtype.ext (Subtype.ext (funext fun k => by
        by_cases hks : k = s
        · rw [hks]; exact hval.symm
        · exact (hagree' k hks).symm)))
    · exact hH (heisenbergHamiltonianS_apply_eq_zero_of_one_site_diff (ringCoupling L) 2
        (z := s) hagree' hval)
  -- value match via magnetization conservation
  have hmag : magSumS σ.1.1 = magSumS τ.1.1 := by
    by_contra hm
    exact hH (heisenbergHamiltonianS_apply_eq_zero_of_mag_ne (ringCoupling L) 2
      (fun h => hm ((magEigenvalueS_eq_iff τ.1.1 σ.1.1).mp h).symm))
  have hσt : σ.1.1 t = 1 := hhafPM1_eq_one_of_ne σ (Ne.symm hst)
  have hτs : τ.1.1 s = 1 := hhafPM1_eq_one_of_ne τ hst
  -- split the magnetization sum at `s` and `t`
  have hvalsum : (σ.1.1 s).val + (σ.1.1 t).val = (τ.1.1 s).val + (τ.1.1 t).val := by
    have hsplit : ∀ f : Fin L → Fin 3, magSumS f =
        (f s).val + ((f t).val + ∑ x ∈ (Finset.univ.erase s).erase t, (f x).val) := fun f => by
      rw [magSumS, ← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hst, Finset.mem_univ t⟩)]
    have hrest : (∑ x ∈ (Finset.univ.erase s).erase t, (σ.1.1 x).val) =
        ∑ x ∈ (Finset.univ.erase s).erase t, (τ.1.1 x).val :=
      Finset.sum_congr rfl fun x hx => by
        rw [hagree x (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
          (Finset.mem_erase.mp hx).1]
    have hms := hsplit σ.1.1
    have hmt := hsplit τ.1.1
    omega
  have hτsv : (τ.1.1 s).val = 1 := by simp [hτs]
  have hσtv : (σ.1.1 t).val = 1 := by simp [hσt]
  have hsval : (σ.1.1 s).val = (τ.1.1 t).val := by omega
  refine ⟨hst, hagree, ?_, ?_⟩
  · -- shift structure from the `±` value `0` or `2`
    rcases hhafPM1_site_val σ with h0 | h2
    · rw [← hsdef] at h0; right; constructor <;> omega
    · rw [← hsdef] at h2; left; constructor <;> omega
  · -- `τ = slidePM σ s t`
    funext k
    rw [slidePM_apply σ.1.1 hst k]
    by_cases hkt : k = t
    · rw [if_pos hkt, hkt]; exact Fin.eq_of_val_eq hsval.symm
    · rw [if_neg hkt]
      by_cases hks : k = s
      · rw [if_pos hks, hks]; exact hτs
      · rw [if_neg hks]; exact (hagree k hks hkt).symm

/-- **Single-`±` row bound** (per entry): a nonzero off-diagonal entry of the single-`±` block is
bounded by the symmetrized coupling between the two `±` sites. -/
theorem hhafDressedMatrixPM1_offdiag_le {L : ℕ} (σ τ : hhafConfigPM1 L) (hne : τ ≠ σ)
    (hnz : (hhafRestrictedMatrix L) σ.1 τ.1 ≠ 0) :
    ‖hhafDressedMatrixPM1 L σ τ‖ ≤ (ringCouplingSym L (hhafPM1Site σ) (hhafPM1Site τ)).re := by
  obtain ⟨hst, hagree, hsh, _⟩ := hhafPM1_coupling_imp σ τ hne hnz
  rw [hhafDressedMatrixPM1, Matrix.submatrix_apply, Real.norm_eq_abs]
  exact hhafDressedMatrix_abs_le_ringCouplingSym hst hsh hagree

/-- The `±`-site map is **injective on the coupling support**: two distinct configurations both
coupling to `σ` and sharing a `±` site are equal (both are the unique slide of `σ` to that site). -/
theorem hhafPM1Site_injOn_support {L : ℕ} (σ : hhafConfigPM1 L) :
    Set.InjOn (hhafPM1Site)
      {τ : hhafConfigPM1 L | τ ≠ σ ∧ (hhafRestrictedMatrix L) σ.1 τ.1 ≠ 0} := by
  intro τ hτ τ' hτ' heq
  obtain ⟨_, _, _, hslide⟩ := hhafPM1_coupling_imp σ τ hτ.1 hτ.2
  obtain ⟨_, _, _, hslide'⟩ := hhafPM1_coupling_imp σ τ' hτ'.1 hτ'.2
  exact Subtype.ext (Subtype.ext (hslide.trans (heq ▸ hslide'.symm)))

/-- A nonnegative function composed with a map injective on a finite index set sums to at most the
total over the codomain.  Stated over abstract types so that `Finset.image`/`Finset.sum_image`
reductions never force the (astronomically large) `Finset.univ` of a concrete configuration type. -/
theorem sum_comp_le_sum_univ_of_injOn {α β : Type*} [Fintype β]
    (s : Finset α) (g : α → β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b)
    (hinj : Set.InjOn g (s : Set α)) :
    ∑ a ∈ s, f (g a) ≤ ∑ b, f b := by
  classical
  rw [← Finset.sum_image
    (fun x hx y hy h => hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)

/-- **Row-sum identity** for the symmetrized ring coupling: every site has exactly two incident
directed ring bonds, so the real part of the row sum is `2` (the Gershgorin radius). -/
theorem ringCouplingSym_re_row_sum (L : ℕ) (hL : 1 ≤ L) (s : Fin L) :
    ∑ t : Fin L, (ringCouplingSym L s t).re = 2 := by
  have hsucc : (⟨(s.val + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L).val = (s.val + 1) % L := rfl
  have hsum1 : ∑ t : Fin L, (ringCoupling L s t).re = 1 := by
    rw [Finset.sum_eq_single (⟨(s.val + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L)]
    · rw [ringCoupling]; simp
    · intro t _ hne
      rw [ringCoupling]
      have : t.val ≠ (s.val + 1) % L := fun h => hne (Fin.ext (h.trans hsucc.symm))
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsucc_inj : ∀ a b : ℕ, a < L → b < L → (a + 1) % L = (b + 1) % L → a = b := by
    intro a b ha hb hab
    rcases Nat.lt_or_ge (a + 1) L with ha1 | ha1 <;> rcases Nat.lt_or_ge (b + 1) L with hb1 | hb1
    · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at hab; omega
    · rw [Nat.mod_eq_of_lt ha1, show b + 1 = L by omega, Nat.mod_self] at hab; omega
    · rw [show a + 1 = L by omega, Nat.mod_self, Nat.mod_eq_of_lt hb1] at hab; omega
    · omega
  have hsum2 : ∑ t : Fin L, (ringCoupling L t s).re = 1 := by
    set p : Fin L := ⟨(s.val + L - 1) % L, Nat.mod_lt _ (by omega)⟩ with hp
    have hps : (p.val + 1) % L = s.val := by
      have hsL := s.isLt
      rcases Nat.eq_zero_or_pos s.val with h0 | h0
      · simp only [hp, h0, Nat.mod_eq_of_lt (show 0 + L - 1 < L by omega)]
        rw [show 0 + L - 1 + 1 = L by omega, Nat.mod_self]
      · simp only [hp, show s.val + L - 1 = (s.val - 1) + L by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show s.val - 1 < L by omega), show s.val - 1 + 1 = s.val by omega,
          Nat.mod_eq_of_lt hsL]
    rw [Finset.sum_eq_single p]
    · rw [ringCoupling]; simp [hps.symm]
    · intro t _ hne
      rw [ringCoupling]
      have : s.val ≠ (t.val + 1) % L := by
        intro h
        exact hne (Fin.ext (hsucc_inj t.val p.val t.isLt p.isLt (h ▸ hps).symm))
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∑ t : Fin L, (ringCouplingSym L s t).re
      = ∑ t : Fin L, ((ringCoupling L s t).re + (ringCoupling L t s).re) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ringCouplingSym, Complex.add_re]
    _ = (∑ t : Fin L, (ringCoupling L s t).re) + ∑ t : Fin L, (ringCoupling L t s).re :=
        Finset.sum_add_distrib
    _ = 2 := by rw [hsum1, hsum2]; norm_num

/-- **Magnetization-`±1` sector Gershgorin radius**: each single-`±` row has off-diagonal `ℓ¹`-norm
at most `2`.  The support of a row is the `≤ 2` adjacent slides of the `±` spin, each bounded by the
incident coupling, and the `±`-site map is injective on the support, so the sum collapses to the
ring-coupling row sum `2`. -/
theorem hhafDressedMatrixPM1_rowSum_le_two {L : ℕ} (hL : 1 ≤ L) (σ : hhafConfigPM1 L) :
    ∑ τ ∈ Finset.univ.erase σ, ‖hhafDressedMatrixPM1 L σ τ‖ ≤ 2 := by
  classical
  set S := (Finset.univ.erase σ).filter
    (fun τ => (hhafRestrictedMatrix L) σ.1 τ.1 ≠ 0) with hSdef
  -- restrict the sum to the coupling support
  have hsupp : ∑ τ ∈ Finset.univ.erase σ, ‖hhafDressedMatrixPM1 L σ τ‖ =
      ∑ τ ∈ S, ‖hhafDressedMatrixPM1 L σ τ‖ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro τ hτ hτS
    rw [Finset.mem_filter, not_and] at hτS
    have h0 : (hhafRestrictedMatrix L) σ.1 τ.1 = 0 := by
      by_contra h; exact hτS hτ h
    have hd0 : hhafDressedMatrixPM1 L σ τ = 0 :=
      hhafDressedMatrix_eq_zero_of_restricted_zero h0
    rw [hd0, norm_zero]
  rw [hsupp]
  -- per-entry bound, then reindex by the injective `±`-site map
  have hinj : Set.InjOn hhafPM1Site (S : Set (hhafConfigPM1 L)) := by
    refine (hhafPM1Site_injOn_support σ).mono ?_
    intro τ hτ
    rw [hSdef, Finset.coe_filter] at hτ
    exact ⟨Finset.mem_erase.mp hτ.1 |>.1, hτ.2⟩
  calc ∑ τ ∈ S, ‖hhafDressedMatrixPM1 L σ τ‖
      ≤ ∑ τ ∈ S, (ringCouplingSym L (hhafPM1Site σ) (hhafPM1Site τ)).re := by
        refine Finset.sum_le_sum fun τ hτ => ?_
        rw [hSdef, Finset.mem_filter] at hτ
        exact hhafDressedMatrixPM1_offdiag_le σ τ (Finset.mem_erase.mp hτ.1).1 hτ.2
    _ ≤ ∑ t : Fin L, (ringCouplingSym L (hhafPM1Site σ) t).re :=
        sum_comp_le_sum_univ_of_injOn S hhafPM1Site _
          (fun t => ringCouplingSym_re_nonneg L _ t) hinj
    _ = 2 := ringCouplingSym_re_row_sum L hL _

/-- **Magnetization-`±1` sector minimum energy `≥ −2`** (Gershgorin).  Every eigenvalue of the
single-`±` dressed block lies in the disc of centre `0` (vanishing diagonal) and radius `2` (the
ring-coupling row sum), so the lowest eigenvalue is at least `−2`.  This is the single-kink
tight-binding lower bound that places the `Sz = ±1` sectors strictly above the balanced ground
energy. -/
theorem hhafDressedMatrixPM1_eigenvalue_ge {L : ℕ} (hL : 2 ≤ L) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (hhafDressedMatrixPM1 L)) μ) :
    -2 ≤ μ := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  rw [Metric.mem_closedBall, hhafDressedMatrixPM1_diag_eq_zero L hL k, Real.dist_eq, sub_zero] at hk
  have hrow : ∑ j ∈ Finset.univ.erase k, ‖hhafDressedMatrixPM1 L k j‖ ≤ 2 :=
    hhafDressedMatrixPM1_rowSum_le_two (by omega) k
  have : |μ| ≤ 2 := le_trans hk hrow
  rw [abs_le] at this
  linarith [this.1]

/-! ## The balanced ground energy is strictly below `−L` -/

/-- **Strict row inequality** for a real matrix with a strictly positive vector, nonpositive
off-diagonal row entries, and at least one strictly negative off-diagonal entry: the weighted row
sum is strictly below the diagonal contribution.  (The Perron–Frobenius row contradiction used to
make the balanced ground energy strict.) -/
theorem row_sum_mul_lt_diag_mul_of_offdiag_nonpos_exists_neg
    {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℝ} {v : ι → ℝ} {i : ι}
    (hv : ∀ j, 0 < v j) (hoff : ∀ j, j ≠ i → M i j ≤ 0)
    (hex : ∃ j, j ≠ i ∧ M i j < 0) :
    ∑ j, M i j * v j < M i i * v i := by
  classical
  obtain ⟨k, hk_ne, hk_neg⟩ := hex
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hkmem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hk_ne, Finset.mem_univ k⟩
  have hrest : ∑ j ∈ Finset.univ.erase i, M i j * v j < 0 := by
    rw [← Finset.add_sum_erase _ _ hkmem]
    have hkterm : M i k * v k < 0 := mul_neg_of_neg_of_pos hk_neg (hv k)
    have hrest2 : ∑ j ∈ (Finset.univ.erase i).erase k, M i j * v j ≤ 0 :=
      Finset.sum_nonpos fun j hj => mul_nonpos_iff.mpr (Or.inr
        ⟨hoff j (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj)).1, (hv j).le⟩)
    linarith
  linarith

/-- Off-diagonal entries of the balanced-sector dressed block are nonpositive. -/
theorem hhafDressedMatrix0_offdiag_nonpos (L : ℕ) (hLeven : Even L) {σ τ : hhafConfig0 L}
    (hne : σ ≠ τ) : hhafDressedMatrix0 L σ τ ≤ 0 := by
  rw [hhafDressedMatrix0, Matrix.submatrix_apply]
  exact hhafDressedMatrix_offdiag_nonpos L hLeven (fun h => hne (Subtype.ext h))

/-- The balanced-sector dressed diagonal at the Néel configuration is `−L`. -/
theorem hhafDressedMatrix0_Neel_diag (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L) :
    hhafDressedMatrix0 L (hhafNeelConfig0 L hLeven hL) (hhafNeelConfig0 L hLeven hL) =
      -(L : ℝ) := by
  rw [hhafDressedMatrix0, Matrix.submatrix_apply, hhafDressedMatrix_diag_eq,
    hhafRestrictedMatrixReal]
  simp only [hhafNeelConfig0]
  rw [hhafNeel_diag L hL hLeven]
  simp

/-- The Néel configuration has a **strictly-negative** balanced ladder neighbour: annihilating the
adjacent opposite-`±` pair at sites `0, 1` is a single HAF step, so the dressed entry there is
`< 0`. -/
theorem hhafNeel_step_neighbor (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L) :
    ∃ τ : hhafConfig0 L, τ ≠ hhafNeelConfig0 L hLeven hL ∧
      hhafDressedMatrix0 L (hhafNeelConfig0 L hLeven hL) τ < 0 := by
  set a : Fin L := ⟨0, by omega⟩ with ha_def
  set b : Fin L := ⟨1, by omega⟩ with hb_def
  have hab : a ≠ b := by
    rw [ha_def, hb_def]; exact fun h => by simpa using congrArg Fin.val h
  have hbv : b.val = (a.val + 1) % L := by
    rw [ha_def, hb_def]; simp [Nat.mod_eq_of_lt (show 1 < L by omega)]
  have hva : hhafNeel L a = 0 := by rw [ha_def, hhafNeel]; simp
  have hvb : hhafNeel L b = 2 := by
    rw [hb_def, hhafNeel]; norm_num [Nat.mod_eq_of_lt (show 1 < L by omega)]
  have hav : hhafNeel L a ≠ 1 := by rw [hva]; decide
  have hbv1 : hhafNeel L b ≠ 1 := by rw [hvb]; decide
  have hne : hhafNeel L a ≠ hhafNeel L b := by rw [hva, hvb]; decide
  -- the annihilated config and its membership in the balanced sector
  have hneelHAF := hhafNeel_isHiddenAFM L hLeven hL
  set τ1 : hhafConfig L :=
    ⟨annihPM (hhafNeel L) a b, annihPM_isHiddenAFM hneelHAF hab hbv hav hbv1 hne⟩ with hτ1
  have hτ1pc : pmCount L τ1 = L - 2 := by
    rw [hτ1, pmCount, annihPM_pmCount_eq (hhafNeel L) hab hav hbv1]
    have : (Finset.univ.filter (fun x => hhafNeel L x ≠ 1)).card = L := hhafNeel_pmCount L
    rw [this]
  have hτ1even : Even (pmCount L τ1) := by
    rw [hτ1pc]; obtain ⟨m, hm⟩ := hLeven; exact ⟨m - 1, by omega⟩
  refine ⟨⟨τ1, hτ1even⟩, ?_, ?_⟩
  · -- the neighbour differs from Néel at site `a` (Néel `0`, annihilated `1`)
    intro h
    have hval : annihPM (hhafNeel L) a b a = hhafNeel L a := congrFun (congrArg Subtype.val
      (congrArg Subtype.val h)) a
    rw [annihPM_apply (hhafNeel L) hab a, if_pos (Or.inl rfl)] at hval
    exact hav hval.symm
  · -- the step gives a strictly negative dressed entry
    have hstep : RaiseLowerStepSHhaf L (hhafNeelConfig0 L hLeven hL).1 τ1 :=
      annihPM_isRaiseLowerStepSHhaf ⟨hhafNeel L, hneelHAF⟩ hab hbv hav hbv1 hne
    have hpos := hhafShifted_pos_of_stepHhaf L hLeven (c := 0) hstep
    have hne1 : τ1 ≠ (hhafNeelConfig0 L hLeven hL).1 := by
      intro h
      have hval : annihPM (hhafNeel L) a b a = hhafNeel L a :=
        congrFun (congrArg Subtype.val h) a
      rw [annihPM_apply (hhafNeel L) hab a, if_pos (Or.inl rfl)] at hval
      exact hav hval.symm
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne1, smul_zero, zero_sub,
      neg_pos] at hpos
    -- `hpos : hhafDressedMatrix L τ1 Néel < 0`; symmetrize and restrict to the block
    have heq : hhafDressedMatrix0 L (hhafNeelConfig0 L hLeven hL) ⟨τ1, hτ1even⟩ =
        hhafDressedMatrix L τ1 (hhafNeelConfig0 L hLeven hL).1 := by
      rw [hhafDressedMatrix0, Matrix.submatrix_apply]
      exact (hhafDressedMatrix_isSymm L).apply τ1 (hhafNeelConfig0 L hLeven hL).1
    rw [heq]; exact hpos

/-- **The balanced ground energy is strictly below `−L`.**  The Perron–Frobenius lowest eigenvector
`v > 0` paired with the Néel row gives `μ · v(Néel) = −L · v(Néel) + Σ_{τ≠Néel} M₀(Néel,τ) v(τ)`;
every off-diagonal term is `≤ 0` and at least one (the annihilation neighbour) is `< 0`, so
`μ · v(Néel) < −L · v(Néel)`, hence `μ < −L`.  Since `−L ≤ −2`, the balanced sector lies *strictly*
below the magnetization-`±1` sectors (`≥ −2`), with no `L = 2` tie. -/
theorem hhafDressedMatrix0_ground_lt_neg_L (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L)
    {μ : ℝ} {v : hhafConfig0 L → ℝ} (hposv : ∀ i, 0 < v i)
    (heig : (hhafDressedMatrix0 L).mulVec v = μ • v) :
    μ < -(L : ℝ) := by
  set n := hhafNeelConfig0 L hLeven hL with hn
  obtain ⟨τ, hτ_ne, hτ_neg⟩ := hhafNeel_step_neighbor L hLeven hL
  -- the eigenvalue equation read at the Néel row
  have hrow : ∑ j, hhafDressedMatrix0 L n j * v j = μ * v n := by
    have hc := congrFun heig n
    rw [Pi.smul_apply, smul_eq_mul] at hc
    rw [← hc]; rfl
  -- the strict row inequality
  have hlt : ∑ j, hhafDressedMatrix0 L n j * v j < hhafDressedMatrix0 L n n * v n :=
    row_sum_mul_lt_diag_mul_of_offdiag_nonpos_exists_neg (i := n) hposv
      (fun j hj => hhafDressedMatrix0_offdiag_nonpos L hLeven fun h => hj h.symm)
      ⟨τ, hτ_ne, hτ_neg⟩
  have hdiag : hhafDressedMatrix0 L n n = -(L : ℝ) := hhafDressedMatrix0_Neel_diag L hLeven hL
  rw [hrow, hdiag] at hlt
  -- `μ * v n < -L * v n` with `v n > 0`
  have hvn := hposv n
  nlinarith [hlt, hvn]

/-! ## Classification of hidden-AFM sectors (`pmCount ∈ {1} ∪ even`)

The complete-hidden-AFM constraint makes the `±` spins alternate in sign along the ring.  Reading
the `±` sites in increasing index order, consecutive ones are `IsNextPM` pairs (no `±` spin strictly
between), so their signs alternate; and the maximal/minimal `±` sites are also an `IsNextPM` pair
(the cyclic wrap contains no `±` spin), which closes the alternation.  Consequently the `±` count is
`1` or even, and `magSumS = L` exactly on the even (balanced) sector. -/

/-- The finset of `±` sites of a configuration. -/
def hhafPMFinset {L : ℕ} (σ : Fin L → Fin 3) : Finset (Fin L) :=
  Finset.univ.filter (fun x => σ x ≠ 1)

/-- Membership in the `±` finset is being a `±` site. -/
theorem mem_hhafPMFinset {L : ℕ} (σ : Fin L → Fin 3) (x : Fin L) :
    x ∈ hhafPMFinset σ ↔ σ x ≠ 1 := by
  rw [hhafPMFinset, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

/-- `hhafPMFinset` has cardinality `pmCount`. -/
theorem hhafPMFinset_card {L : ℕ} (σ : hhafConfig L) :
    (hhafPMFinset σ.1).card = pmCount L σ := rfl

/-- **Consecutive `±` sites are an `IsNextPM` pair**: no `±` spin lies strictly between two
index-adjacent `±` sites, so the open arc between them is all `0`-spins. -/
theorem hhaf_isNextPM_consecutive {L k : ℕ} (σ : Fin L → Fin 3)
    (h : (hhafPMFinset σ).card = k) (i : Fin k) (hi : i.val + 1 < k) :
    IsNextPM σ ((hhafPMFinset σ).orderEmbOfFin h i)
      ((hhafPMFinset σ).orderEmbOfFin h ⟨i.val + 1, hi⟩) := by
  set e := (hhafPMFinset σ).orderEmbOfFin h with he
  have hlt : e i < e ⟨i.val + 1, hi⟩ := e.strictMono (Nat.lt_succ_self i.val)
  refine ⟨ne_of_lt hlt, ?_, ?_, ?_⟩
  · exact (mem_hhafPMFinset σ _).mp (Finset.orderEmbOfFin_mem _ h i)
  · exact (mem_hhafPMFinset σ _).mp (Finset.orderEmbOfFin_mem _ h _)
  · intro z hz
    have hlt' : (e i).val < (e ⟨i.val + 1, hi⟩).val := hlt
    rw [InCyclicOpen, if_pos hlt'] at hz
    by_contra hzpm
    have hzF : z ∈ hhafPMFinset σ := (mem_hhafPMFinset σ z).mpr hzpm
    have hzr : z ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hzF
    obtain ⟨m, hm⟩ := hzr
    have hmi : i < m := e.strictMono.lt_iff_lt.mp (hm ▸ (Fin.lt_def).mpr hz.1)
    have hmi1 : m < (⟨i.val + 1, hi⟩ : Fin k) :=
      e.strictMono.lt_iff_lt.mp (hm ▸ (Fin.lt_def).mpr hz.2)
    exact absurd (lt_of_lt_of_le hmi (Nat.lt_succ_iff.mp hmi1)) (lt_irrefl _)

/-- Two distinct `±` spin values are complementary: `{0, 2}` with `v = 2 - u`. -/
theorem pm_flip {u v : Fin 3} (hu : u ≠ 1) (hv : v ≠ 1) (huv : u ≠ v) :
    v.val = 2 - u.val := by
  have hu3 := u.isLt
  have hv3 := v.isLt
  have hune : u.val ≠ 1 := fun hh => hu (Fin.ext hh)
  have hvne : v.val ≠ 1 := fun hh => hv (Fin.ext hh)
  have huvne : u.val ≠ v.val := fun hh => huv (Fin.ext hh)
  omega

/-- **The maximal and minimal `±` sites are an `IsNextPM` pair** (the cyclic wrap): no `±` spin lies
outside the index range `[min, max]` of `±` sites, so the wrap arc is all `0`-spins. -/
theorem hhaf_isNextPM_wrap {L k : ℕ} (σ : Fin L → Fin 3) (h : (hhafPMFinset σ).card = k)
    (hk : 2 ≤ k) :
    IsNextPM σ ((hhafPMFinset σ).orderEmbOfFin h ⟨k - 1, by omega⟩)
      ((hhafPMFinset σ).orderEmbOfFin h ⟨0, by omega⟩) := by
  set e := (hhafPMFinset σ).orderEmbOfFin h with he
  have hgt : e ⟨0, by omega⟩ < e ⟨k - 1, by omega⟩ := e.strictMono (by simp; omega)
  refine ⟨ne_of_gt hgt, ?_, ?_, ?_⟩
  · exact (mem_hhafPMFinset σ _).mp (Finset.orderEmbOfFin_mem _ h _)
  · exact (mem_hhafPMFinset σ _).mp (Finset.orderEmbOfFin_mem _ h _)
  · intro z hz
    have hgt' : (e ⟨0, by omega⟩).val < (e ⟨k - 1, by omega⟩).val := hgt
    have hnle : ¬ (e ⟨k - 1, by omega⟩).val < (e ⟨0, by omega⟩).val := by omega
    rw [InCyclicOpen, if_neg hnle] at hz
    by_contra hzpm
    have hzF : z ∈ hhafPMFinset σ := (mem_hhafPMFinset σ z).mpr hzpm
    have hzr : z ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hzF
    obtain ⟨m, hm⟩ := hzr
    have hlo : e ⟨0, by omega⟩ ≤ e m := e.le_iff_le.mpr (Fin.le_def.mpr (Nat.zero_le _))
    have hhi : e m ≤ e ⟨k - 1, by omega⟩ :=
      e.le_iff_le.mpr (Fin.le_def.mpr (Nat.le_pred_of_lt m.isLt))
    rw [hm] at hlo hhi
    have hlo' : (e ⟨0, by omega⟩).val ≤ z.val := hlo
    have hhi' : z.val ≤ (e ⟨k - 1, by omega⟩).val := hhi
    omega

/-- **The `±` signs alternate along the sorted `±` sites**: the `i`-th `±` value (in increasing
index order) equals the `0`-th value when `i` is even and its complement when `i` is odd. -/
theorem hhaf_pm_alternates {L k : ℕ} {σ : Fin L → Fin 3} (hσ : IsHiddenAFMConfig σ)
    (h : (hhafPMFinset σ).card = k) (hk0 : 0 < k) :
    ∀ j (hj : j < k), (σ ((hhafPMFinset σ).orderEmbOfFin h ⟨j, hj⟩)).val =
      if Even j then (σ ((hhafPMFinset σ).orderEmbOfFin h ⟨0, hk0⟩)).val
      else 2 - (σ ((hhafPMFinset σ).orderEmbOfFin h ⟨0, hk0⟩)).val := by
  set e := (hhafPMFinset σ).orderEmbOfFin h with he
  set a := (σ (e ⟨0, hk0⟩)).val with ha
  intro j
  induction j with
  | zero =>
    intro hj
    split_ifs with hc
    · rfl
    · exact absurd (⟨0, rfl⟩ : Even 0) hc
  | succ n ih =>
    intro hj
    have hn : n < k := by omega
    have hstep := hhaf_isNextPM_consecutive σ h ⟨n, hn⟩ (by omega)
    have hne := hσ _ _ hstep
    have hpmn : σ (e ⟨n, hn⟩) ≠ 1 := (mem_hhafPMFinset σ _).mp (Finset.orderEmbOfFin_mem _ h _)
    have hpmn1 : σ (e ⟨n + 1, hj⟩) ≠ 1 :=
      (mem_hhafPMFinset σ _).mp (Finset.orderEmbOfFin_mem _ h _)
    have hflip : (σ (e ⟨n + 1, hj⟩)).val = 2 - (σ (e ⟨n, hn⟩)).val := pm_flip hpmn hpmn1 hne
    have ha2 : a ≤ 2 := by have := (σ (e ⟨0, hk0⟩)).isLt; omega
    rw [hflip, ih hn]
    simp only [Nat.even_iff]
    split_ifs <;> omega

/-- **Sector classification (count)**: a hidden-AFM configuration has exactly one `±` spin or an
even number.  An odd count `≥ 3` is impossible: the wrap `IsNextPM` pair (max/min `±` site) would
force the first and last `±` signs to differ, but the linear alternation makes them equal when the
count is odd. -/
theorem hhaf_pmCount_eq_one_or_even {L : ℕ} (σ : hhafConfig L) :
    pmCount L σ = 1 ∨ Even (pmCount L σ) := by
  set k := pmCount L σ with hk
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · interval_cases k
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl rfl
  · refine Or.inr ?_
    by_contra hodd
    have hcard : (hhafPMFinset σ.1).card = k := hhafPMFinset_card σ
    have hk0 : 0 < k := by omega
    have hwrap := hhaf_isNextPM_wrap σ.1 hcard hge
    have hne := σ.2 _ _ hwrap
    have halt := hhaf_pm_alternates σ.2 hcard hk0
    have hek : Even (k - 1) := Nat.even_iff.mpr (by rw [Nat.even_iff] at hodd; omega)
    have hvk := halt (k - 1) (by omega)
    rw [if_pos hek] at hvk
    exact hne (Fin.ext hvk)

/-- **Sector classification (magnetization, single-`±`)**: a single-`±` configuration has total
magnetization `L ± 1`, never `L` (the lone `±` site contributes `0` or `2`, the rest contribute
`1`). -/
theorem hhaf_magSumS_ne_L_of_pmCount_one {L : ℕ} (σ : hhafConfig L) (hpm : pmCount L σ = 1) :
    magSumS σ.1 ≠ L := by
  have hpm' : (hhafPMFinset σ.1).card = 1 := (hhafPMFinset_card σ).trans hpm
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hpm'
  have hsne : σ.1 s ≠ 1 :=
    (mem_hhafPMFinset σ.1 s).mp (by rw [hs]; exact Finset.mem_singleton_self s)
  have hother : ∀ x, x ≠ s → σ.1 x = 1 := by
    intro x hx
    by_contra hxpm
    have hxF : x ∈ hhafPMFinset σ.1 := (mem_hhafPMFinset σ.1 x).mpr hxpm
    rw [hs, Finset.mem_singleton] at hxF
    exact hx hxF
  have hrest : ∑ x ∈ Finset.univ.erase s, (σ.1 x).val = L - 1 := by
    have hone : ∀ x ∈ Finset.univ.erase s, (σ.1 x).val = 1 := fun x hx => by
      rw [hother x (Finset.mem_erase.mp hx).1]; rfl
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ s),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hsval : (σ.1 s).val = 0 ∨ (σ.1 s).val = 2 := by
    have h3 := (σ.1 s).isLt
    have hne1 : (σ.1 s).val ≠ 1 := fun hh => hsne (Fin.ext hh)
    omega
  have hLpos : 1 ≤ L := by have := s.isLt; omega
  rw [magSumS, ← Finset.add_sum_erase _ _ (Finset.mem_univ s), hrest]
  omega

/-- `magSumS` is invariant under HAF reachability (every ladder move preserves it). -/
theorem magSumS_eq_of_hhafReachable {L : ℕ} {σ τ : hhafConfig L}
    (h : RaiseLowerReachableSHhaf L σ τ) : magSumS σ.1 = magSumS τ.1 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [ih]; exact (magSumS_eq_of_raiseLowerStepS hstep).symm

/-- **Sector classification (magnetization, balanced)**: an even-`±`-count configuration has total
magnetization exactly `L`.  Every HAF ladder move preserves `magSumS`, and an even-count
configuration is HAF-reachable from the canonical all-`0`-spin configuration (which has
`magSumS = L`). -/
theorem hhaf_magSumS_eq_L_of_even {L : ℕ} (σ : hhafConfig L) (heven : Even (pmCount L σ)) :
    magSumS σ.1 = L := by
  rw [← magSumS_eq_of_hhafReachable (hhaf_reachable_canonical σ heven)]
  simp [magSumS_def, hhafCanonical]

/-! ## Block structure of the restricted matrix by magnetization sector -/

/-- The restricted matrix is **block-diagonal by total magnetization**: entries between
configurations of different `magSumS` vanish (magnetization conservation of the Heisenberg
Hamiltonian). -/
theorem hhafRestrictedMatrix_eq_zero_of_magSumS_ne {L : ℕ} {σ τ : hhafConfig L}
    (h : magSumS σ.1 ≠ magSumS τ.1) : hhafRestrictedMatrix L σ τ = 0 := by
  rw [hhafRestrictedMatrix, Matrix.submatrix_apply, afmHeisenbergChainHamiltonianS]
  exact heisenbergHamiltonianS_apply_eq_zero_of_magSumS_ne (ringCoupling L) 2 (Ne.symm h)

/-- The **`P`-slice** of the restricted matrix (its submatrix on `{σ // P σ}`). -/
noncomputable def hhafRestrictedMatrixSlice {L : ℕ} (P : hhafConfig L → Prop) [DecidablePred P] :
    Matrix {σ : hhafConfig L // P σ} {σ : hhafConfig L // P σ} ℂ :=
  (hhafRestrictedMatrix L).submatrix Subtype.val Subtype.val

/-- **Block restriction**: if the restricted matrix has no coupling from a `P`-configuration to a
non-`P`-configuration, then a full eigenvector restricted to the `P`-slice is an eigenvector of the
`P`-slice with the same eigenvalue. -/
theorem hhafRestrictedMatrixSlice_mulVec_of_full_eigen {L : ℕ} (P : hhafConfig L → Prop)
    [DecidablePred P] (hclosed : ∀ σ τ, P σ → ¬ P τ → hhafRestrictedMatrix L σ τ = 0)
    {E : ℂ} {w : hhafConfig L → ℂ}
    (hw : (hhafRestrictedMatrix L).mulVec w = E • w) :
    (hhafRestrictedMatrixSlice P).mulVec (fun σ => w σ.1) = E • (fun σ => w σ.1) := by
  classical
  funext σ
  have hfull : ∑ τ : hhafConfig L, hhafRestrictedMatrix L σ.1 τ * w τ = E * w σ.1 := by
    have := congrFun hw σ.1
    rwa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at this
  rw [Pi.smul_apply, smul_eq_mul, ← hfull]
  -- split the full sum into the `P` part and the (vanishing) non-`P` part
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P
    (fun τ => hhafRestrictedMatrix L σ.1 τ * w τ)]
  have hnot : ∑ τ ∈ Finset.univ.filter (fun τ => ¬ P τ),
      hhafRestrictedMatrix L σ.1 τ * w τ = 0 :=
    Finset.sum_eq_zero fun τ hτ => by
      rw [hclosed σ.1 τ σ.2 (Finset.mem_filter.mp hτ).2, zero_mul]
  rw [hnot, add_zero]
  -- the `P`-slice mulVec is the sum over the `P`-subtype
  change (∑ τ : {σ : hhafConfig L // P σ}, hhafRestrictedMatrix L σ.1 τ.1 * w τ.1) = _
  exact (Finset.sum_subtype (Finset.univ.filter P)
    (fun x => by simp) (fun τ => hhafRestrictedMatrix L σ.1 τ * w τ)).symm

/-- The **single-`±` slice is block-closed**: a single-`±` configuration (`pmCount = 1`, total
magnetization `L ± 1`) has no coupling to a non-single-`±` configuration (which, by the
classification, has even `pmCount` hence magnetization `L`). -/
theorem hhafRestrictedMatrix_pmCount_one_block_closed {L : ℕ}
    (σ τ : hhafConfig L) (hσ : pmCount L σ = 1) (hτ : ¬ pmCount L τ = 1) :
    hhafRestrictedMatrix L σ τ = 0 := by
  have hτeven : Even (pmCount L τ) := (hhaf_pmCount_eq_one_or_even τ).resolve_left hτ
  refine hhafRestrictedMatrix_eq_zero_of_magSumS_ne ?_
  rw [hhaf_magSumS_eq_L_of_even τ hτeven]
  exact hhaf_magSumS_ne_L_of_pmCount_one σ hσ

/-- The **balanced slice is block-closed**: an even-`pmCount` configuration (magnetization `L`) has
no coupling to an odd-`pmCount` (i.e. `pmCount = 1`, magnetization `L ± 1`) configuration. -/
theorem hhafRestrictedMatrix_even_block_closed {L : ℕ}
    (σ τ : hhafConfig L) (hσ : Even (pmCount L σ)) (hτ : ¬ Even (pmCount L τ)) :
    hhafRestrictedMatrix L σ τ = 0 := by
  have hτ1 : pmCount L τ = 1 := (hhaf_pmCount_eq_one_or_even τ).resolve_right hτ
  refine hhafRestrictedMatrix_eq_zero_of_magSumS_ne ?_
  rw [hhaf_magSumS_eq_L_of_even σ hσ]
  exact (hhaf_magSumS_ne_L_of_pmCount_one τ hτ1).symm

/-! ## Ground-eigenspace finrank ≤ 1 -/

/-- The **complex balanced block** (submatrix of `hhafRestrictedMatrix` on the balanced sector) is
the real balanced block cast to `ℂ` (the entries are real). -/
theorem hhafRestrictedMatrix_submatrix0_eq_map (L : ℕ) :
    (hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfig0 L → hhafConfig L) Subtype.val =
      (hhafRestrictedMatrixReal0 L).map (Complex.ofReal) := by
  ext σ τ
  rw [Matrix.submatrix_apply, Matrix.map_apply, hhafRestrictedMatrixReal0, Matrix.submatrix_apply]
  exact (hhafRestrictedMatrixReal_ofReal L σ.1 τ.1).symm

/-- The **complex balanced block ground eigenspace is one-dimensional**: transferring the real
balanced Perron–Frobenius `finrank ≤ 1` through the real-to-complex bridge. -/
theorem hhafRestrictedMatrix_submatrix0_eigenspace_finrank_le_one (L : ℕ) (hLeven : Even L) :
    ∃ μ : ℝ, Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin'
      ((hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfig0 L → hhafConfig L)
        Subtype.val)) (μ : ℂ)) ≤ 1 := by
  obtain ⟨μ, w, _, _, _, hfin⟩ := hhafRestrictedMatrixReal0_ground_finrank_le_one L hLeven
  refine ⟨μ, ?_⟩
  rw [hhafRestrictedMatrix_submatrix0_eq_map]
  exact matrix_complex_eigenspace_finrank_le_one_of_real (hhafRestrictedMatrixReal0 L) μ hfin

/-- The **real (undressed) restricted matrix on the single-`±` sector**. -/
noncomputable def hhafRestrictedMatrixRealPM1 (L : ℕ) :
    Matrix (hhafConfigPM1 L) (hhafConfigPM1 L) ℝ :=
  (hhafRestrictedMatrixReal L).submatrix Subtype.val Subtype.val

/-- The complex single-`±` block is the real single-`±` block cast to `ℂ`. -/
theorem hhafRestrictedMatrix_submatrixPM1_eq_map (L : ℕ) :
    (hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfigPM1 L → hhafConfig L) Subtype.val =
      (hhafRestrictedMatrixRealPM1 L).map (Complex.ofReal) := by
  ext σ τ
  rw [Matrix.submatrix_apply, Matrix.map_apply, hhafRestrictedMatrixRealPM1, Matrix.submatrix_apply]
  exact (hhafRestrictedMatrixReal_ofReal L σ.1 τ.1).symm

/-- The **single-`±` Marshall sign diagonal** `Θ` (entries `±1`). -/
noncomputable def hhafMarshallDiagPM1 (L : ℕ) : Matrix (hhafConfigPM1 L) (hhafConfigPM1 L) ℝ :=
  Matrix.diagonal (fun σ : hhafConfigPM1 L => (marshallSignS (ringSublattice L) σ.1.1).re)

/-- The single-`±` Marshall sign diagonal squares to the identity. -/
theorem hhafMarshallDiagPM1_mul_self (L : ℕ) :
    hhafMarshallDiagPM1 L * hhafMarshallDiagPM1 L = 1 := by
  rw [hhafMarshallDiagPM1, Matrix.diagonal_mul_diagonal]
  have h1 : (fun σ : hhafConfigPM1 L => (marshallSignS (ringSublattice L) σ.1.1).re *
      (marshallSignS (ringSublattice L) σ.1.1).re) = fun _ => 1 := by
    funext σ
    have h := congrArg Complex.re (marshallSignS_sq (ringSublattice L) σ.1.1)
    rwa [Complex.mul_re, marshallSignS_im, mul_zero, sub_zero, Complex.one_re] at h
  rw [h1, Matrix.diagonal_one]

/-- The dressed single-`±` block is the Marshall conjugate of the undressed real block. -/
theorem hhafDressedMatrixPM1_eq_conj (L : ℕ) :
    hhafDressedMatrixPM1 L =
      hhafMarshallDiagPM1 L * hhafRestrictedMatrixRealPM1 L * hhafMarshallDiagPM1 L := by
  ext σ τ
  rw [hhafDressedMatrixPM1, Matrix.submatrix_apply, hhafDressedMatrix_eq, Matrix.mul_assoc,
    hhafMarshallDiagPM1, Matrix.diagonal_mul, Matrix.mul_diagonal, hhafRestrictedMatrixRealPM1,
    Matrix.submatrix_apply]
  ring

/-- **The complex single-`±` block has all eigenvalues `≥ −2`.**  An eigenvalue is real (the block
is real), transfers to a real-block eigenvector (re/im part), then to a dressed-block eigenvector
via the Marshall conjugation, where the Gershgorin bound `≥ −2` applies. -/
theorem hhafRestrictedMatrix_submatrixPM1_eigenvalue_ge (L : ℕ) (hL : 2 ≤ L) {E : ℝ}
    (hE : Module.End.HasEigenvalue (Matrix.toLin'
      ((hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfigPM1 L → hhafConfig L)
        Subtype.val)) (E : ℂ)) : -2 ≤ E := by
  rw [hhafRestrictedMatrix_submatrixPM1_eq_map] at hE
  obtain ⟨v, hv_eig, hv_ne⟩ := hE.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv_eig
  -- transfer a nonzero real-block eigenvector to a dressed-block eigenvalue via Marshall
  have hdΘ : hhafDressedMatrixPM1 L * hhafMarshallDiagPM1 L =
      hhafMarshallDiagPM1 L * hhafRestrictedMatrixRealPM1 L := by
    rw [hhafDressedMatrixPM1_eq_conj, Matrix.mul_assoc, Matrix.mul_assoc,
      hhafMarshallDiagPM1_mul_self, Matrix.mul_one]
  have key : ∀ w : hhafConfigPM1 L → ℝ, w ≠ 0 →
      (hhafRestrictedMatrixRealPM1 L).mulVec w = E • w →
      Module.End.HasEigenvalue (Matrix.toLin' (hhafDressedMatrixPM1 L)) E := by
    intro w hw hweig
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := (hhafMarshallDiagPM1 L).mulVec w) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hdΘ,
        ← Matrix.mulVec_mulVec, hweig, Matrix.mulVec_smul]
    · intro hh
      apply hw
      have h0 : (hhafMarshallDiagPM1 L).mulVec ((hhafMarshallDiagPM1 L).mulVec w) = 0 := by
        rw [hh, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hhafMarshallDiagPM1_mul_self, Matrix.one_mulVec] at h0
  refine hhafDressedMatrixPM1_eigenvalue_ge hL ?_
  by_cases hvre : (fun i => (v i).re) = 0
  · have hvim : (fun i => (v i).im) ≠ 0 := by
      intro hh; apply hv_ne; funext i
      exact Complex.ext (congrFun hvre i) (congrFun hh i)
    exact key _ hvim (matrix_eigenvec_im_of_complex hv_eig)
  · exact key _ hvre (matrix_eigenvec_re_of_complex hv_eig)

/-- The **zero-extension** of a `P`-slice vector to all of `hhafConfig`. -/
noncomputable def hhafSliceExtend {L : ℕ} (P : hhafConfig L → Prop) [DecidablePred P]
    (w : {σ : hhafConfig L // P σ} → ℂ) : hhafConfig L → ℂ :=
  fun σ => if h : P σ then w ⟨σ, h⟩ else 0

/-- The zero-extension is nonzero when the slice vector is. -/
theorem hhafSliceExtend_ne_zero {L : ℕ} (P : hhafConfig L → Prop) [DecidablePred P]
    {w : {σ : hhafConfig L // P σ} → ℂ} (hw : w ≠ 0) : hhafSliceExtend P w ≠ 0 := by
  intro h
  apply hw
  funext σ
  have hc := congrFun h σ.1
  rwa [hhafSliceExtend, dif_pos σ.2, Subtype.coe_eta, Pi.zero_apply] at hc

/-- **Reverse block restriction**: if the restricted matrix has no coupling into a `P`-slice from
its complement (`hclosed'`), then the zero-extension of a `P`-slice eigenvector is a full
eigenvector with the same eigenvalue. -/
theorem hhafRestrictedMatrix_mulVec_hhafSliceExtend {L : ℕ} (P : hhafConfig L → Prop)
    [DecidablePred P] (hclosed' : ∀ σ τ, ¬ P σ → P τ → hhafRestrictedMatrix L σ τ = 0)
    {E : ℂ} {w : {σ : hhafConfig L // P σ} → ℂ}
    (hw : (hhafRestrictedMatrixSlice P).mulVec w = E • w) :
    (hhafRestrictedMatrix L).mulVec (hhafSliceExtend P w) = E • (hhafSliceExtend P w) := by
  classical
  funext σ
  have hsum : (hhafRestrictedMatrix L).mulVec (hhafSliceExtend P w) σ =
      ∑ τ : {σ : hhafConfig L // P σ}, hhafRestrictedMatrix L σ τ.1 * w τ := by
    rw [Matrix.mulVec, dotProduct,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ P
        (fun τ => hhafRestrictedMatrix L σ τ * hhafSliceExtend P w τ)]
    have hnot : ∑ τ ∈ Finset.univ.filter (fun τ => ¬ P τ),
        hhafRestrictedMatrix L σ τ * hhafSliceExtend P w τ = 0 :=
      Finset.sum_eq_zero fun τ hτ => by
        rw [hhafSliceExtend, dif_neg (Finset.mem_filter.mp hτ).2, mul_zero]
    have hmem : ∀ x : hhafConfig L, x ∈ Finset.univ.filter P ↔ P x :=
      fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hnot, add_zero,
      Finset.sum_subtype (Finset.univ.filter P) hmem
        (fun τ => hhafRestrictedMatrix L σ τ * hhafSliceExtend P w τ)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hhafSliceExtend, dif_pos τ.2, Subtype.coe_eta]
  rw [hsum, Pi.smul_apply, smul_eq_mul]
  by_cases hσ : P σ
  · have heq := congrFun hw ⟨σ, hσ⟩
    rw [Pi.smul_apply, smul_eq_mul] at heq
    rw [hhafSliceExtend, dif_pos hσ, ← heq, hhafRestrictedMatrixSlice, Matrix.mulVec, dotProduct]
    rfl
  · rw [hhafSliceExtend, dif_neg hσ, mul_zero]
    exact Finset.sum_eq_zero fun τ _ => by rw [hclosed' σ τ.1 hσ τ.2, zero_mul]

/-- **Consolidated balanced ground data** (a single `μ`): the balanced Perron–Frobenius energy
`μ < −L` is the minimal eigenvalue of the complex balanced block, that block's `μ`-eigenspace is
one-dimensional, and `μ` is realised by a nonzero eigenvector. -/
theorem hhafRestrictedMatrix_balanced_ground (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L) :
    ∃ μ : ℝ, μ < -(L : ℝ) ∧
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin'
        ((hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfig0 L → hhafConfig L)
          Subtype.val)) (μ : ℂ)) ≤ 1 ∧
      (∀ (lam : ℝ) (u : hhafConfig0 L → ℂ), u ≠ 0 →
        ((hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfig0 L → hhafConfig L)
          Subtype.val).mulVec u = (lam : ℂ) • u → μ ≤ lam) ∧
      ∃ w : hhafConfig0 L → ℂ, w ≠ 0 ∧
        ((hhafRestrictedMatrix L).submatrix (Subtype.val : hhafConfig0 L → hhafConfig L)
          Subtype.val).mulVec w = (μ : ℂ) • w := by
  obtain ⟨μ, v, hvpos, hMv, hmin, hfin⟩ := hhafDressedMatrix0_ground_finrank_le_one L hLeven
  have hΘsq := hhafMarshallDiag0_mul_self L
  have hΘinj : Function.Injective (hhafMarshallDiag0 L).mulVec := fun a b hab => by
    have := congrArg (hhafMarshallDiag0 L).mulVec hab
    rwa [Matrix.mulVec_mulVec, hΘsq, Matrix.one_mulVec, Matrix.mulVec_mulVec, hΘsq,
      Matrix.one_mulVec] at this
  have hreal0_dressed : hhafRestrictedMatrixReal0 L * hhafMarshallDiag0 L =
      hhafMarshallDiag0 L * hhafDressedMatrix0 L := by
    rw [hhafDressedMatrix0_eq_conj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hΘsq, Matrix.one_mul]
  have hdressed_real0 : hhafDressedMatrix0 L * hhafMarshallDiag0 L =
      hhafMarshallDiag0 L * hhafRestrictedMatrixReal0 L := by
    rw [hhafDressedMatrix0_eq_conj, Matrix.mul_assoc, hΘsq, Matrix.mul_one]
  have hmin_real0 : ∀ (lam : ℝ) (u : hhafConfig0 L → ℝ), u ≠ 0 →
      (hhafRestrictedMatrixReal0 L).mulVec u = lam • u → μ ≤ lam := by
    intro lam u hu hueig
    refine hmin lam ((hhafMarshallDiag0 L).mulVec u)
      (fun h => hu (hΘinj (by rw [h, Matrix.mulVec_zero]))) ?_
    rw [Matrix.mulVec_mulVec, hdressed_real0, ← Matrix.mulVec_mulVec, hueig, Matrix.mulVec_smul]
  refine ⟨μ, hhafDressedMatrix0_ground_lt_neg_L L hLeven hL hvpos hMv, ?_, ?_, ?_⟩
  · rw [hhafRestrictedMatrix_submatrix0_eq_map]
    apply matrix_complex_eigenspace_finrank_le_one_of_real
    rw [← matrix_similar_eigenspace_finrank_eq hΘsq hΘsq (hhafDressedMatrix0_eq_conj L) μ]
    exact hfin
  · intro lam u hu hueig
    rw [hhafRestrictedMatrix_submatrix0_eq_map] at hueig
    by_cases hure : (fun i => (u i).re) = 0
    · have huim : (fun i => (u i).im) ≠ 0 := fun hh => hu (funext fun i =>
        Complex.ext (congrFun hure i) (congrFun hh i))
      exact hmin_real0 lam _ huim (matrix_eigenvec_im_of_complex hueig)
    · exact hmin_real0 lam _ hure (matrix_eigenvec_re_of_complex hueig)
  · refine ⟨(fun i => (((hhafMarshallDiag0 L).mulVec v) i : ℂ)), ?_, ?_⟩
    · intro h
      have hΘv0 : (hhafMarshallDiag0 L).mulVec v = 0 := by
        funext i; have := congrFun h i; simpa using this
      have hv0 : v = 0 := hΘinj (by rw [hΘv0, Matrix.mulVec_zero])
      obtain ⟨i⟩ := (inferInstance : Nonempty (hhafConfig0 L))
      exact absurd (hv0 ▸ hvpos i) (lt_irrefl 0)
    · rw [hhafRestrictedMatrix_submatrix0_eq_map]
      apply matrix_eigenvec_map_ofReal
      rw [Matrix.mulVec_mulVec, hreal0_dressed, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul]

/-- **The `H_HAF`-restricted ground eigenspace is one-dimensional** — the unique-ground-state core
of Tasaki §6.3 Proposition 6.5.  At the ground energy `E = hhafMinEnergy < −2`, the single-`±` block
is
vacated (its eigenvalues are `≥ −2`) and the balanced block contributes the one-dimensional
Perron–Frobenius ground state. -/
theorem hhafRestrictedMatrix_ground_finrank_le_one (L : ℕ) (hLeven : Even L) (hL : 2 ≤ L) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (hhafRestrictedMatrix L))
      (hhafMinEnergy L : ℂ)) ≤ 1 := by
  classical
  obtain ⟨μ, hμlt, hbal_fin, hbal_min, w0, hw0ne, hw0eig⟩ :=
    hhafRestrictedMatrix_balanced_ground L hLeven hL
  -- reverse-slice closure for the even (balanced) block
  have hclosed_even : ∀ σ τ : hhafConfig L, ¬ Even (pmCount L σ) → Even (pmCount L τ) →
      hhafRestrictedMatrix L σ τ = 0 := fun σ τ hσ hτ =>
    hhafRestrictedMatrix_pmCount_one_block_closed σ τ
      ((hhaf_pmCount_eq_one_or_even σ).resolve_right hσ)
      (fun hpm1 => absurd (hpm1 ▸ hτ) (by decide))
  -- P2: the ground energy is ≤ the balanced eigenvalue μ
  have hEμ : hhafMinEnergy L ≤ μ :=
    hermitian_min_eigenvalue_le_of_eigenvector_exists (hhafRestrictedMatrix_isHermitian L)
      (hhafSliceExtend_ne_zero _ hw0ne)
      (hhafRestrictedMatrix_mulVec_hhafSliceExtend (fun σ => Even (pmCount L σ)) hclosed_even
        hw0eig)
  -- P3: E < −2
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hELt2 : hhafMinEnergy L < -2 := by linarith [hEμ, hμlt]
  -- P4: any E-eigenvector vanishes on the single-`±` configurations
  have hpm0 : ∀ {Ψ : hhafConfig L → ℂ},
      (hhafRestrictedMatrix L).mulVec Ψ = (hhafMinEnergy L : ℂ) • Ψ →
      ∀ τ : hhafConfigPM1 L, Ψ τ.1 = 0 := by
    intro Ψ hΨ τ
    by_contra hτ0
    have hslice := hhafRestrictedMatrixSlice_mulVec_of_full_eigen (fun σ => pmCount L σ = 1)
      (fun σ τ' hσ hτ' => hhafRestrictedMatrix_pmCount_one_block_closed σ τ' hσ hτ') hΨ
    have hsne : (fun σ : hhafConfigPM1 L => Ψ σ.1) ≠ 0 := fun h => hτ0 (congrFun h τ)
    have hev : Module.End.HasEigenvalue (Matrix.toLin' ((hhafRestrictedMatrix L).submatrix
        (Subtype.val : hhafConfigPM1 L → hhafConfig L) Subtype.val)) (hhafMinEnergy L : ℂ) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hslice), hsne⟩
    linarith [hhafRestrictedMatrix_submatrixPM1_eigenvalue_ge L hL hev]
  -- P5: E ≥ μ, hence E = μ (else a ground eigenvector would vanish on both blocks)
  obtain ⟨Ψ₀, hΨ₀ne, hΨ₀eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue (hhafRestrictedMatrix_isHermitian L)
  have hμE : μ ≤ hhafMinEnergy L := by
    by_contra hlt
    -- balanced restriction is a balanced eigenvector at E < μ = balanced min ⟹ zero
    have hbal_eig := hhafRestrictedMatrixSlice_mulVec_of_full_eigen (fun σ => Even (pmCount L σ))
      (fun σ τ hσ hτ => hhafRestrictedMatrix_even_block_closed σ τ hσ hτ) hΨ₀eig
    apply hΨ₀ne
    funext σ
    rcases hhaf_pmCount_eq_one_or_even σ with hpm | hev
    · exact hpm0 hΨ₀eig ⟨σ, hpm⟩
    · by_contra hσ0
      have hsne : (fun σ : hhafConfig0 L => Ψ₀ σ.1) ≠ 0 := fun h => hσ0 (congrFun h ⟨σ, hev⟩)
      exact hlt (hbal_min (hhafMinEnergy L) _ hsne hbal_eig)
  have hEeqμ : hhafMinEnergy L = μ := le_antisymm hEμ hμE
  -- assemble: inject the ground eigenspace into the balanced block eigenspace
  set R : (Module.End.eigenspace (Matrix.toLin' (hhafRestrictedMatrix L))
      (hhafMinEnergy L : ℂ)) →ₗ[ℂ]
      (Module.End.eigenspace (Matrix.toLin' ((hhafRestrictedMatrix L).submatrix
        (Subtype.val : hhafConfig0 L → hhafConfig L) Subtype.val)) (μ : ℂ)) :=
    { toFun := fun Ψ => ⟨fun σ => Ψ.1 σ.1, by
        have hΨeig : (hhafRestrictedMatrix L).mulVec Ψ.1 = (hhafMinEnergy L : ℂ) • Ψ.1 := by
          have := Module.End.mem_eigenspace_iff.mp Ψ.2; rwa [Matrix.toLin'_apply] at this
        have hslice := hhafRestrictedMatrixSlice_mulVec_of_full_eigen
          (fun σ => Even (pmCount L σ))
          (fun σ τ hσ hτ => hhafRestrictedMatrix_even_block_closed σ τ hσ hτ) hΨeig
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, ← hEeqμ]
        exact hslice⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl } with hRdef
  have hR_inj : Function.Injective R := by
    intro x y hxy
    apply Subtype.ext
    funext σ
    have hbal0 : ∀ τ : hhafConfig0 L, x.1 τ.1 = y.1 τ.1 := fun τ =>
      congrFun (congrArg Subtype.val hxy) τ
    have hxeig : (hhafRestrictedMatrix L).mulVec x.1 = (hhafMinEnergy L : ℂ) • x.1 := by
      have := Module.End.mem_eigenspace_iff.mp x.2; rwa [Matrix.toLin'_apply] at this
    have hyeig : (hhafRestrictedMatrix L).mulVec y.1 = (hhafMinEnergy L : ℂ) • y.1 := by
      have := Module.End.mem_eigenspace_iff.mp y.2; rwa [Matrix.toLin'_apply] at this
    rcases hhaf_pmCount_eq_one_or_even σ with hpm | hev
    · rw [hpm0 hxeig ⟨σ, hpm⟩, hpm0 hyeig ⟨σ, hpm⟩]
    · exact hbal0 ⟨σ, hev⟩
  exact le_trans (LinearMap.finrank_le_finrank_of_injective hR_inj) hbal_fin

/-- A projection-fixed vector is the embedding of its restriction to `H_HAF`. -/
theorem hhafSubspaceEmbedding_of_projFixed (L : ℕ) {Ψ : (Fin L → Fin 3) → ℂ}
    (hΨ : (hhafProjection L).mulVec Ψ = Ψ) :
    Ψ = hhafSubspaceEmbedding L (fun σ : hhafConfig L => Ψ σ.1) := by
  funext σ
  by_cases h : IsHiddenAFMConfig σ
  · exact (hhafSubspaceEmbedding_apply_subtype L (fun σ : hhafConfig L => Ψ σ.1) ⟨σ, h⟩).symm
  · rw [hhafSubspaceEmbedding_apply_of_not L (fun σ : hhafConfig L => Ψ σ.1) h]
    have hc := congrFun hΨ σ
    rw [hhafProjection, Matrix.mulVec_diagonal, if_neg h, zero_mul] at hc
    exact hc.symm

/-- A projection-fixed eigenvector of the compressed Hamiltonian restricts to an eigenvector of the
restricted matrix at the same energy. -/
theorem hhafRestrictedMatrix_mulVec_of_projFixed_eig (L : ℕ) {E : ℂ}
    {Ψ : (Fin L → Fin 3) → ℂ} (hproj : (hhafProjection L).mulVec Ψ = Ψ)
    (heig : (hhafRestrictedChainHamiltonianS L).mulVec Ψ = E • Ψ) :
    (hhafRestrictedMatrix L).mulVec (fun σ : hhafConfig L => Ψ σ.1) =
      E • (fun σ : hhafConfig L => Ψ σ.1) := by
  set w : hhafConfig L → ℂ := fun σ => Ψ σ.1 with hw
  have hΨemb : Ψ = hhafSubspaceEmbedding L w := hhafSubspaceEmbedding_of_projFixed L hproj
  have hinj : Function.Injective (hhafSubspaceEmbedding L) := by
    intro a b hab
    funext σ
    have := congrFun hab σ.1
    rwa [hhafSubspaceEmbedding_apply_subtype, hhafSubspaceEmbedding_apply_subtype] at this
  apply hinj
  rw [← hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding, ← hΨemb, heig,
    hhafSubspaceEmbedding_smul, hΨemb]

/-- **Tasaki §6.3 Proposition 6.5 — unique ground state, finite gap, exponential decay** for the
`S = 1` antiferromagnetic Heisenberg chain on the hidden-antiferromagnetic subspace `H_HAF`
(Gómez-Santos).  For an even ring there is a ground state `Φ` of the compressed Hamiltonian that is
the **unique** (up to scalar) minimal-energy `H_HAF` vector, with a positive spectral gap and
exponentially decaying correlations.  (This discharges the former axiom
`tasaki_prop_6_5_hhaf_spin_one`.) -/
theorem tasaki_prop_6_5_hhaf_spin_one (L : ℕ) (hL : Even L) (hLpos : 0 < L) :
    ∃ (E gap ξ C : ℝ) (Φ : (Fin L → Fin 3) → ℂ),
      (hhafProjection L).mulVec Φ = Φ ∧ Φ ≠ 0 ∧
      (hhafRestrictedChainHamiltonianS L).mulVec Φ = (E : ℂ) • Φ ∧
      (∀ E' ∈ hhafRealSpectrum L, E ≤ E') ∧
      (∀ Ψ : (Fin L → Fin 3) → ℂ, Ψ ≠ 0 → (hhafProjection L).mulVec Ψ = Ψ →
        (hhafRestrictedChainHamiltonianS L).mulVec Ψ = (E : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ) ∧
      0 < gap ∧ (∃ E₁ ∈ hhafRealSpectrum L, E < E₁ ∧ gap = E₁ - E ∧
        ∀ E' ∈ hhafRealSpectrum L, E < E' → E₁ ≤ E') ∧
      0 < ξ ∧ 0 ≤ C ∧
      ∀ x y : Fin L, |chainCorrelation L Φ x y| ≤ C * Real.exp (-(ringDist L x y : ℝ) / ξ) := by
  have hL2 : 2 ≤ L := by obtain ⟨m, hm⟩ := hL; omega
  obtain ⟨w₀, hw₀ne, hw₀eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue (hhafRestrictedMatrix_isHermitian L)
  set Φ := hhafSubspaceEmbedding L w₀ with hΦdef
  -- clause 3: the embedded ground vector is an eigenvector of the compressed Hamiltonian
  have hΦeig : (hhafRestrictedChainHamiltonianS L).mulVec Φ = (hhafMinEnergy L : ℂ) • Φ := by
    rw [hΦdef, hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding, hw₀eig,
      hhafSubspaceEmbedding_smul, hhafMinEnergy]
  -- the finrank ≤ 1 bound on the restricted ground eigenspace
  have hfin := hhafRestrictedMatrix_ground_finrank_le_one L hL hL2
  have hw₀mem : w₀ ∈ Module.End.eigenspace (Matrix.toLin' (hhafRestrictedMatrix L))
      (hhafMinEnergy L : ℂ) := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hw₀eig
  obtain ⟨gap, hgappos, hgapwit⟩ := exists_hhaf_positive_gap L hL hLpos
  obtain ⟨ξ, hξpos, C, hCnn, hdecay⟩ := hhaf_correlation_exp_decay_exists L Φ
  refine ⟨hhafMinEnergy L, gap, ξ, C, Φ,
    hΦdef ▸ hhafProjection_mulVec_hhafSubspaceEmbedding L w₀,
    hΦdef ▸ hhafSubspaceEmbedding_ne_zero L hw₀ne, hΦeig, ?_, ?_, hgappos, hgapwit, hξpos, hCnn,
    hdecay⟩
  · -- clause 4: minimality over the restricted spectrum
    rintro E' ⟨Φ', hΦ'ne, hΦ'proj, hΦ'eig⟩
    have hrest := hhafRestrictedMatrix_mulVec_of_projFixed_eig L hΦ'proj hΦ'eig
    have hwne : (fun σ : hhafConfig L => Φ' σ.1) ≠ 0 := by
      intro h
      apply hΦ'ne
      rw [hhafSubspaceEmbedding_of_projFixed L hΦ'proj, h]
      funext σ; simp only [hhafSubspaceEmbedding, Pi.zero_apply]; split_ifs <;> rfl
    exact hermitian_min_eigenvalue_le_of_eigenvector_exists (hhafRestrictedMatrix_isHermitian L)
      hwne hrest
  · -- clause 5: uniqueness via finrank ≤ 1
    intro Ψ hΨne hΨproj hΨeig
    have hrest := hhafRestrictedMatrix_mulVec_of_projFixed_eig L hΨproj hΨeig
    have hΨmem : (fun σ : hhafConfig L => Ψ σ.1) ∈
        Module.End.eigenspace (Matrix.toLin' (hhafRestrictedMatrix L)) (hhafMinEnergy L : ℂ) := by
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hrest
    rw [finrank_le_one_iff] at hfin
    obtain ⟨v₀, hv₀⟩ := hfin
    obtain ⟨cΨ, hcΨ⟩ := hv₀ ⟨_, hΨmem⟩
    obtain ⟨c0, hc0⟩ := hv₀ ⟨w₀, hw₀mem⟩
    have hΨv : (fun σ : hhafConfig L => Ψ σ.1) = cΨ • v₀.1 := by
      have h := congrArg Subtype.val hcΨ.symm; simpa using h
    have hw₀v : w₀ = c0 • v₀.1 := by
      have h := congrArg Subtype.val hc0.symm; simpa using h
    have hc0ne : c0 ≠ 0 := by
      intro h; apply hw₀ne; rw [hw₀v, h, zero_smul]
    refine ⟨cΨ * c0⁻¹, ?_⟩
    rw [hhafSubspaceEmbedding_of_projFixed L hΨproj, hΦdef, ← hhafSubspaceEmbedding_smul]
    congr 1
    rw [hΨv, hw₀v, smul_smul, mul_assoc, inv_mul_cancel₀ hc0ne, mul_one]

end LatticeSystem.Quantum
