import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandWeightSupport
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModePeel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandDoubleOcc

/-!
# Tasaki §11.3.1: the no-double-occupancy spin-swap coefficient relation (toward block ≤ 1)

Applying the double annihilation `ĉ_{int(p)↓} ĉ_{int(p)↑}` (which kills a ground vector) and reading
one occupation-basis coordinate isolates exactly the two orbital-spin configurations that differ by
swapping the spins of the overlapping orbitals `p` and `p+1`: only `α_p` and `α_{p+1}` are supported
at the shared internal site `int(p)` (both with amplitude `−ν`).  The two contributions carry the
same scalar `ν²` and a relative Koszul sign of `−1` — *independent* of where `p, p+1` sit in the
occupation list — so the two coefficients are equal: `c_S = c_{S with p,(p+1) spins swapped}`.

This file sets up the position-independent Koszul sign identity and the orbital-spin ↔ occupation
config map; the coefficient extraction and the swap relation itself follow.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **Position-independent relative Koszul sign for a two-mode erase.**  Whatever the lengths of the
list segments before / between the two erased modes, the two ways of erasing them (in the two spin
orders) differ by an overall sign of `−1`: both sides reduce to `(-1)^(2m+n)`. -/
theorem koszul_two_erase_sign_split (m n : ℕ) :
    (-1 : ℂ) ^ m * (-1 : ℂ) ^ (m + n) = -((-1 : ℂ) ^ (m + n + 1) * (-1 : ℂ) ^ m) := by
  rw [← pow_add, ← pow_add, show m + n + 1 + m = m + (m + n) + 1 by ring, pow_succ]
  ring

/-- **Orbital-spin → occupation config.**  An up/down assignment `s : Fin (K+1) → Fin 2` of the
`K+1` flat-band orbitals (`s p` the chosen spin) maps to the occupation config that occupies the
single mode `(inl p, s p)` for each orbital `p` and no `β` mode. -/
def flatBandAlphaSpinOcc (K : ℕ) (s : Fin (K + 1) → Fin 2) :
    (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2 :=
  fun q => match q.1 with
    | Sum.inl p => if q.2 = s p then 1 else 0
    | Sum.inr _ => 0

/-- The `α`-spin occupation config has no `β` occupation. -/
theorem flatBandAlphaSpinOcc_inr (s : Fin (K + 1) → Fin 2) (u : Fin (K + 1)) (σ : Fin 2) :
    flatBandAlphaSpinOcc K s (Sum.inr u, σ) = 0 := rfl

/-- The mode `(inl p, σ)` is occupied in the `α`-spin config exactly when `σ` is the chosen spin. -/
theorem flatBandAlphaSpinOcc_inl (s : Fin (K + 1) → Fin 2) (p : Fin (K + 1)) (σ : Fin 2) :
    flatBandAlphaSpinOcc K s (Sum.inl p, σ) = if σ = s p then 1 else 0 := rfl

/-- A mode is in the occupied finset iff the config value there is `1`. -/
theorem mem_occFinset_iff (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (q : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2) : q ∈ occFinset f ↔ f q = 1 := by
  rw [occFinset, Finset.mem_filter, and_iff_right (Finset.mem_univ q)]

/-- **Occupied modes of an `α`-spin config.**  A mode `q` is occupied exactly when it is the chosen
spin mode `(inl p, s p)` of some orbital `p`. -/
theorem mem_occFinset_alphaSpinOcc (s : Fin (K + 1) → Fin 2)
    (q : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2) :
    q ∈ occFinset (flatBandAlphaSpinOcc K s) ↔ ∃ p, q = (Sum.inl p, s p) := by
  rw [occFinset, Finset.mem_filter]
  obtain ⟨m, σ⟩ := q
  constructor
  · rintro ⟨_, hq⟩
    cases m with
    | inl p =>
      rw [flatBandAlphaSpinOcc_inl] at hq
      split_ifs at hq with h
      · exact ⟨p, by rw [h]⟩
      · exact absurd hq (by decide)
    | inr u => rw [flatBandAlphaSpinOcc_inr] at hq; exact absurd hq (by decide)
  · rintro ⟨p, hp⟩
    obtain ⟨hm, hσ⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
    subst hm; subst hσ
    exact ⟨Finset.mem_univ _, by rw [flatBandAlphaSpinOcc_inl, if_pos rfl]⟩

/-- The `α`-spin occupation set is the image of the chosen-spin embedding `p ↦ (inl p, s p)`. -/
theorem occFinset_alphaSpinOcc_eq_image (s : Fin (K + 1) → Fin 2) :
    occFinset (flatBandAlphaSpinOcc K s)
      = Finset.univ.image (fun p : Fin (K + 1) => (Sum.inl p, s p)) := by
  ext q
  rw [mem_occFinset_alphaSpinOcc, Finset.mem_image]
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p, Finset.mem_univ _, rfl⟩
  · rintro ⟨p, _, rfl⟩; exact ⟨p, rfl⟩

/-- The `α`-spin config occupies exactly `K+1` modes (one per orbital). -/
theorem occFinset_alphaSpinOcc_card (s : Fin (K + 1) → Fin 2) :
    (occFinset (flatBandAlphaSpinOcc K s)).card = K + 1 := by
  rw [occFinset_alphaSpinOcc_eq_image,
    Finset.card_image_of_injective _ (fun a b hab => Sum.inl_injective (congrArg Prod.fst hab)),
    Finset.card_univ, Fintype.card_fin]

/-- **The `Ŝ^z` weight of an `α`-spin config** is the sum of the per-orbital spin charges:
`∑_{q occupied} (1/2 − σ_q) = ∑_p (1/2 − s p)`.  Each orbital `p` contributes its single occupied
mode's charge `flatBandSpinCharge (s p)`. -/
theorem occFinset_alphaSpinOcc_spinCharge_sum (s : Fin (K + 1) → Fin 2) :
    ∑ q ∈ occFinset (flatBandAlphaSpinOcc K s), flatBandSpinCharge q.2
      = ∑ p : Fin (K + 1), flatBandSpinCharge (s p) := by
  rw [occFinset_alphaSpinOcc_eq_image,
    Finset.sum_image (fun a _ b _ hab => Sum.inl_injective (congrArg Prod.fst hab))]

/-- **An `α`-spin occupation monomial is an `Ŝ^z` eigenvector** with eigenvalue
`∑_p (1/2 − s p)` (the total chosen-spin charge). -/
theorem fermionTotalSpinZ_mulVec_occMonomial_alphaSpinOcc (K : ℕ) (ν : ℝ)
    (s : Fin (K + 1) → Fin 2) :
    (fermionTotalSpinZ (2 * K + 1)).mulVec (occMonomial K ν (flatBandAlphaSpinOcc K s))
      = (∑ p : Fin (K + 1), flatBandSpinCharge (s p)) •
        occMonomial K ν (flatBandAlphaSpinOcc K s) := by
  rw [fermionTotalSpinZ_mulVec_occMonomial, occFinset_alphaSpinOcc_spinCharge_sum]

/-- The basis vector at an `α` index is the `ℂ`-valued single-particle state `α_p`. -/
theorem flatBandBasis_inl (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    flatBandBasis K ν (Sum.inl p) = flatBandAlphaC K ν p := by
  have hb : ⇑(flatBandBasis K ν) = Sum.elim (flatBandAlphaC K ν) (flatBandBetaC K ν) := by
    unfold flatBandBasis; exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  rw [hb, Sum.elim_inl]

/-- The `α_p` amplitude at the shared internal site `int(p)` is `−ν`. -/
theorem flatBandBasis_inl_deltaInternalSite_self (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    flatBandBasis K ν (Sum.inl p) (deltaInternalSite K p) = (-(ν : ℝ) : ℂ) := by
  rw [flatBandBasis_inl, flatBandAlphaC, flatBandAlpha_deltaInternalSite, if_pos (Or.inl rfl)]
  push_cast; ring

/-- The neighbouring `α_{p+1}` amplitude at the shared internal site `int(p)` is also `−ν`
(`int(p)` is the bond between orbitals `p` and `p+1`). -/
theorem flatBandBasis_inl_deltaInternalSite_succ (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    flatBandBasis K ν (Sum.inl (p + 1)) (deltaInternalSite K p) = (-(ν : ℝ) : ℂ) := by
  rw [flatBandBasis_inl, flatBandAlphaC, flatBandAlpha_deltaInternalSite,
    if_pos (Or.inr (by rw [add_sub_cancel_right]))]
  push_cast; ring

/-- **The site annihilation peels a leading mode of matching spin at orbital `r`.**  If no other
mode of `rest` is a spin-`σ` mode supported at `int(p)`, then `ĉ_{int(p),σ}` removes the head
`(inl r, σ)` with the single-particle amplitude `α_r(int p)`:
`ĉ_{int(p),σ}·monomial((inl r, σ) :: rest) = α_r(int p) · monomial(rest)`. -/
theorem flatBand_siteAnnihilation_head (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2)) (r : Fin (K + 1))
    (σ : Fin 2) (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 x = 0 ∨ q.2 ≠ σ) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1)
        (spinfulIndex (2 * K + 1) x σ)).mulVec
        (flatBandModeMonomial K ν ((Sum.inl r, σ) :: rest))
      = flatBandBasis K ν (Sum.inl r) x • flatBandModeMonomial K ν rest := by
  rw [flatBand_siteAnnihilation_peel_modeMonomial]
  change ∑ i : Fin (rest.length + 1),
      flatBandModePeelTerm K ν x σ ((Sum.inl r, σ) :: rest) i = _
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · simp only [flatBandModePeelTerm, List.get_cons_zero, List.eraseIdx_cons_zero, Fin.val_zero,
      pow_zero, one_smul]
    rw [if_true]
  · simp only [flatBandModePeelTerm, List.get_cons_succ', List.eraseIdx_cons_succ, Fin.val_succ]
    rcases hrest (rest.get i) (List.get_mem rest i) with h0 | hne
    · rw [h0, ite_self]; simp
    · rw [if_neg hne]; simp

/-- **The double annihilation on a two-`α`-head monomial.**  If `rest` has no mode supported at
`int(p)`, then `ĉ_{int(p)↓} ĉ_{int(p)↑}` removes the leading up head `(inl r₁, ↑)` and down head
`(inl r₂, ↓)`, leaving `α_{r₁}(int p) · α_{r₂}(int p) · monomial(rest)`. -/
theorem flatBand_cDownUp_two_head (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2)) (r₁ r₂ : Fin (K + 1))
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 x = 0) :
    (cDownUp K x).mulVec
        (flatBandModeMonomial K ν
          ((Sum.inl r₁, (0 : Fin 2)) :: (Sum.inl r₂, (1 : Fin 2)) :: rest))
      = (flatBandBasis K ν (Sum.inl r₁) x *
          flatBandBasis K ν (Sum.inl r₂) x) •
        flatBandModeMonomial K ν rest := by
  rw [cDownUp, ← Matrix.mulVec_mulVec,
    flatBand_siteAnnihilation_head K ν x r₁ 0 ((Sum.inl r₂, (1 : Fin 2)) :: rest)
      (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inr (show (1 : Fin 2) ≠ 0 by decide)
        · exact Or.inl (hrest q hq')),
    Matrix.mulVec_smul,
    flatBand_siteAnnihilation_head K ν x r₂ 1 rest (fun q hq => Or.inl (hrest q hq)), smul_smul]

/-- **Canonical `(↑,↓)` two-overlap monomial:** `ĉ_{int(p)↓} ĉ_{int(p)↑}` on
`(inl p, ↑) :: (inl(p+1), ↓) :: rest` gives `+ν² · monomial(rest)`. -/
theorem flatBand_cDownUp_canonical (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 (deltaInternalSite K p) = 0) :
    (cDownUp K (deltaInternalSite K p)).mulVec
        (flatBandModeMonomial K ν
          ((Sum.inl p, (0 : Fin 2)) :: (Sum.inl (p + 1), (1 : Fin 2)) :: rest))
      = (((ν : ℝ) : ℂ)) ^ 2 • flatBandModeMonomial K ν rest := by
  rw [flatBand_cDownUp_two_head K ν (deltaInternalSite K p) p (p + 1) rest hrest,
    flatBandBasis_inl_deltaInternalSite_self, flatBandBasis_inl_deltaInternalSite_succ]
  congr 1
  ring

/-- **Swapped `(↓,↑)` two-overlap monomial:** `ĉ_{int(p)↓} ĉ_{int(p)↑}` on
`(inl p, ↓) :: (inl(p+1), ↑) :: rest` gives `−ν² · monomial(rest)` — the opposite sign from the
canonical assignment (one extra Koszul transposition). -/
theorem flatBand_cDownUp_swap (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 (deltaInternalSite K p) = 0) :
    (cDownUp K (deltaInternalSite K p)).mulVec
        (flatBandModeMonomial K ν
          ((Sum.inl p, (1 : Fin 2)) :: (Sum.inl (p + 1), (0 : Fin 2)) :: rest))
      = (-(((ν : ℝ) : ℂ)) ^ 2) • flatBandModeMonomial K ν rest := by
  rw [show flatBandModeMonomial K ν
        ((Sum.inl p, (1 : Fin 2)) :: (Sum.inl (p + 1), (0 : Fin 2)) :: rest)
      = -flatBandModeMonomial K ν
        ((Sum.inl (p + 1), (0 : Fin 2)) :: (Sum.inl p, (1 : Fin 2)) :: rest) from by
      rw [flatBandModeMonomial_swap], Matrix.mulVec_neg,
    flatBand_cDownUp_two_head K ν (deltaInternalSite K p) (p + 1) p rest hrest,
    flatBandBasis_inl_deltaInternalSite_self, flatBandBasis_inl_deltaInternalSite_succ]
  rw [← neg_smul]
  congr 1
  ring

/-- **The `α`-spin occupation list, with the overlapping pair pulled to the front.**  For
`s p = ↑`, `s (p+1) = ↓` the occupation list is a permutation of `(inl p, ↑) :: (inl(p+1), ↓) ::
rest`, where `rest` is the rest of the occupied modes (the other orbitals, shared with the spin-swap
of `s`). -/
theorem flatBandAlphaSpinOcc_toList_perm (K : ℕ) (s : Fin (K + 1) → Fin 2) (p : Fin (K + 1))
    (hsp : s p = 0) (hsp1 : s (p + 1) = 1) (hp1 : p + 1 ≠ p) :
    (occFinset (flatBandAlphaSpinOcc K s)).toList.Perm
      ((Sum.inl p, (0 : Fin 2)) :: (Sum.inl (p + 1), (1 : Fin 2)) ::
        (((occFinset (flatBandAlphaSpinOcc K s)).erase (Sum.inl p, (0 : Fin 2))).erase
          (Sum.inl (p + 1), (1 : Fin 2))).toList) := by
  classical
  set occ := occFinset (flatBandAlphaSpinOcc K s) with hocc
  set a : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 := (Sum.inl p, (0 : Fin 2)) with ha
  set b : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 := (Sum.inl (p + 1), (1 : Fin 2)) with hb
  have hmem0 : a ∈ occ := (mem_occFinset_alphaSpinOcc s _).mpr ⟨p, by rw [ha, hsp]⟩
  have hne : b ≠ a := fun h => hp1 (Sum.inl_injective (congrArg Prod.fst h))
  have hmem1 : b ∈ occ.erase a :=
    Finset.mem_erase.mpr ⟨hne, (mem_occFinset_alphaSpinOcc s _).mpr ⟨p + 1, by rw [hb, hsp1]⟩⟩
  have h1 : occ.toList.Perm (a :: (occ.erase a).toList) := by
    have h := Finset.toList_insert (Finset.notMem_erase a occ)
    rwa [Finset.insert_erase hmem0] at h
  have h2 : (occ.erase a).toList.Perm (b :: ((occ.erase a).erase b).toList) := by
    have h := Finset.toList_insert (Finset.notMem_erase b (occ.erase a))
    rwa [Finset.insert_erase hmem1] at h
  exact h1.trans (h2.cons _)

/-- Moving one leading creation past the next two negates twice (back to `+`):
`monomial(c::a::b::l) = monomial(a::b::c::l)`. -/
theorem flatBandModeMonomial_move_one_past_two (c a b : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    flatBandModeMonomial K ν (c :: a :: b :: l) = flatBandModeMonomial K ν (a :: b :: c :: l) := by
  rw [flatBandModeMonomial_swap a c (b :: l), ← flatBandModeCreation_mulVec_monomial a.1 a.2,
    flatBandModeMonomial_swap b c l, Matrix.mulVec_neg,
    flatBandModeCreation_mulVec_monomial a.1 a.2, neg_neg]

/-- **Moving a contiguous pair to the front of a monomial preserves it** (sign `+1`): pushing the
pair `a, b` leftward past the block `l₁` is `2·|l₁|` adjacent transpositions.  Hence
`monomial(l₁ ++ a :: b :: l₂) = monomial(a :: b :: (l₁ ++ l₂))`. -/
theorem flatBandModeMonomial_move_pair_front (a b : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)
    (l₁ l₂ : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    flatBandModeMonomial K ν (l₁ ++ a :: b :: l₂)
      = flatBandModeMonomial K ν (a :: b :: (l₁ ++ l₂)) := by
  induction l₁ with
  | nil => rfl
  | cons c l₁' ih =>
    rw [List.cons_append, ← flatBandModeCreation_mulVec_monomial c.1 c.2, ih,
      flatBandModeCreation_mulVec_monomial c.1 c.2,
      flatBandModeMonomial_move_one_past_two c a b (l₁' ++ l₂), List.cons_append]

/-- **The two-hole occupation config.**  `alphaSpinOcc s` with the `p` and `p+1` α-modes removed —
the common `(K-1)`-electron config reached by the double annihilation from both spin assignments of
the overlapping pair. -/
def flatBandAlphaTwoHoleOcc (K : ℕ) (s : Fin (K + 1) → Fin 2) (p : Fin (K + 1)) :
    (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2 :=
  fun q => if q.1 = Sum.inl p ∨ q.1 = Sum.inl (p + 1) then 0 else flatBandAlphaSpinOcc K s q

/-- The two-hole config is unchanged by swapping the spins of `p` and `p+1` (they are zeroed out;
the configs agree off `{p, p+1}`). -/
theorem flatBandAlphaTwoHoleOcc_swap_eq (K : ℕ) (s : Fin (K + 1) → Fin 2) (p : Fin (K + 1)) :
    flatBandAlphaTwoHoleOcc K (Function.update (Function.update s p 1) (p + 1) 0) p
      = flatBandAlphaTwoHoleOcc K s p := by
  funext q
  simp only [flatBandAlphaTwoHoleOcc]
  by_cases hq : q.1 = Sum.inl p ∨ q.1 = Sum.inl (p + 1)
  · rw [if_pos hq, if_pos hq]
  · rw [if_neg hq, if_neg hq]
    rw [not_or] at hq
    obtain ⟨hqp, hqp1⟩ := hq
    obtain ⟨m, σ⟩ := q
    cases m with
    | inr u => rfl
    | inl r =>
      have hrp : r ≠ p := fun h => hqp (by rw [h])
      have hrp1 : r ≠ p + 1 := fun h => hqp1 (by rw [h])
      simp only [flatBandAlphaSpinOcc_inl, Function.update_apply]
      rw [if_neg hrp1, if_neg hrp]

/-- The occupied modes of the two-hole config are those of `alphaSpinOcc s` minus the `p`, `p+1`
chosen-spin modes. -/
theorem occFinset_alphaTwoHoleOcc_eq (K : ℕ) (s : Fin (K + 1) → Fin 2) (p : Fin (K + 1)) :
    occFinset (flatBandAlphaTwoHoleOcc K s p)
      = ((occFinset (flatBandAlphaSpinOcc K s)).erase (Sum.inl p, s p)).erase
        (Sum.inl (p + 1), s (p + 1)) := by
  ext q
  rw [Finset.mem_erase, Finset.mem_erase, mem_occFinset_iff, mem_occFinset_iff]
  constructor
  · intro hq1
    simp only [flatBandAlphaTwoHoleOcc] at hq1
    by_cases h : q.1 = Sum.inl p ∨ q.1 = Sum.inl (p + 1)
    · rw [if_pos h] at hq1; exact absurd hq1 (by decide)
    · rw [if_neg h] at hq1
      rw [not_or] at h
      exact ⟨fun he => h.2 (by rw [he]), fun he => h.1 (by rw [he]), hq1⟩
  · rintro ⟨hne1, hne0, hmem⟩
    obtain ⟨r, hr⟩ := (mem_occFinset_alphaSpinOcc s q).mp ((mem_occFinset_iff _ q).mpr hmem)
    subst hr
    have hrp : r ≠ p := fun h => hne0 (by rw [h])
    have hrp1 : r ≠ p + 1 := fun h => hne1 (by rw [h])
    have hcond : ¬((Sum.inl r : Fin (K + 1) ⊕ Fin (K + 1)) = Sum.inl p ∨
        (Sum.inl r : Fin (K + 1) ⊕ Fin (K + 1)) = Sum.inl (p + 1)) := by
      rw [not_or]
      exact ⟨fun he => hrp (Sum.inl_injective he), fun he => hrp1 (Sum.inl_injective he)⟩
    simp only [flatBandAlphaTwoHoleOcc]
    rw [if_neg hcond, flatBandAlphaSpinOcc_inl, if_pos rfl]

/-- The canonical orbital-ordered list of occupied modes of an `α`-spin config:
`[(inl 0, s 0), (inl 1, s 1), …, (inl K, s K)]`. -/
def flatBandAlphaSpinList (K : ℕ) (s : Fin (K + 1) → Fin 2) :
    List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2) :=
  List.ofFn (fun q : Fin (K + 1) => (Sum.inl q, s q))

/-- **The canonical list splits with the adjacent overlapping pair `p, p+1` exposed.**  For
`p : Fin K` the orbitals `p` and `p+1` sit at consecutive positions `p, p+1` (no cycle wrap), so the
list is `take p ++ (inl p, s p) :: (inl(p+1), s(p+1)) :: drop (p+2)`. -/
theorem flatBandAlphaSpinList_split_adj (s : Fin (K + 1) → Fin 2) (p : Fin K) :
    flatBandAlphaSpinList K s =
      (flatBandAlphaSpinList K s).take p.val ++
        (Sum.inl p.castSucc, s p.castSucc) :: (Sum.inl p.succ, s p.succ) ::
        (flatBandAlphaSpinList K s).drop (p.val + 2) := by
  have hlen : (flatBandAlphaSpinList K s).length = K + 1 := List.length_ofFn
  have h1 : p.val < (flatBandAlphaSpinList K s).length := by rw [hlen]; omega
  have h2 : p.val + 1 < (flatBandAlphaSpinList K s).length := by rw [hlen]; omega
  have hc1 : (⟨p.val, by omega⟩ : Fin (K + 1)) = p.castSucc := Fin.ext rfl
  have hc2 : (⟨p.val + 1, by omega⟩ : Fin (K + 1)) = p.succ := Fin.ext rfl
  have e1 : (flatBandAlphaSpinList K s)[p.val]'h1 = (Sum.inl p.castSucc, s p.castSucc) := by
    simp only [flatBandAlphaSpinList, List.getElem_ofFn]
    rw [hc1]
  have e2 : (flatBandAlphaSpinList K s)[p.val + 1]'h2 = (Sum.inl p.succ, s p.succ) := by
    simp only [flatBandAlphaSpinList, List.getElem_ofFn]
    rw [hc2]
  conv_lhs => rw [← List.take_append_drop p.val (flatBandAlphaSpinList K s)]
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2, e1, e2]

/-- The canonical orbital list has no repeated mode. -/
theorem flatBandAlphaSpinList_nodup (s : Fin (K + 1) → Fin 2) :
    (flatBandAlphaSpinList K s).Nodup := by
  rw [flatBandAlphaSpinList]
  exact List.nodup_ofFn.mpr (fun a b h => Sum.inl_injective (congrArg Prod.fst h))

/-- **The non-pair part of the canonical list is `int(p)`-clean.**  Every mode outside the
overlapping pair `p, p+1` has zero single-particle amplitude at the shared internal site `int(p)`
(only `α_p` and `α_{p+1}` are supported there). -/
theorem flatBandAlphaSpinList_rest_clean (s : Fin (K + 1) → Fin 2) (p : Fin K) :
    ∀ m ∈ (flatBandAlphaSpinList K s).take p.val ++ (flatBandAlphaSpinList K s).drop (p.val + 2),
      flatBandBasis K ν m.1 (deltaInternalSite K p.castSucc) = 0 := by
  intro m hm
  have hsplit := flatBandAlphaSpinList_split_adj s p
  have hnd : (flatBandAlphaSpinList K s).Nodup := flatBandAlphaSpinList_nodup s
  rw [hsplit] at hnd
  -- a, b (the pair modes) are not in take ++ drop, by nodup
  obtain ⟨_, hcons, hdisj⟩ := List.nodup_append.mp hnd
  have hane : (Sum.inl p.castSucc, s p.castSucc) ∉
      (flatBandAlphaSpinList K s).take p.val ++ (flatBandAlphaSpinList K s).drop (p.val + 2) := by
    rw [List.mem_append, not_or]
    refine ⟨fun h => hdisj _ h _ List.mem_cons_self rfl, fun h => ?_⟩
    exact (List.nodup_cons.mp hcons).1 (List.mem_cons_of_mem _ h)
  have hbne : (Sum.inl p.succ, s p.succ) ∉
      (flatBandAlphaSpinList K s).take p.val ++ (flatBandAlphaSpinList K s).drop (p.val + 2) := by
    rw [List.mem_append, not_or]
    refine ⟨fun h => hdisj _ h _ (List.mem_cons_of_mem _ List.mem_cons_self) rfl, fun h => ?_⟩
    exact (List.nodup_cons.mp (List.nodup_cons.mp hcons).2).1 h
  -- m is some (inl r, s r); r ≠ p.castSucc, p.succ since m ≠ a, b
  have hmem : m ∈ flatBandAlphaSpinList K s := by
    rw [hsplit]
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr
        (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
  rw [flatBandAlphaSpinList, List.mem_ofFn] at hmem
  obtain ⟨r, rfl⟩ := hmem
  have hrp : r ≠ p.castSucc := fun h => hane (h ▸ hm)
  have hrp1 : r ≠ p.succ := fun h => hbne (h ▸ hm)
  rw [flatBandBasis_inl, flatBandAlphaC, flatBandAlpha_deltaInternalSite, if_neg,
    Complex.ofReal_zero]
  rintro (h | h)
  · exact hrp h.symm
  · apply hrp1
    -- h : p.castSucc = r - 1, decode the modular subtraction to r = p.succ
    have hv : (p.castSucc : Fin (K + 1)).val = (r - 1 : Fin (K + 1)).val := congrArg Fin.val h
    rw [Fin.val_castSucc, Fin.coe_sub_one] at hv
    by_cases hr0 : r = 0
    · rw [if_pos hr0] at hv; exact absurd hv (by have := p.isLt; omega)
    · rw [if_neg hr0] at hv
      have hrpos : 0 < r.val := Fin.pos_iff_ne_zero.mpr hr0
      exact Fin.ext (by rw [Fin.val_succ]; omega)

/-- For `p : Fin K` the successor orbital equals `p.castSucc + 1` inside `Fin (K + 1)`
(no wrap, since `p.castSucc < last`). -/
theorem flatBand_succ_eq_castSucc_add_one (p : Fin K) :
    (p.succ : Fin (K + 1)) = p.castSucc + 1 := by
  apply Fin.ext
  rw [Fin.val_add_one, if_neg (Fin.castSucc_lt_last p).ne, Fin.val_castSucc, Fin.val_succ]

/-- **Double-annihilation on the canonical α-monomial (aligned spins).**  When the overlapping pair
carries `(↑, ↓)` at orbitals `p, p+1`, `ĉ_↓ĉ_↑` at the shared internal site `int(p)` returns
`+ν²` times the canonical monomial with that pair removed. -/
theorem flatBand_cDownUp_alphaSpinList_canonical (s : Fin (K + 1) → Fin 2) (p : Fin K)
    (h0 : s p.castSucc = 0) (h1 : s p.succ = 1) :
    (cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (flatBandModeMonomial K ν (flatBandAlphaSpinList K s))
      = ((ν : ℝ) : ℂ) ^ 2 • flatBandModeMonomial K ν
          ((flatBandAlphaSpinList K s).take p.val
            ++ (flatBandAlphaSpinList K s).drop (p.val + 2)) := by
  nth_rewrite 1 [flatBandAlphaSpinList_split_adj s p]
  rw [flatBandModeMonomial_move_pair_front, h0, h1, flatBand_succ_eq_castSucc_add_one p]
  exact flatBand_cDownUp_canonical K ν p.castSucc _ (flatBandAlphaSpinList_rest_clean s p)

/-- **Double-annihilation on the canonical α-monomial (swapped spins).**  When the overlapping pair
carries `(↓, ↑)` at orbitals `p, p+1`, `ĉ_↓ĉ_↑` at `int(p)` returns `-ν²` times the canonical
monomial with that pair removed.  The relative sign vs. the aligned case is position-independent. -/
theorem flatBand_cDownUp_alphaSpinList_swap (s : Fin (K + 1) → Fin 2) (p : Fin K)
    (h0 : s p.castSucc = 1) (h1 : s p.succ = 0) :
    (cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (flatBandModeMonomial K ν (flatBandAlphaSpinList K s))
      = (-(((ν : ℝ) : ℂ)) ^ 2) • flatBandModeMonomial K ν
          ((flatBandAlphaSpinList K s).take p.val
            ++ (flatBandAlphaSpinList K s).drop (p.val + 2)) := by
  nth_rewrite 1 [flatBandAlphaSpinList_split_adj s p]
  rw [flatBandModeMonomial_move_pair_front, h0, h1, flatBand_succ_eq_castSucc_add_one p]
  exact flatBand_cDownUp_swap K ν p.castSucc _ (flatBandAlphaSpinList_rest_clean s p)

/-- The canonical orbital list is a permutation of the (arbitrary-order) occupation `toList`:
both enumerate the occupied modes `{(inl q, s q)}` without repetition. -/
theorem flatBandAlphaSpinList_perm_toList (s : Fin (K + 1) → Fin 2) :
    (flatBandAlphaSpinList K s).Perm (occFinset (flatBandAlphaSpinOcc K s)).toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq (flatBandAlphaSpinList_nodup s)
    (Finset.nodup_toList _)
  rw [Finset.toList_toFinset]
  ext x
  rw [List.mem_toFinset, flatBandAlphaSpinList, List.mem_ofFn, mem_occFinset_alphaSpinOcc]
  exact ⟨fun ⟨q, hq⟩ => ⟨q, hq.symm⟩, fun ⟨p, hp⟩ => ⟨p, hp.symm⟩⟩

/-- **The occupation monomial is a nonzero scalar multiple of the canonical-list monomial.**  Since
`occMonomial` is built from the `toList`-opaque enumeration, it differs from the orbital-ordered
canonical monomial only by a nonzero fermionic reordering scalar `z`.  This makes the canonical
α-monomials nonzero multiples of distinct basis vectors, hence linearly independent. -/
theorem occMonomial_alphaSpinOcc_eq_smul_canonical (s : Fin (K + 1) → Fin 2) :
    ∃ z : ℂ, z ≠ 0 ∧ occMonomial K ν (flatBandAlphaSpinOcc K s)
      = z • flatBandModeMonomial K ν (flatBandAlphaSpinList K s) := by
  rw [occMonomial]
  exact flatBandModeMonomial_perm (flatBandAlphaSpinList_perm_toList s).symm

/-- **Site annihilation kills a monomial with no matching-spin mode at the site.**  If every mode of
`M` either has zero amplitude at `x` or carries the wrong spin, then `ĉ_{x,σ}` annihilates the
monomial. -/
theorem flatBand_siteAnnihilation_eq_zero (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2)) (σ : Fin 2)
    (M : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hM : ∀ q ∈ M, flatBandBasis K ν q.1 x = 0 ∨ q.2 ≠ σ) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)).mulVec
        (flatBandModeMonomial K ν M) = 0 := by
  rw [flatBand_siteAnnihilation_peel_modeMonomial]
  apply Finset.sum_eq_zero
  intro i _
  simp only [flatBandModePeelTerm]
  rcases hM (M.get i) (List.get_mem M i) with h0 | hne
  · rw [h0, ite_self, zero_smul, smul_zero]
  · rw [if_neg hne, zero_smul, smul_zero]

/-- **Double annihilation on a same-spin two-head monomial vanishes.**  If both leading heads carry
the same spin `σ` and `rest` is `int(p)`-clean, then `ĉ_{int(p)↓} ĉ_{int(p)↑}` cannot extract both
an up and a down electron at `int(p)`, so the result is zero.  (One factor annihilates the state
outright; for `σ = ↑` we first anticommute the two annihilations.) -/
theorem flatBand_cDownUp_two_head_same_spin (K : ℕ) (ν : ℝ) (p r₁ r₂ : Fin (K + 1)) (σ : Fin 2)
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 (deltaInternalSite K p) = 0) :
    (cDownUp K (deltaInternalSite K p)).mulVec
        (flatBandModeMonomial K ν ((Sum.inl r₁, σ) :: (Sum.inl r₂, σ) :: rest)) = 0 := by
  fin_cases σ
  · rw [cDownUp,
      eq_neg_of_add_eq_zero_left (fermionMultiAnnihilation_anticomm_of_ne
        (spinfulIndex_up_ne_down (2 * K + 1) (deltaInternalSite K p) (deltaInternalSite K p)).symm),
      Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      flatBand_siteAnnihilation_eq_zero K ν (deltaInternalSite K p) 1 _ ?_,
      Matrix.mulVec_zero, neg_zero]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq1
    · exact Or.inr (show (0 : Fin 2) ≠ 1 by decide)
    · rcases List.mem_cons.mp hq1 with rfl | hq2
      · exact Or.inr (show (0 : Fin 2) ≠ 1 by decide)
      · exact Or.inl (hrest q hq2)
  · rw [cDownUp, ← Matrix.mulVec_mulVec,
      flatBand_siteAnnihilation_eq_zero K ν (deltaInternalSite K p) 0 _ ?_, Matrix.mulVec_zero]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq1
    · exact Or.inr (show (1 : Fin 2) ≠ 0 by decide)
    · rcases List.mem_cons.mp hq1 with rfl | hq2
      · exact Or.inr (show (1 : Fin 2) ≠ 0 by decide)
      · exact Or.inl (hrest q hq2)

/-- **Double annihilation on the canonical α-monomial (same spins) vanishes.**  When the overlapping
pair `p, p+1` carries the same spin, `ĉ_↓ĉ_↑` at `int(p)` returns zero. -/
theorem flatBand_cDownUp_alphaSpinList_same_spin (s : Fin (K + 1) → Fin 2) (p : Fin K)
    (hsame : s p.castSucc = s p.succ) :
    (cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (flatBandModeMonomial K ν (flatBandAlphaSpinList K s)) = 0 := by
  nth_rewrite 1 [flatBandAlphaSpinList_split_adj s p]
  rw [flatBandModeMonomial_move_pair_front, hsame]
  exact flatBand_cDownUp_two_head_same_spin K ν p.castSucc p.castSucc p.succ (s p.succ) _
    (flatBandAlphaSpinList_rest_clean s p)

/-- The `α_q` amplitude at its own external site `ext(q)` is `1` (only `α_q` is supported at
`ext(q)`). -/
theorem flatBandBasis_inl_deltaExternalSite_self (K : ℕ) (ν : ℝ) (q : Fin (K + 1)) :
    flatBandBasis K ν (Sum.inl q) (deltaExternalSite K q) = 1 := by
  rw [flatBandBasis_inl, flatBandAlphaC, flatBandAlpha_deltaExternalSite, if_pos rfl]
  norm_num

/-- **Double annihilation at an external site detects orbital double occupancy.**  Since only `α_q`
is supported at `ext(q)` (amplitude `1`), `ĉ_{ext(q)↓} ĉ_{ext(q)↑}` on a monomial whose two leading
heads are both at orbital `q` (with opposite spins) and whose `rest` is `ext(q)`-clean returns
`monomial(rest)`. -/
theorem flatBand_cDownUp_extSite_double (K : ℕ) (ν : ℝ) (q : Fin (K + 1))
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q' ∈ rest, flatBandBasis K ν q'.1 (deltaExternalSite K q) = 0) :
    (cDownUp K (deltaExternalSite K q)).mulVec
        (flatBandModeMonomial K ν
          ((Sum.inl q, (0 : Fin 2)) :: (Sum.inl q, (1 : Fin 2)) :: rest))
      = flatBandModeMonomial K ν rest := by
  rw [flatBand_cDownUp_two_head K ν (deltaExternalSite K q) q q rest hrest,
    flatBandBasis_inl_deltaExternalSite_self, one_mul, one_smul]

/-- **Pulling two occupied modes to the front of an occupation `toList`.**  For any config `f` and
two distinct occupied modes `a, b`, the `toList` enumeration is a permutation of `a :: b :: r`,
where `r` lists the remaining occupied modes.  (Generalises `flatBandAlphaSpinOcc_toList_perm` to an
arbitrary config and mode pair; used for both the external double-occupancy and the internal
coefficient readings.) -/
theorem occFinset_toList_perm_two_front
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (a b : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)
    (ha : a ∈ occFinset f) (hb : b ∈ (occFinset f).erase a) :
    (occFinset f).toList.Perm
      (a :: b :: (((occFinset f).erase a).erase b).toList) := by
  classical
  have h1 : (occFinset f).toList.Perm (a :: ((occFinset f).erase a).toList) := by
    have h := Finset.toList_insert (Finset.notMem_erase a (occFinset f))
    rwa [Finset.insert_erase ha] at h
  have h2 : ((occFinset f).erase a).toList.Perm
      (b :: (((occFinset f).erase a).erase b).toList) := by
    have h := Finset.toList_insert (Finset.notMem_erase b ((occFinset f).erase a))
    rwa [Finset.insert_erase hb] at h
  exact h1.trans (h2.cons _)

/-- The `α_{q'}` amplitude at external site `ext(q₀)` is `1` if `q' = q₀`, else `0`. -/
theorem flatBandBasis_inl_deltaExternalSite (K : ℕ) (ν : ℝ) (q' q₀ : Fin (K + 1)) :
    flatBandBasis K ν (Sum.inl q') (deltaExternalSite K q₀) = if q₀ = q' then 1 else 0 := by
  rw [flatBandBasis_inl, flatBandAlphaC, flatBandAlpha_deltaExternalSite]
  split_ifs <;> norm_num

/-- **A single annihilation at an external site kills a β-free monomial missing that mode.**  For a
β-free config `f` not occupying `(inl q₀, σ)`, `ĉ_{ext(q₀),σ}` annihilates `occMonomial f` (the only
mode reaching `ext(q₀)` is `α_{q₀}`, which carries the missing spin). -/
theorem flatBand_siteAnnihilation_ext_betaFree_eq_zero (K : ℕ) (ν : ℝ) (q₀ : Fin (K + 1))
    (σ : Fin 2) (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r)
    (hmiss : (Sum.inl q₀, σ) ∉ occFinset f) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1)
        (spinfulIndex (2 * K + 1) (deltaExternalSite K q₀) σ)).mulVec (occMonomial K ν f) = 0 := by
  rw [occMonomial]
  apply flatBand_siteAnnihilation_eq_zero
  intro q' hq'
  rw [Finset.mem_toList] at hq'
  obtain ⟨r, hr⟩ := hbf q' hq'
  rw [hr, flatBandBasis_inl_deltaExternalSite]
  by_cases hrq : q₀ = r
  · refine Or.inr (fun hσ => hmiss ?_)
    have : (Sum.inl q₀, σ) = q' := Prod.ext (by rw [hr, hrq]) hσ.symm
    rwa [this]
  · exact Or.inl (if_neg hrq)

/-- **External double annihilation vanishes on a β-free non-doubly-occupied config.**  If a β-free
config `f` does not doubly occupy orbital `q₀` (it misses one of the two spins), then
`ĉ_{ext(q₀)↓} ĉ_{ext(q₀)↑}` annihilates `occMonomial f`. -/
theorem flatBand_cDownUp_ext_betaFree_eq_zero_of_not_double (K : ℕ) (ν : ℝ) (q₀ : Fin (K + 1))
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r)
    (hnd : (Sum.inl q₀, (0 : Fin 2)) ∉ occFinset f ∨ (Sum.inl q₀, (1 : Fin 2)) ∉ occFinset f) :
    (cDownUp K (deltaExternalSite K q₀)).mulVec (occMonomial K ν f) = 0 := by
  rcases hnd with h0 | h1
  · rw [cDownUp, ← Matrix.mulVec_mulVec,
      flatBand_siteAnnihilation_ext_betaFree_eq_zero K ν q₀ 0 f hbf h0, Matrix.mulVec_zero]
  · rw [cDownUp,
      eq_neg_of_add_eq_zero_left (fermionMultiAnnihilation_anticomm_of_ne
        (spinfulIndex_up_ne_down (2 * K + 1) (deltaExternalSite K q₀)
          (deltaExternalSite K q₀)).symm),
      Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      flatBand_siteAnnihilation_ext_betaFree_eq_zero K ν q₀ 1 f hbf h1, Matrix.mulVec_zero,
      neg_zero]

/-- **External double annihilation on a β-free doubly-occupied config.**  If a β-free config `f`
doubly occupies orbital `q₀`, then `ĉ_{ext(q₀)↓} ĉ_{ext(q₀)↑}` removes that pair, returning a
nonzero scalar multiple of the monomial of the remaining (`q₀`-pair-erased) modes. -/
theorem flatBand_cDownUp_ext_betaFree_double (K : ℕ) (ν : ℝ) (q₀ : Fin (K + 1))
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r)
    (h0 : (Sum.inl q₀, (0 : Fin 2)) ∈ occFinset f)
    (h1 : (Sum.inl q₀, (1 : Fin 2)) ∈ occFinset f) :
    ∃ z : ℂ, z ≠ 0 ∧ (cDownUp K (deltaExternalSite K q₀)).mulVec (occMonomial K ν f)
      = z • flatBandModeMonomial K ν
          (((occFinset f).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1)).toList := by
  have hb : (Sum.inl q₀, (1 : Fin 2)) ∈ (occFinset f).erase (Sum.inl q₀, 0) :=
    Finset.mem_erase.mpr ⟨by simp, h1⟩
  obtain ⟨z, hz0, hz⟩ := flatBandModeMonomial_perm (occFinset_toList_perm_two_front f _ _ h0 hb)
  refine ⟨z, hz0, ?_⟩
  rw [occMonomial, hz, Matrix.mulVec_smul, flatBand_cDownUp_extSite_double K ν q₀ _ ?_]
  intro q' hq'
  rw [Finset.mem_toList, Finset.mem_erase, Finset.mem_erase] at hq'
  obtain ⟨hqb, hqa, hqf⟩ := hq'
  obtain ⟨r, hr⟩ := hbf q' hqf
  rw [hr, flatBandBasis_inl_deltaExternalSite, if_neg ?_]
  intro hq0r
  have hlt := q'.2.isLt
  have hd : q'.2 = 0 ∨ q'.2 = 1 := by
    rcases (by omega : q'.2.val = 0 ∨ q'.2.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hd with h | h
  · exact hqa (Prod.ext (by rw [hr, hq0r]) h)
  · exact hqb (Prod.ext (by rw [hr, hq0r]) h)

/-- Setting a mode to unoccupied erases it from the occupation finset. -/
theorem occFinset_update_zero (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    {q : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2} :
    occFinset (Function.update f q 0) = (occFinset f).erase q := by
  ext q'
  simp only [occFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    Function.update_apply]
  by_cases h : q' = q
  · subst h; simp
  · simp [h]

/-- The canonical orbital list's `toFinset` is the occupation finset of the α-spin config. -/
theorem flatBandAlphaSpinList_toFinset (s : Fin (K + 1) → Fin 2) :
    (flatBandAlphaSpinList K s).toFinset = occFinset (flatBandAlphaSpinOcc K s) := by
  ext x
  rw [List.mem_toFinset, flatBandAlphaSpinList, List.mem_ofFn, mem_occFinset_alphaSpinOcc]
  exact ⟨fun ⟨q, hq⟩ => ⟨q, hq.symm⟩, fun ⟨p, hp⟩ => ⟨p, hp.symm⟩⟩

/-- **The non-pair part of the canonical list permutes the two-hole occupation `toList`.**  Both
enumerate the occupied modes of `αs` with the `p, p+1` pair removed. -/
theorem flatBandAlphaSpinList_rest_perm_twoHole (s : Fin (K + 1) → Fin 2) (p : Fin K) :
    ((flatBandAlphaSpinList K s).take p.val
        ++ (flatBandAlphaSpinList K s).drop (p.val + 2)).Perm
      (occFinset (flatBandAlphaTwoHoleOcc K s p.castSucc)).toList := by
  have hnd := flatBandAlphaSpinList_nodup s
  rw [flatBandAlphaSpinList_split_adj s p] at hnd
  obtain ⟨htnd, hcons, hdisj⟩ := List.nodup_append.mp hnd
  have hdnd : ((flatBandAlphaSpinList K s).drop (p.val + 2)).Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hcons).2).2
  have hrnd : ((flatBandAlphaSpinList K s).take p.val
      ++ (flatBandAlphaSpinList K s).drop (p.val + 2)).Nodup :=
    List.nodup_append.mpr ⟨htnd, hdnd, fun x hx y hy =>
      hdisj x hx y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))⟩
  have ha_rest : (Sum.inl p.castSucc, s p.castSucc) ∉
      (flatBandAlphaSpinList K s).take p.val ++ (flatBandAlphaSpinList K s).drop (p.val + 2) := by
    rw [List.mem_append, not_or]
    exact ⟨fun h => hdisj _ h _ List.mem_cons_self rfl,
      fun h => (List.nodup_cons.mp hcons).1 (List.mem_cons_of_mem _ h)⟩
  have hb_rest : (Sum.inl p.succ, s p.succ) ∉
      (flatBandAlphaSpinList K s).take p.val ++ (flatBandAlphaSpinList K s).drop (p.val + 2) := by
    rw [List.mem_append, not_or]
    exact ⟨fun h => hdisj _ h _ (List.mem_cons_of_mem _ List.mem_cons_self) rfl,
      fun h => (List.nodup_cons.mp (List.nodup_cons.mp hcons).2).1 h⟩
  apply List.perm_of_nodup_nodup_toFinset_eq hrnd (Finset.nodup_toList _)
  rw [Finset.toList_toFinset, occFinset_alphaTwoHoleOcc_eq, ← flatBand_succ_eq_castSucc_add_one p]
  ext x
  rw [List.mem_toFinset, Finset.mem_erase, Finset.mem_erase]
  constructor
  · intro hx
    refine ⟨fun he => hb_rest (he ▸ hx), fun he => ha_rest (he ▸ hx), ?_⟩
    rw [← flatBandAlphaSpinList_toFinset, List.mem_toFinset, flatBandAlphaSpinList_split_adj s p]
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
  · rintro ⟨hxb, hxa, hxocc⟩
    rw [← flatBandAlphaSpinList_toFinset, List.mem_toFinset, flatBandAlphaSpinList_split_adj s p]
      at hxocc
    rcases List.mem_append.mp hxocc with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · rcases List.mem_cons.mp h with rfl | h'
      · exact absurd rfl hxa
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact absurd rfl hxb
        · exact List.mem_append.mpr (Or.inr h'')

/-- **Internal double annihilation on a canonical-oriented α-config.**  For an α-spin config `s`
with `(↑, ↓)` on the overlapping pair `p, p+1`, `ĉ_{int(p)↓} ĉ_{int(p)↑}` returns a nonzero scalar
multiple of the two-hole occupation monomial. -/
theorem flatBand_cDownUp_int_occMonomial_canonical (hν : 0 < ν) (s : Fin (K + 1) → Fin 2)
    (p : Fin K) (h0 : s p.castSucc = 0) (h1 : s p.succ = 1) :
    ∃ z : ℂ, z ≠ 0 ∧ (cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s))
      = z • occMonomial K ν (flatBandAlphaTwoHoleOcc K s p.castSucc) := by
  obtain ⟨z1, hz1, hz1eq⟩ := occMonomial_alphaSpinOcc_eq_smul_canonical s
  obtain ⟨z2, hz2, hz2eq⟩ := flatBandModeMonomial_perm (flatBandAlphaSpinList_rest_perm_twoHole s p)
  refine ⟨z1 * (((ν : ℝ) : ℂ)) ^ 2 * z2,
    mul_ne_zero (mul_ne_zero hz1 (pow_ne_zero _ (by exact_mod_cast ne_of_gt hν))) hz2, ?_⟩
  rw [hz1eq, Matrix.mulVec_smul, flatBand_cDownUp_alphaSpinList_canonical s p h0 h1, smul_smul,
    hz2eq, ← occMonomial, smul_smul]

/-- **Internal double annihilation on a swap-oriented α-config.**  For `(↓, ↑)` on the pair
`p, p+1`, `ĉ_{int(p)↓} ĉ_{int(p)↑}` returns a nonzero scalar multiple of the two-hole monomial. -/
theorem flatBand_cDownUp_int_occMonomial_swap (hν : 0 < ν) (s : Fin (K + 1) → Fin 2)
    (p : Fin K) (h0 : s p.castSucc = 1) (h1 : s p.succ = 0) :
    ∃ z : ℂ, z ≠ 0 ∧ (cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s))
      = z • occMonomial K ν (flatBandAlphaTwoHoleOcc K s p.castSucc) := by
  obtain ⟨z1, hz1, hz1eq⟩ := occMonomial_alphaSpinOcc_eq_smul_canonical s
  obtain ⟨z2, hz2, hz2eq⟩ := flatBandModeMonomial_perm (flatBandAlphaSpinList_rest_perm_twoHole s p)
  refine ⟨z1 * (-(((ν : ℝ) : ℂ)) ^ 2) * z2,
    mul_ne_zero (mul_ne_zero hz1 (neg_ne_zero.mpr (pow_ne_zero _
      (by exact_mod_cast ne_of_gt hν)))) hz2, ?_⟩
  rw [hz1eq, Matrix.mulVec_smul, flatBand_cDownUp_alphaSpinList_swap s p h0 h1, smul_smul,
    hz2eq, ← occMonomial, smul_smul]

/-- **Internal double annihilation on a same-spin α-config vanishes.** -/
theorem flatBand_cDownUp_int_occMonomial_same (s : Fin (K + 1) → Fin 2) (p : Fin K)
    (hsame : s p.castSucc = s p.succ) :
    (cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s)) = 0 := by
  obtain ⟨z1, _, hz1eq⟩ := occMonomial_alphaSpinOcc_eq_smul_canonical s
  rw [hz1eq, Matrix.mulVec_smul, flatBand_cDownUp_alphaSpinList_same_spin s p hsame, smul_zero]

/-- **A β-free, non-doubly-occupied, half-filled config is an α-spin config.**  Its occupation set
equals that of `αs'` for `s' q := (the spin occupied at orbital q)`.  Subset (each occupied mode is
at its `s'`-spin, by no double occupancy) plus equal cardinality `K+1` forces equality. -/
theorem flatBand_occFinset_eq_alphaSpinOcc_of_betaFree_noDouble
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r)
    (hnd : ∀ q : Fin (K + 1),
      ¬((Sum.inl q, (0 : Fin 2)) ∈ occFinset f ∧ (Sum.inl q, (1 : Fin 2)) ∈ occFinset f))
    (hcard : (occFinset f).card = K + 1) :
    occFinset f = occFinset (flatBandAlphaSpinOcc K
      (fun q => if (Sum.inl q, (0 : Fin 2)) ∈ occFinset f then 0 else 1)) := by
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_)
    (by rw [occFinset_alphaSpinOcc_card, hcard])
  obtain ⟨r, hr⟩ := hbf x hx
  rw [mem_occFinset_alphaSpinOcc]
  refine ⟨r, Prod.ext hr ?_⟩
  change x.2 = if (Sum.inl r, (0 : Fin 2)) ∈ occFinset f then (0 : Fin 2) else 1
  have hlt := x.2.isLt
  by_cases h0 : (Sum.inl r, (0 : Fin 2)) ∈ occFinset f
  · rw [if_pos h0]
    by_contra hne
    have hx1 : x.2 = 1 := by
      rcases (by omega : x.2.val = 0 ∨ x.2.val = 1) with h | h
      · exact absurd (Fin.ext h) hne
      · exact Fin.ext h
    have hxe : x = (Sum.inl r, (1 : Fin 2)) := Prod.ext hr hx1
    rw [hxe] at hx
    exact hnd r ⟨h0, hx⟩
  · rw [if_neg h0]
    have hx0 : x.2 ≠ 0 := by
      intro hc
      have hxe : x = (Sum.inl r, (0 : Fin 2)) := Prod.ext hr hc
      rw [hxe] at hx
      exact h0 hx
    rcases (by omega : x.2.val = 0 ∨ x.2.val = 1) with h | h
    · exact absurd (Fin.ext h) hx0
    · exact Fin.ext h

/-- **Only matching-two-hole opposite-spin α-configs survive the internal coordinate read.**  If the
two-hole coordinate of `ĉ_{int(p)↓}ĉ_{int(p)↑}` applied to `occMonomial(αs')` is nonzero, then `s'`
carries opposite pair spins and its two-hole config matches that of `s`. -/
theorem flatBand_cDownUp_int_occMonomial_repr_ne_zero_imp (hν : 0 < ν)
    (s s' : Fin (K + 1) → Fin 2) (p : Fin K)
    (hne : (flatBandOccBasis K ν).repr
        ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec
          (occMonomial K ν (flatBandAlphaSpinOcc K s'))) (flatBandAlphaTwoHoleOcc K s p.castSucc)
      ≠ 0) :
    s' p.castSucc ≠ s' p.succ ∧
      flatBandAlphaTwoHoleOcc K s' p.castSucc = flatBandAlphaTwoHoleOcc K s p.castSucc := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  by_cases hsame : s' p.castSucc = s' p.succ
  · exact absurd (by rw [flatBand_cDownUp_int_occMonomial_same s' p hsame, map_zero,
      Finsupp.zero_apply]) hne
  refine ⟨hsame, ?_⟩
  by_contra htw
  apply hne
  rcases hdich (s' p.castSucc) with h0 | h1
  · have h1 : s' p.succ = 1 := by
      rcases hdich (s' p.succ) with h | h
      · exact absurd (h0.trans h.symm) hsame
      · exact h
    obtain ⟨z, _, hz⟩ := flatBand_cDownUp_int_occMonomial_canonical hν s' p h0 h1
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_neg htw, mul_zero]
  · have h0 : s' p.succ = 0 := by
      rcases hdich (s' p.succ) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hsame
    obtain ⟨z, _, hz⟩ := flatBand_cDownUp_int_occMonomial_swap hν s' p h1 h0
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_neg htw, mul_zero]

/-- An occupation config (a `Fin 2`-valued function) is determined by its occupation finset. -/
theorem config_eq_of_occFinset_eq (f g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (h : occFinset f = occFinset g) : f = g := by
  funext q
  have hiff := Finset.ext_iff.mp h q
  simp only [occFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
  have hf2 := (f q).isLt
  have hg2 := (g q).isLt
  by_cases hf : f q = 1
  · rw [hf, hiff.mp hf]
  · have hg : g q ≠ 1 := fun hg => hf (hiff.mpr hg)
    rw [Fin.ext (by have := Fin.val_ne_of_ne hf; omega : (f q).val = (g q).val)]

/-- The occupation monomial depends only on the occupation finset. -/
theorem occMonomial_congr (f g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (h : occFinset f = occFinset g) :
    occMonomial K ν f = occMonomial K ν g := by
  rw [occMonomial, occMonomial, h]

/-- **Two-hole configs with opposite pair spins coincide only for `s` and its pair-swap.**  If the
two-hole occupations of `s'` and `s` agree and `s'` carries opposite spins on the pair `p, p+1`,
then `s'` is `s` itself or `s` with the pair spins swapped (it must agree with `s` off the pair). -/
theorem flatBand_alphaTwoHoleOcc_eq_imp (s s' : Fin (K + 1) → Fin 2) (p : Fin K)
    (hs0 : s p.castSucc = 0) (hs1 : s p.succ = 1) (hopp : s' p.castSucc ≠ s' p.succ)
    (heq : flatBandAlphaTwoHoleOcc K s' p.castSucc = flatBandAlphaTwoHoleOcc K s p.castSucc) :
    s' = s ∨ s' = Function.update (Function.update s p.castSucc 1) p.succ 0 := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hne : p.castSucc ≠ p.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hoff : ∀ q, q ≠ p.castSucc → q ≠ p.succ → s' q = s q := by
    intro q hq0 hq1
    have hc := congrFun heq (Sum.inl q, s' q)
    have hcond : ¬((Sum.inl q : Fin (K + 1) ⊕ Fin (K + 1)) = Sum.inl p.castSucc ∨
        (Sum.inl q : Fin (K + 1) ⊕ Fin (K + 1)) = Sum.inl (p.castSucc + 1)) := by
      rw [← flatBand_succ_eq_castSucc_add_one p, not_or]
      exact ⟨fun h => hq0 (Sum.inl_injective h), fun h => hq1 (Sum.inl_injective h)⟩
    simp only [flatBandAlphaTwoHoleOcc] at hc
    rw [if_neg hcond, if_neg hcond, flatBandAlphaSpinOcc_inl, flatBandAlphaSpinOcc_inl,
      if_pos rfl] at hc
    by_contra hsq
    rw [if_neg hsq] at hc
    exact absurd hc (by decide)
  have hswap0 : Function.update (Function.update s p.castSucc 1) p.succ 0 p.castSucc = 1 := by
    rw [Function.update_of_ne hne, Function.update_self]
  have hswap1 : Function.update (Function.update s p.castSucc 1) p.succ 0 p.succ = 0 :=
    Function.update_self _ _ _
  rcases hdich (s' p.castSucc) with hc0 | hc1
  · left
    funext q
    by_cases hq0 : q = p.castSucc
    · rw [hq0, hc0, hs0]
    · by_cases hq1 : q = p.succ
      · rw [hq1, hs1]
        rcases hdich (s' p.succ) with h | h
        · exact absurd (hc0.trans h.symm) hopp
        · exact h
      · exact hoff q hq0 hq1
  · right
    funext q
    by_cases hq0 : q = p.castSucc
    · rw [hq0, hc1, hswap0]
    · by_cases hq1 : q = p.succ
      · rw [hq1, hswap1]
        rcases hdich (s' p.succ) with h | h
        · exact h
        · exact absurd (hc1.trans h.symm) hopp
      · rw [hoff q hq0 hq1, Function.update_of_ne hq1, Function.update_of_ne hq0]

/-- **No orbital double occupancy in the half-filled ground subspace.**  A β-free occupation config
`g` that doubly occupies an orbital `q₀` has vanishing ground-state coordinate.  Reading the
`(q₀`-pair-erased) coordinate of `0 = ĉ_{ext(q₀)↓} ĉ_{ext(q₀)↑} v` isolates exactly the `g` term
(β-occupied configs are killed by the b̂-kernel; β-free non-doubly-occupied ones by the external
double annihilation), forcing `z_g · repr(v, g) = 0` with `z_g ≠ 0`. -/
theorem flatBandOccBasis_repr_eq_zero_of_doubleOcc (K : ℕ) (ν t U : ℝ) (ht : 0 < t) (hU : 0 < U)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U) {q₀ : Fin (K + 1)}
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2}
    (hgbf : ∀ q' ∈ occFinset g, ∃ r, q'.1 = Sum.inl r)
    (hg0 : (Sum.inl q₀, (0 : Fin 2)) ∈ occFinset g)
    (hg1 : (Sum.inl q₀, (1 : Fin 2)) ∈ occFinset g) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  classical
  have hE : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0 := by
    rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hv
    obtain ⟨hker, _⟩ := hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    unfold rayleighOnVec; rw [hker, dotProduct_zero, Complex.zero_re]
  have hcd := flatBand_groundState_doubleAnnihilation_mulVec_eq_zero K ν t U ht.le hU hE
    (deltaExternalSite K q₀)
  have hBK := flatBand_groundState_mem_BKernelSubmodule K ν t U ht hU.le hE
  -- the q₀-pair-erased config of g
  set h := Function.update (Function.update g (Sum.inl q₀, 0) 0) (Sum.inl q₀, 1) 0 with hh
  have hocch : occFinset h = ((occFinset g).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1) := by
    rw [hh, occFinset_update_zero, occFinset_update_zero]
  obtain ⟨zg, hzg0, hzg⟩ := flatBand_cDownUp_ext_betaFree_double K ν q₀ g hgbf hg0 hg1
  -- expand the h-coordinate of `cDownUp(ext q₀) v`
  have hexp : (flatBandOccBasis K ν).repr ((cDownUp K (deltaExternalSite K q₀)).mulVec v) h
      = ∑ f, (flatBandOccBasis K ν).repr v f *
          (flatBandOccBasis K ν).repr
            ((cDownUp K (deltaExternalSite K q₀)).mulVec (occMonomial K ν f)) h := by
    conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
    rw [Matrix.mulVec_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [flatBandOccBasis_apply, Matrix.mulVec_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hcd, map_zero, Finsupp.zero_apply] at hexp
  -- only f = g contributes
  rw [Finset.sum_eq_single g] at hexp
  · -- g term: repr(cDownUp occMonomial g)(h) = zg
    rw [hzg, map_smul, Finsupp.smul_apply, smul_eq_mul] at hexp
    have hmono : flatBandModeMonomial K ν
        (((occFinset g).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1)).toList
        = occMonomial K ν h := by rw [occMonomial, hocch]
    rw [hmono, ← flatBandOccBasis_apply, (flatBandOccBasis K ν).repr_self_apply, if_pos rfl,
      mul_one] at hexp
    exact (mul_eq_zero.mp hexp.symm).resolve_right hzg0
  · -- f ≠ g term vanishes
    intro f _ hfg
    by_cases hfbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r
    · by_cases hfd : (Sum.inl q₀, (0 : Fin 2)) ∈ occFinset f ∧
          (Sum.inl q₀, (1 : Fin 2)) ∈ occFinset f
      · -- β-free, doubly-occ, but f ≠ g ⇒ erased coordinate differs
        obtain ⟨zf, _, hzf⟩ := flatBand_cDownUp_ext_betaFree_double K ν q₀ f hfbf hfd.1 hfd.2
        rw [hzf, map_smul, Finsupp.smul_apply, smul_eq_mul]
        have hmono : flatBandModeMonomial K ν
            (((occFinset f).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1)).toList
            = occMonomial K ν (Function.update (Function.update f (Sum.inl q₀, 0) 0)
                (Sum.inl q₀, 1) 0) := by
          rw [occMonomial, occFinset_update_zero, occFinset_update_zero]
        rw [hmono, ← flatBandOccBasis_apply, (flatBandOccBasis K ν).repr_self_apply, if_neg ?_,
          mul_zero, mul_zero]
        -- the erased configs differ since f ≠ g
        intro heq
        apply hfg
        funext m
        by_cases hma : m = (Sum.inl q₀, 0)
        · rw [hma]
          exact (mem_occFinset_iff f _).mp hfd.1 |>.trans ((mem_occFinset_iff g _).mp hg0).symm
        · by_cases hmb : m = (Sum.inl q₀, 1)
          · rw [hmb]
            exact (mem_occFinset_iff f _).mp hfd.2 |>.trans ((mem_occFinset_iff g _).mp hg1).symm
          · have := congrFun heq m
            simp only [hh, Function.update_of_ne hma, Function.update_of_ne hmb] at this
            exact this
      · -- β-free, not doubly-occ ⇒ cDownUp annihilates
        rw [not_and_or] at hfd
        rw [flatBand_cDownUp_ext_betaFree_eq_zero_of_not_double K ν q₀ f hfbf hfd, map_zero,
          Finsupp.zero_apply, mul_zero]
    · -- not β-free ⇒ repr(v, f) = 0 by b̂-kernel
      simp only [not_forall, not_exists] at hfbf
      obtain ⟨q', hq'occ, hq'⟩ := hfbf
      obtain ⟨u, hu⟩ : ∃ u, q'.1 = Sum.inr u := by
        cases hq'1 : q'.1 with
        | inl r => exact absurd hq'1 (by simpa using hq' r)
        | inr u => exact ⟨u, rfl⟩
      have : (Sum.inr u, q'.2) ∈ occFinset f := by
        have : (Sum.inr u, q'.2) = q' := Prod.ext hu.symm rfl
        rwa [this]
      rw [flatBandOccBasis_repr_eq_zero_of_mem_BKernel u q'.2 hBK this, zero_mul]
  · intro hg_notin; exact absurd (Finset.mem_univ g) hg_notin

/-- **Adjacent spin-swap leaves the ground coordinate-vanishing invariant (Marshall sign).**  For a
ground vector `v` and an α-config `s` carrying `(↑, ↓)` on the pair `p, p+1`, the occupation
coordinate at `αs` vanishes iff it vanishes at the pair-swapped config.  Reading the two-hole
coordinate of `0 = ĉ_{int(p)↓} ĉ_{int(p)↑} v` isolates exactly the `αs` and pair-swap terms, with
nonzero relative weights `z_s, z_swap`. -/
theorem flatBand_ground_repr_alphaSpinOcc_swap_iff (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U)
    (p : Fin K) (s : Fin (K + 1) → Fin 2) (hs0 : s p.castSucc = 0) (hs1 : s p.succ = 1) :
    (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s) = 0 ↔
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K
        (Function.update (Function.update s p.castSucc 1) p.succ 0)) = 0 := by
  classical
  have hpne : p.castSucc ≠ p.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hE : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0 := by
    rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hv
    obtain ⟨hker, _⟩ := hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    unfold rayleighOnVec; rw [hker, dotProduct_zero, Complex.zero_re]
  have hcd := flatBand_groundState_doubleAnnihilation_mulVec_eq_zero K ν t U ht.le hU hE
    (deltaInternalSite K p.castSucc)
  have hBK := flatBand_groundState_mem_BKernelSubmodule K ν t U ht hU.le hE
  set s_sw := Function.update (Function.update s p.castSucc 1) p.succ 0 with hssw
  have hsw0 : s_sw p.castSucc = 1 := by rw [hssw, Function.update_of_ne hpne, Function.update_self]
  have hsw1 : s_sw p.succ = 0 := by rw [hssw, Function.update_self]
  have hαne : flatBandAlphaSpinOcc K s ≠ flatBandAlphaSpinOcc K s_sw := by
    intro h
    have hh := congrFun h (Sum.inl p.castSucc, 0)
    rw [flatBandAlphaSpinOcc_inl, flatBandAlphaSpinOcc_inl, hs0, hsw0] at hh
    simp at hh
  obtain ⟨zs, hzs0, hzseq⟩ := flatBand_cDownUp_int_occMonomial_canonical hν s p hs0 hs1
  obtain ⟨zsw, hzsw0, hzsweq⟩ := flatBand_cDownUp_int_occMonomial_swap hν s_sw p hsw0 hsw1
  have htwsw : flatBandAlphaTwoHoleOcc K s_sw p.castSucc
      = flatBandAlphaTwoHoleOcc K s p.castSucc := by
    rw [hssw, flatBand_succ_eq_castSucc_add_one p]
    exact flatBandAlphaTwoHoleOcc_swap_eq K s p.castSucc
  -- expand the two-hole coordinate of `cDownUp(int p) v`
  have hexp : (flatBandOccBasis K ν).repr
        ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec v)
        (flatBandAlphaTwoHoleOcc K s p.castSucc)
      = ∑ f, (flatBandOccBasis K ν).repr v f *
          (flatBandOccBasis K ν).repr
            ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec (occMonomial K ν f))
            (flatBandAlphaTwoHoleOcc K s p.castSucc) := by
    conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
    rw [Matrix.mulVec_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [flatBandOccBasis_apply, Matrix.mulVec_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hcd, map_zero, Finsupp.zero_apply] at hexp
  have hca : (flatBandOccBasis K ν).repr ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s)))
        (flatBandAlphaTwoHoleOcc K s p.castSucc) = zs := by
    rw [hzseq, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_pos rfl, mul_one]
  have hcsw : (flatBandOccBasis K ν).repr ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s_sw)))
        (flatBandAlphaTwoHoleOcc K s p.castSucc) = zsw := by
    rw [hzsweq, htwsw, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_pos rfl, mul_one]
  rw [← Finset.sum_subset
      (Finset.subset_univ {flatBandAlphaSpinOcc K s, flatBandAlphaSpinOcc K s_sw}) ?_,
    Finset.sum_pair hαne, hca, hcsw] at hexp
  · constructor
    · intro h
      rw [h, zero_mul, zero_add] at hexp
      exact (mul_eq_zero.mp hexp.symm).resolve_right hzsw0
    · intro h
      rw [h, zero_mul, add_zero] at hexp
      exact (mul_eq_zero.mp hexp.symm).resolve_right hzs0
  -- the off-{αs, αsw} terms vanish
  intro f _ hf
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hf
  by_cases hrv : (flatBandOccBasis K ν).repr v f = 0
  · rw [hrv, zero_mul]
  · have hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r := by
      intro q' hq'
      by_contra hcon
      apply hrv
      obtain ⟨u, hu⟩ : ∃ u, q'.1 = Sum.inr u := by
        cases hq1 : q'.1 with
        | inl r => exact absurd ⟨r, hq1⟩ hcon
        | inr u => exact ⟨u, rfl⟩
      have hmem : (Sum.inr u, q'.2) ∈ occFinset f := by
        rw [show (Sum.inr u, q'.2) = q' from Prod.ext hu.symm rfl]; exact hq'
      exact flatBandOccBasis_repr_eq_zero_of_mem_BKernel u q'.2 hBK hmem
    have hnd : ∀ q : Fin (K + 1),
        ¬((Sum.inl q, (0 : Fin 2)) ∈ occFinset f ∧ (Sum.inl q, (1 : Fin 2)) ∈ occFinset f) :=
      fun q hd => hrv (flatBandOccBasis_repr_eq_zero_of_doubleOcc K ν t U ht hU hv hbf hd.1 hd.2)
    have hcard : (occFinset f).card = K + 1 := by
      by_contra hc; exact hrv (flatBandOccBasis_repr_eq_zero_of_card_ne t U hv hc)
    have hrecon := flatBand_occFinset_eq_alphaSpinOcc_of_betaFree_noDouble f hbf hnd hcard
    rw [occMonomial_congr f _ hrecon]
    by_contra hcoord
    obtain ⟨hopp, htweq⟩ := flatBand_cDownUp_int_occMonomial_repr_ne_zero_imp hν s _ p
      (fun h => hcoord (by rw [h, mul_zero]))
    rcases flatBand_alphaTwoHoleOcc_eq_imp s _ p hs0 hs1 hopp htweq with hs's | hs'sw
    · exact hf.1 (config_eq_of_occFinset_eq f (flatBandAlphaSpinOcc K s) (by rw [hrecon, hs's]))
    · exact hf.2 (config_eq_of_occFinset_eq f (flatBandAlphaSpinOcc K s_sw) (by rw [hrecon, hs'sw]))

/-- **Ground coordinate-vanishing is invariant under any adjacent opposite-spin transposition.**
For a ground vector `v` and an α-config `s` with opposite spins on the adjacent pair `p, p+1`, the
coordinate at `αs` vanishes iff it vanishes at the pair-transposed config. -/
theorem flatBand_ground_repr_adjSwap_iff (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U)
    (p : Fin K) (s : Fin (K + 1) → Fin 2) (hopp : s p.castSucc ≠ s p.succ) :
    (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s) = 0 ↔
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K
        (Function.update (Function.update s p.castSucc (s p.succ)) p.succ (s p.castSucc))) = 0 := by
  have hpne : p.castSucc ≠ p.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hdich (s p.castSucc) with h0 | h1
  · have h1 : s p.succ = 1 := by
      rcases hdich (s p.succ) with h | h
      · exact absurd (h0.trans h.symm) hopp
      · exact h
    have hcfg : Function.update (Function.update s p.castSucc (s p.succ)) p.succ (s p.castSucc)
        = Function.update (Function.update s p.castSucc 1) p.succ 0 := by
      rw [h0, h1]
    rw [hcfg]
    exact flatBand_ground_repr_alphaSpinOcc_swap_iff K ν t U hν ht hU hv p s h0 h1
  · have h0 : s p.succ = 0 := by
      rcases hdich (s p.succ) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hopp
    set s2 := Function.update (Function.update s p.castSucc (s p.succ)) p.succ (s p.castSucc)
      with hs2
    have hs20 : s2 p.castSucc = 0 := by
      rw [hs2, Function.update_of_ne hpne, Function.update_self, h0]
    have hs21 : s2 p.succ = 1 := by rw [hs2, Function.update_self, h1]
    have hback : Function.update (Function.update s2 p.castSucc 1) p.succ 0 = s := by
      funext q
      by_cases hq0 : q = p.castSucc
      · rw [hq0, Function.update_of_ne hpne, Function.update_self, h1]
      · by_cases hq1 : q = p.succ
        · rw [hq1, Function.update_self, h0]
        · rw [Function.update_of_ne hq1, Function.update_of_ne hq0, hs2,
            Function.update_of_ne hq1, Function.update_of_ne hq0]
    have hmain := flatBand_ground_repr_alphaSpinOcc_swap_iff K ν t U hν ht hU hv p s2 hs20 hs21
    rw [hback] at hmain
    exact hmain.symm

/-- **Without an adjacent `(1,0)` descent, occupied spins propagate to the right.**  If no adjacent
orbital pair is `(↓-from-↑)` i.e. `(1, 0)`, then an up-spin at orbital `i` forces up-spins at all
later orbitals. -/
theorem flatBand_one_propagates (s : Fin (K + 1) → Fin 2)
    (h : ∀ k : Fin K, ¬(s k.castSucc = 1 ∧ s k.succ = 0)) :
    ∀ i j : Fin (K + 1), i ≤ j → s i = 1 → s j = 1 := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hstep : ∀ k : Fin K, s k.castSucc = 1 → s k.succ = 1 := by
    intro k hk
    rcases hdich (s k.succ) with h0 | h1
    · exact absurd ⟨hk, h0⟩ (h k)
    · exact h1
  have hgap : ∀ (m : ℕ) (i : Fin (K + 1)), s i = 1 → (hm : i.val + m < K + 1) →
      s ⟨i.val + m, hm⟩ = 1 := by
    intro m
    induction m with
    | zero =>
      intro i hi hm
      rw [show (⟨i.val + 0, hm⟩ : Fin (K + 1)) = i from Fin.ext (Nat.add_zero i.val)]; exact hi
    | succ n ih =>
      intro i hi hm
      have hn1 : i.val + n < K + 1 := by omega
      have hkK : i.val + n < K := by omega
      have hihn := ih i hi hn1
      have hcs : ((⟨i.val + n, hkK⟩ : Fin K).castSucc) = (⟨i.val + n, hn1⟩ : Fin (K + 1)) :=
        Fin.ext rfl
      have hsc : ((⟨i.val + n, hkK⟩ : Fin K).succ) = (⟨i.val + (n + 1), hm⟩ : Fin (K + 1)) :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [← hsc]
      exact hstep ⟨i.val + n, hkK⟩ (by rw [hcs]; exact hihn)
  intro i j hij hi
  have hle : i.val ≤ j.val := hij
  have hj : j.val < K + 1 := j.isLt
  have hb : i.val + (j.val - i.val) < K + 1 := by omega
  have hg := hgap (j.val - i.val) i hi hb
  rwa [show (⟨i.val + (j.val - i.val), hb⟩ : Fin (K + 1)) = j from
    Fin.ext (Nat.add_sub_cancel' hle)] at hg

/-- **A config with no adjacent inversion is determined by its up-count.**  Two monotone
(`0…01…1`) configs with the same number of up-spins are equal. -/
theorem flatBand_no_adj_inv_eq (s s' : Fin (K + 1) → Fin 2)
    (hs : ∀ k : Fin K, ¬(s k.castSucc = 1 ∧ s k.succ = 0))
    (hs' : ∀ k : Fin K, ¬(s' k.castSucc = 1 ∧ s' k.succ = 0))
    (hc : (Finset.univ.filter (fun q => s q = 1)).card
        = (Finset.univ.filter (fun q => s' q = 1)).card) :
    s = s' := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have key : ∀ (a b : Fin (K + 1) → Fin 2),
      (∀ k : Fin K, ¬(a k.castSucc = 1 ∧ a k.succ = 0)) →
      (∀ k : Fin K, ¬(b k.castSucc = 1 ∧ b k.succ = 0)) →
      (Finset.univ.filter (fun q => a q = 1)).card
        = (Finset.univ.filter (fun q => b q = 1)).card →
      ∀ q, a q = 1 → b q = 1 := by
    intro a b ha hb hcard q haq
    by_contra hbq
    have hbq0 : b q = 0 := (hdich (b q)).resolve_right hbq
    have hsub1 : Finset.Ici q ⊆ Finset.univ.filter (fun q' => a q' = 1) := fun q' hq' =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        flatBand_one_propagates a ha q q' (Finset.mem_Ici.mp hq') haq⟩
    have hsub0 : Finset.Iic q ⊆ Finset.univ.filter (fun q' => b q' = 0) := by
      intro q' hq'
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hdich (b q') with h0 | h1
      · exact h0
      · exact absurd (flatBand_one_propagates b hb q' q (Finset.mem_Iic.mp hq') h1)
          (by rw [hbq0]; decide)
    have hc1 : (K + 1) - q.val ≤ (Finset.univ.filter (fun q' => a q' = 1)).card := by
      rw [← Fin.card_Ici]; exact Finset.card_le_card hsub1
    have hc0 : q.val + 1 ≤ (Finset.univ.filter (fun q' => b q' = 0)).card := by
      rw [← Fin.card_Iic]; exact Finset.card_le_card hsub0
    have hsplit : (Finset.univ.filter (fun q' => b q' = 0)).card
        + (Finset.univ.filter (fun q' => b q' = 1)).card = K + 1 := by
      have hh := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (K + 1)))) (p := fun q' => b q' = 0)
      rw [Finset.card_univ, Fintype.card_fin,
        show (Finset.univ.filter (fun q' => ¬ b q' = 0))
            = Finset.univ.filter (fun q' => b q' = 1) from
          Finset.filter_congr (fun q' _ => by rcases hdich (b q') with h | h <;> simp [h])] at hh
      exact hh
    have hq := q.isLt
    omega
  funext q
  rcases hdich (s q) with h0 | h1
  · rcases hdich (s' q) with h0' | h1'
    · rw [h0, h0']
    · exact absurd (key s' s hs' hs hc.symm q h1') (by rw [h0]; decide)
  · rw [h1, key s s' hs hs' hc q h1]

/-- Split a sum over `Fin (K+1)` off the two adjacent pair positions `k, k+1`. -/
theorem flatBand_sum_split_pair (k : Fin K) (g : Fin (K + 1) → ℕ) :
    ∑ q, g q = g k.castSucc + g k.succ
      + ∑ q ∈ (Finset.univ.erase k.castSucc).erase k.succ, g q := by
  have hne : k.castSucc ≠ k.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ k.castSucc),
    ← Finset.add_sum_erase _ g (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ k.succ⟩),
    ← add_assoc]

/-- **An adjacent `(1,0) → (0,1)` swap preserves the up-count and raises the weight by one.** -/
theorem flatBand_adjSwap_weight_upCount (s' : Fin (K + 1) → Fin 2) (k : Fin K)
    (h1 : s' k.castSucc = 1) (h0 : s' k.succ = 0) :
    (∑ q, (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val
        = ∑ q, (s' q).val) ∧
      (∑ q, q.val * (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val
        = (∑ q, q.val * (s' q).val) + 1) := by
  have hne : k.castSucc ≠ k.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  set G := Function.update (Function.update s' k.castSucc 0) k.succ 1 with hG
  have hGksc : G k.succ = 1 := Function.update_self _ _ _
  have hGkcs : G k.castSucc = 0 := by rw [hG, Function.update_of_ne hne, Function.update_self]
  have hGoff : ∀ q, q ≠ k.castSucc → q ≠ k.succ → G q = s' q := fun q hq0 hq1 => by
    rw [hG, Function.update_of_ne hq1, Function.update_of_ne hq0]
  have hrest : ∀ (g : Fin 2 → ℕ → ℕ),
      (∑ q ∈ (Finset.univ.erase k.castSucc).erase k.succ, g (G q) q.val)
        = ∑ q ∈ (Finset.univ.erase k.castSucc).erase k.succ, g (s' q) q.val := by
    intro g
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_erase, Finset.mem_erase] at hq
    rw [hGoff q hq.2.1 hq.1]
  refine ⟨?_, ?_⟩
  · rw [flatBand_sum_split_pair k (fun q => (G q).val),
      flatBand_sum_split_pair k (fun q => (s' q).val), hGkcs, hGksc, h1, h0,
      hrest (fun v _ => v.val)]
    simp only [Fin.val_zero, Fin.val_one, Nat.zero_add, Nat.add_zero]
  · rw [flatBand_sum_split_pair k (fun q => q.val * (G q).val),
      flatBand_sum_split_pair k (fun q => q.val * (s' q).val), hGkcs, hGksc, h1, h0,
      hrest (fun v n => n * v.val)]
    simp only [Fin.val_zero, Fin.val_one, mul_zero, mul_one, Fin.val_succ, Fin.val_castSucc]
    ring

/-- **Coordinate-vanishing propagates across all configs of equal up-count.**  If a ground vector's
coordinate vanishes at the sorted (no-adjacent-inversion) representative `rep`, it vanishes at every
α-config with the same up-count.  Strong induction on `M − weight`: an adjacent `(1,0)` raises the
weight (via the swap-iff and `flatBand_adjSwap_weight_upCount`); when none remains the config is
`rep` (sorted-unique). -/
theorem flatBand_ground_repr_zero_of_upCount (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U) (rep : Fin (K + 1) → Fin 2)
    (hrepsort : ∀ k : Fin K, ¬(rep k.castSucc = 1 ∧ rep k.succ = 0))
    (hrep0 : (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K rep) = 0) :
    ∀ s' : Fin (K + 1) → Fin 2, (∑ q, (s' q).val = ∑ q, (rep q).val) →
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s') = 0 := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hcardval : ∀ (s : Fin (K + 1) → Fin 2),
      (Finset.univ.filter (fun q => s q = 1)).card = ∑ q, (s q).val := by
    intro s
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun q _ => by rcases hdich (s q) with h | h <;> simp [h])
  have hwle : ∀ (s : Fin (K + 1) → Fin 2), (∑ q, q.val * (s q).val) ≤ (K + 1) * (K + 1) := by
    intro s
    calc ∑ q, q.val * (s q).val ≤ ∑ _q : Fin (K + 1), K :=
          Finset.sum_le_sum (fun q _ => by have := q.isLt; have := (s q).isLt; nlinarith)
      _ = (K + 1) * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ (K + 1) * (K + 1) := by nlinarith
  suffices H : ∀ (D : ℕ) (s' : Fin (K + 1) → Fin 2),
      (K + 1) * (K + 1) - (∑ q, q.val * (s' q).val) = D →
      (∑ q, (s' q).val = ∑ q, (rep q).val) →
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s') = 0 by
    intro s' hc; exact H _ s' rfl hc
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro s' hD hc
    by_cases hsw : ∃ k : Fin K, s' k.castSucc = 1 ∧ s' k.succ = 0
    · obtain ⟨k, hk1, hk0⟩ := hsw
      obtain ⟨huc, hwt⟩ := flatBand_adjSwap_weight_upCount s' k hk1 hk0
      have hcG : ∑ q, (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val
          = ∑ q, (rep q).val := by rw [huc, hc]
      have hwGle := hwle (Function.update (Function.update s' k.castSucc 0) k.succ 1)
      rw [hwt] at hwGle
      have hlt : (K + 1) * (K + 1) - (∑ q, q.val *
          (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val) < D := by
        rw [hwt]; omega
      have hGrepr := ih _ hlt (Function.update (Function.update s' k.castSucc 0) k.succ 1) rfl hcG
      have hopp : s' k.castSucc ≠ s' k.succ := by rw [hk1, hk0]; decide
      have hiff := flatBand_ground_repr_adjSwap_iff K ν t U hν ht hU hv k s' hopp
      rw [show Function.update (Function.update s' k.castSucc (s' k.succ)) k.succ (s' k.castSucc)
          = Function.update (Function.update s' k.castSucc 0) k.succ 1 by rw [hk0, hk1]] at hiff
      exact hiff.mpr hGrepr
    · have hs'sort : ∀ k : Fin K, ¬(s' k.castSucc = 1 ∧ s' k.succ = 0) :=
        fun k ⟨ha, hb⟩ => hsw ⟨k, ha, hb⟩
      rw [flatBand_no_adj_inv_eq s' rep hs'sort hrepsort (by rw [hcardval, hcardval, hc])]
      exact hrep0

/-- The sorted representative α-config for a block: `m` leading down-spins, the rest up. -/
def flatBandSortedRep (K m : ℕ) : Fin (K + 1) → Fin 2 := fun q => if q.val < m then 0 else 1

/-- The sorted representative has no adjacent `(1,0)` inversion. -/
theorem flatBandSortedRep_no_adj_inv (m : ℕ) : ∀ k : Fin K,
    ¬((flatBandSortedRep K m) k.castSucc = 1 ∧ (flatBandSortedRep K m) k.succ = 0) := by
  intro k ⟨h1, h0⟩
  simp only [flatBandSortedRep, Fin.val_castSucc, Fin.val_succ] at h1 h0
  by_cases hk : k.val < m
  · rw [if_pos hk] at h1; exact absurd h1 (by decide)
  · rw [if_neg hk] at h1
    by_cases hk1 : k.val + 1 < m
    · omega
    · rw [if_neg hk1] at h0; exact absurd h0 (by decide)

/-- Counting the up-spins of the sorted representative: `∑ (rep q).val = (K+1) − m`. -/
theorem flatBandSortedRep_upCount (m : ℕ) :
    ∑ q, ((flatBandSortedRep K m) q).val = (K + 1) - m := by
  have hrange : ∀ (n : ℕ),
      ∑ i ∈ Finset.range n, (if i < m then (0 : ℕ) else 1) = n - m := by
    intro n
    induction n with
    | zero => simp
    | succ p ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hp : p < m
      · rw [if_pos hp]; omega
      · rw [if_neg hp]; omega
  calc ∑ q, ((flatBandSortedRep K m) q).val
      = ∑ q : Fin (K + 1), (if q.val < m then (0 : ℕ) else 1) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        simp only [flatBandSortedRep]
        by_cases hq : q.val < m <;> simp [hq]
    _ = ∑ i ∈ Finset.range (K + 1), (if i < m then (0 : ℕ) else 1) :=
        (Fin.sum_univ_eq_sum_range (fun i => if i < m then (0 : ℕ) else 1) (K + 1))
    _ = (K + 1) - m := hrange (K + 1)

/-- The `Ŝ^z` weight of an α-config is `(K+1)/2` minus its up-count. -/
theorem flatBand_alphaSpinCharge_eq (s : Fin (K + 1) → Fin 2) :
    ∑ p, flatBandSpinCharge (s p) = ((K + 1 : ℕ) : ℂ) / 2 - ∑ p, ((s p).val : ℂ) := by
  simp only [flatBandSpinCharge]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

open Module in
/-- **Each `Ŝ^z`-weight block of the half-filled ground subspace is at most one-dimensional.**  The
coordinate functional at the sorted representative is injective: its kernel forces every occupation
coordinate to vanish (off-sector ones by the support lemmas, the in-sector ones by the
swap-invariant propagation), hence the vector is zero. -/
theorem flatBand_block_finrank_le_one (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t) (hU : 0 < U)
    (a : Fin (K + 2)) :
    finrank ℂ ↥(flatBandHalfFilledGroundSubmodule K ν t U ⊓
      Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin
        (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤ 1 := by
  classical
  set μ : ℂ := (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) with hμ
  set B := flatBandHalfFilledGroundSubmodule K ν t U ⊓
    Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin μ with hB
  set rep := flatBandSortedRep K a.val with hrep
  have ha : a.val ≤ K + 1 := by have := a.isLt; omega
  have hrepμ : ∑ p, flatBandSpinCharge (rep p) = μ := by
    rw [flatBand_alphaSpinCharge_eq,
      show (∑ p, ((rep p).val : ℂ)) = (((K + 1 - a.val : ℕ) : ℕ) : ℂ) from by
        rw [show (∑ p, ((rep p).val : ℂ)) = ((∑ p, (rep p).val : ℕ) : ℂ) from by push_cast; rfl,
          hrep, flatBandSortedRep_upCount],
      hμ, Nat.cast_sub ha]
    push_cast
    ring
  set Φ : ↥B →ₗ[ℂ] ℂ := (Finsupp.lapply (flatBandAlphaSpinOcc K rep)).comp
    (((flatBandOccBasis K ν).repr.toLinearMap).comp B.subtype) with hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : (flatBandOccBasis K ν).repr w.1 (flatBandAlphaSpinOcc K rep) = 0 := hw
    have hwg : w.1 ∈ flatBandHalfFilledGroundSubmodule K ν t U := (Submodule.mem_inf.mp w.2).1
    have hall : ∀ f, (flatBandOccBasis K ν).repr w.1 f = 0 := by
      intro f
      by_cases hcard : (occFinset f).card = K + 1
      · by_cases hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r
        · by_cases hnd : ∀ q : Fin (K + 1),
              ¬((Sum.inl q, (0 : Fin 2)) ∈ occFinset f ∧ (Sum.inl q, (1 : Fin 2)) ∈ occFinset f)
          · have hrecon := flatBand_occFinset_eq_alphaSpinOcc_of_betaFree_noDouble f hbf hnd hcard
            set s' := fun q => if (Sum.inl q, (0 : Fin 2)) ∈ occFinset f then (0 : Fin 2) else 1
              with hs'
            have hfeq : f = flatBandAlphaSpinOcc K s' := config_eq_of_occFinset_eq f _ hrecon
            by_cases hsc : (∑ q ∈ occFinset f, flatBandSpinCharge q.2) = μ
            · have hscf : ∑ p, flatBandSpinCharge (s' p) = μ := by
                rw [← occFinset_alphaSpinOcc_spinCharge_sum, ← hrecon, hsc]
              have hcount : ∑ q, (s' q).val = ∑ q, (rep q).val := by
                have h1 : ∑ p, flatBandSpinCharge (s' p) = ∑ p, flatBandSpinCharge (rep p) := by
                  rw [hscf, hrepμ]
                rw [flatBand_alphaSpinCharge_eq, flatBand_alphaSpinCharge_eq] at h1
                have h2 := sub_right_inj.mp h1
                exact_mod_cast h2
              rw [hfeq]
              exact flatBand_ground_repr_zero_of_upCount K ν t U hν ht hU hwg rep
                (flatBandSortedRep_no_adj_inv a.val) hw' s' hcount
            · exact flatBandOccBasis_repr_eq_zero_of_spinZ_ne t U μ w.2 hsc
          · simp only [not_forall, not_not] at hnd
            obtain ⟨q, hq0, hq1⟩ := hnd
            exact flatBandOccBasis_repr_eq_zero_of_doubleOcc K ν t U ht hU hwg hbf hq0 hq1
        · rw [not_forall] at hbf
          obtain ⟨q', hq'⟩ := hbf
          rw [Classical.not_imp, not_exists] at hq'
          obtain ⟨hq'occ, hq'nr⟩ := hq'
          obtain ⟨u, hu⟩ : ∃ u, q'.1 = Sum.inr u := by
            cases hq1 : q'.1 with
            | inl r => exact absurd hq1 (hq'nr r)
            | inr u => exact ⟨u, rfl⟩
          have hmem : (Sum.inr u, q'.2) ∈ occFinset f := by
            rw [show (Sum.inr u, q'.2) = q' from Prod.ext hu.symm rfl]; exact hq'occ
          exact flatBandOccBasis_repr_eq_zero_of_mem_BKernel u q'.2
            (flatBand_groundState_mem_BKernelSubmodule K ν t U ht hU.le (by
              rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hwg
              obtain ⟨hker, _⟩ := hwg
              rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
              unfold rayleighOnVec; rw [hker, dotProduct_zero, Complex.zero_re])) hmem
      · exact flatBandOccBasis_repr_eq_zero_of_card_ne t U hwg hcard
    have hw1 : w.1 = 0 := (flatBandOccBasis K ν).repr.map_eq_zero_iff.mp (Finsupp.ext hall)
    exact Subtype.ext hw1
  have key := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [finrank_self] at key

end LatticeSystem.Fermion
