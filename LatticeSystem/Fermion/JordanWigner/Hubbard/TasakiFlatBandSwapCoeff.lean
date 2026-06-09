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
theorem flatBand_siteAnnihilation_head (K : ℕ) (ν : ℝ) (p r : Fin (K + 1)) (σ : Fin 2)
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 (deltaInternalSite K p) = 0 ∨ q.2 ≠ σ) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1)
        (spinfulIndex (2 * K + 1) (deltaInternalSite K p) σ)).mulVec
        (flatBandModeMonomial K ν ((Sum.inl r, σ) :: rest))
      = flatBandBasis K ν (Sum.inl r) (deltaInternalSite K p) • flatBandModeMonomial K ν rest := by
  rw [flatBand_siteAnnihilation_peel_modeMonomial]
  change ∑ i : Fin (rest.length + 1),
      flatBandModePeelTerm K ν (deltaInternalSite K p) σ ((Sum.inl r, σ) :: rest) i = _
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
theorem flatBand_cDownUp_two_head (K : ℕ) (ν : ℝ) (p r₁ r₂ : Fin (K + 1))
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 (deltaInternalSite K p) = 0) :
    (cDownUp K (deltaInternalSite K p)).mulVec
        (flatBandModeMonomial K ν
          ((Sum.inl r₁, (0 : Fin 2)) :: (Sum.inl r₂, (1 : Fin 2)) :: rest))
      = (flatBandBasis K ν (Sum.inl r₁) (deltaInternalSite K p) *
          flatBandBasis K ν (Sum.inl r₂) (deltaInternalSite K p)) •
        flatBandModeMonomial K ν rest := by
  rw [cDownUp, ← Matrix.mulVec_mulVec,
    flatBand_siteAnnihilation_head K ν p r₁ 0 ((Sum.inl r₂, (1 : Fin 2)) :: rest)
      (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inr (show (1 : Fin 2) ≠ 0 by decide)
        · exact Or.inl (hrest q hq')),
    Matrix.mulVec_smul,
    flatBand_siteAnnihilation_head K ν p r₂ 1 rest (fun q hq => Or.inl (hrest q hq)), smul_smul]

/-- **Canonical `(↑,↓)` two-overlap monomial:** `ĉ_{int(p)↓} ĉ_{int(p)↑}` on
`(inl p, ↑) :: (inl(p+1), ↓) :: rest` gives `+ν² · monomial(rest)`. -/
theorem flatBand_cDownUp_canonical (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (rest : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hrest : ∀ q ∈ rest, flatBandBasis K ν q.1 (deltaInternalSite K p) = 0) :
    (cDownUp K (deltaInternalSite K p)).mulVec
        (flatBandModeMonomial K ν
          ((Sum.inl p, (0 : Fin 2)) :: (Sum.inl (p + 1), (1 : Fin 2)) :: rest))
      = (((ν : ℝ) : ℂ)) ^ 2 • flatBandModeMonomial K ν rest := by
  rw [flatBand_cDownUp_two_head K ν p p (p + 1) rest hrest,
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
    flatBand_cDownUp_two_head K ν p (p + 1) p rest hrest,
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

end LatticeSystem.Fermion
