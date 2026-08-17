import LatticeSystem.Quantum.SpinS.KennedyTasakiTransformRules

/-!
# Tasaki §8.2.3: local spin monomials under the Kennedy–Tasaki transformation

A **local product of spin operators** (Tasaki p. 250) is recorded here as a word
`w : List (Fin L × Fin 3)` of (site, axis) letters; `n₁, n₂, n₃` are the `List.countP` occurrences
of the three axes.  Two facts about such words drive Proposition 8.4.

* **The sign law.**  Conjugating by the `π` rotation `Û_π^{(α)}` multiplies the monomial by
  `(-1)^{#{i | α_i ≠ α}}`.  This is an identity, never a biconditional: the monomial can vanish
  (`Ŝ^{(3)} Ŝ^{(1)} Ŝ^{(3)} = 0` at `S = 1`), and `0` is invariant at every parity.  Note the
  **cross-pairing**: the exponent for `Û_π^{(1)}` counts the letters of axis `2` and `3`, which is
  exactly the number of left axis-3 strings created by (8.2.13)–(8.2.14); the exponent for
  `Û_π^{(3)}` counts the letters of axis `1` and `2`, the number of right axis-1 strings.
* **The tail laws.**  Outside the window carrying the word, the transformed monomial
  `Û_KT O_w Û_KT` does not commute with the site algebra but *twists* it by a power of a single-site
  half turn, the power being exactly the string count above.  Left of the word the twist is by the
  axis-3 half turn, right of it by the axis-1 half turn.

Together with `eq_zero_of_onSiteS_twist` — no nonzero operator can both commute with and be
half-turn-twisted by the whole on-site algebra at one site — these give both directions of the
single-monomial form of Proposition 8.4.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2, eqs. (8.2.12)–(8.2.15), p. 243; §8.2.3, p. 250; §2.1, eqs. (2.1.21) and (2.1.23),
pp. 17–18.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **word-indexed spin monomial** `O_w = ∏_i Ŝ_{w_i.1}^{(w_i.2)}` for a word
`w : List (Fin L × Fin 3)` of (site, axis) letters, read left to right in list order.  Same-site
letters do not commute (`Ŝ^{(1)} Ŝ^{(2)} ≠ Ŝ^{(2)} Ŝ^{(1)}`) and the book's own example
`Ŝ_x^{(1)} Ŝ_{x+1}^{(2)} (Ŝ_{x+2}^{(3)})²` repeats a letter, so a `List`, not a `Finset`/`Multiset`,
is the right bookkeeping (idiom precedent: `cartWord`, `AndersonTowerCartWord.lean:33`). -/
noncomputable def spinMonomialS {L : ℕ} (w : List (Fin L × Fin 3)) : ManyBodyOpS (Fin L) 2 :=
  (w.map fun p => spinSSiteComponentS p.2 p.1).prod

/-- The empty word gives the identity. -/
theorem spinMonomialS_nil : spinMonomialS ([] : List (Fin L × Fin 3)) = 1 := by
  rw [spinMonomialS]; simp

/-- Splitting the leading letter off a word. -/
theorem spinMonomialS_cons (p : Fin L × Fin 3) (t : List (Fin L × Fin 3)) :
    spinMonomialS (p :: t) = spinSSiteComponentS p.2 p.1 * spinMonomialS t := by
  rw [spinMonomialS, spinMonomialS, List.map_cons, List.prod_cons]

/-! ## Generic rearrangement helpers -/

/-- From a conjugation identity `R Y R = Z` for an involution `R`, move `R` past `Y`. -/
private theorem mul_eq_of_conj_eq {R Y Z : ManyBodyOpS (Fin L) 2} (hR : R * R = 1)
    (h : R * Y * R = Z) : R * Y = Z * R := by
  rw [← h, mul_assoc, hR, mul_one]

/-- Pushing `Y` leftwards through `Lf Xc Rf` when only the **left** factor twists it. -/
private theorem mul_of_left_twist {Lf Xc Rf Y Z : ManyBodyOpS (Fin L) 2}
    (hRY : Commute Rf Y) (hXY : Commute Xc Y) (hL : Lf * Y = Z * Lf) :
    Lf * Xc * Rf * Y = Z * (Lf * Xc * Rf) := by
  calc Lf * Xc * Rf * Y = Lf * (Xc * (Rf * Y)) := by noncomm_ring
    _ = Lf * (Xc * (Y * Rf)) := by rw [hRY.eq]
    _ = Lf * (Xc * Y * Rf) := by noncomm_ring
    _ = Lf * (Y * Xc * Rf) := by rw [hXY.eq]
    _ = Lf * Y * (Xc * Rf) := by noncomm_ring
    _ = Z * Lf * (Xc * Rf) := by rw [hL]
    _ = Z * (Lf * Xc * Rf) := by noncomm_ring

/-- Pushing `Y` leftwards through `Lf Xc Rf` when only the **right** factor twists it. -/
private theorem mul_of_right_twist {Lf Xc Rf Y Z : ManyBodyOpS (Fin L) 2}
    (hLZ : Commute Lf Z) (hXZ : Commute Xc Z) (hR : Rf * Y = Z * Rf) :
    Lf * Xc * Rf * Y = Z * (Lf * Xc * Rf) := by
  calc Lf * Xc * Rf * Y = Lf * Xc * (Rf * Y) := by noncomm_ring
    _ = Lf * Xc * (Z * Rf) := by rw [hR]
    _ = Lf * (Xc * Z) * Rf := by noncomm_ring
    _ = Lf * (Z * Xc) * Rf := by rw [hXZ.eq]
    _ = Lf * Z * (Xc * Rf) := by noncomm_ring
    _ = Z * Lf * (Xc * Rf) := by rw [hLZ.eq]
    _ = Z * (Lf * Xc * Rf) := by noncomm_ring

/-! ## Half-turn power bookkeeping -/

/-- Adding one more twist to a half-turn power. -/
private theorem halfTurn_pow_conj_succ (alpha : Fin 3) (n : ℕ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    spinOneHalfTurnS alpha ^ (1 : ℕ) *
        (spinOneHalfTurnS alpha ^ n * A * spinOneHalfTurnS alpha ^ n) *
        spinOneHalfTurnS alpha ^ (1 : ℕ)
      = spinOneHalfTurnS alpha ^ (n + 1) * A * spinOneHalfTurnS alpha ^ (n + 1) := by
  rw [pow_one]
  nth_rewrite 1 [pow_succ']
  nth_rewrite 1 [pow_succ]
  simp only [mul_assoc]

/-- Adding no twist leaves a half-turn power unchanged. -/
private theorem halfTurn_pow_conj_zero (alpha : Fin 3) (n : ℕ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    spinOneHalfTurnS alpha ^ (0 : ℕ) *
        (spinOneHalfTurnS alpha ^ n * A * spinOneHalfTurnS alpha ^ n) *
        spinOneHalfTurnS alpha ^ (0 : ℕ)
      = spinOneHalfTurnS alpha ^ (n + 0) * A * spinOneHalfTurnS alpha ^ (n + 0) := by
  simp

/-! ## The tail laws -/

/-- **Single-letter left tail law**: at a site `z` strictly left of the letter's site, the
transformed component twists the on-site algebra by the axis-3 half turn, once if the letter's axis
is not `1` (Lean index not `0`) and not at all otherwise. -/
private theorem ktConj_component_left (alpha : Fin 3) {z x : Fin L} (hzx : z.val < x.val)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ktUnitaryS L * spinSSiteComponentS alpha x * ktUnitaryS L * onSiteS z A
      = onSiteS z (spinOneHalfTurnS 2 ^ (if alpha = 0 then 0 else 1) * A
          * spinOneHalfTurnS 2 ^ (if alpha = 0 then 0 else 1))
        * (ktUnitaryS L * spinSSiteComponentS alpha x * ktUnitaryS L) := by
  have hzne : z ≠ x := by intro he; subst he; omega
  have hXY : Commute (spinSSiteComponentS alpha x) (onSiteS z A) := by
    rw [spinSSiteComponentS_eq_onSiteS]
    exact onSiteS_commute_of_ne (Ne.symm hzne) _ _
  have hRY : Commute (if alpha = 2 then 1 else ktRightStringS L x.val) (onSiteS z A) := by
    split
    · exact Commute.one_left _
    · exact ktRightStringS_commute_onSiteS_of_le L (le_of_lt hzx) A
  rw [ktUnitaryS_conj_spinSSiteComponentS]
  refine mul_of_left_twist hRY hXY ?_
  by_cases h0 : alpha = 0
  · rw [if_pos h0, if_pos h0, pow_zero, one_mul, mul_one, one_mul, mul_one]
  · rw [if_neg h0, if_neg h0, pow_one]
    exact mul_eq_of_conj_eq (edgeStringPrefixRotationS_mul_self L 2 x.val)
      (edgeStringPrefixRotationS_conj_onSiteS_of_lt L 2 x.val hzx A)

/-- **Single-letter right tail law**: at a site `z` strictly right of the letter's site, the
transformed component twists the on-site algebra by the axis-1 half turn, once if the letter's axis
is not `3` (Lean index not `2`) and not at all otherwise. -/
private theorem ktConj_component_right (alpha : Fin 3) {z x : Fin L} (hxz : x.val < z.val)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ktUnitaryS L * spinSSiteComponentS alpha x * ktUnitaryS L * onSiteS z A
      = onSiteS z (spinOneHalfTurnS 0 ^ (if alpha = 2 then 0 else 1) * A
          * spinOneHalfTurnS 0 ^ (if alpha = 2 then 0 else 1))
        * (ktUnitaryS L * spinSSiteComponentS alpha x * ktUnitaryS L) := by
  have hzne : z ≠ x := by intro he; subst he; omega
  have hXZ : Commute (spinSSiteComponentS alpha x)
      (onSiteS z (spinOneHalfTurnS 0 ^ (if alpha = 2 then 0 else 1) * A
        * spinOneHalfTurnS 0 ^ (if alpha = 2 then 0 else 1))) := by
    rw [spinSSiteComponentS_eq_onSiteS]
    exact onSiteS_commute_of_ne (Ne.symm hzne) _ _
  have hLZ : Commute (if alpha = 0 then 1 else edgeStringPrefixRotationS L 2 x.val)
      (onSiteS z (spinOneHalfTurnS 0 ^ (if alpha = 2 then 0 else 1) * A
        * spinOneHalfTurnS 0 ^ (if alpha = 2 then 0 else 1))) := by
    split
    · exact Commute.one_left _
    · exact edgeStringPrefixRotationS_commute_onSiteS_of_le L 2 x.val (le_of_lt hxz) _
  rw [ktUnitaryS_conj_spinSSiteComponentS]
  refine mul_of_right_twist hLZ hXZ ?_
  by_cases h2 : alpha = 2
  · rw [if_pos h2, if_pos h2, pow_zero, one_mul, mul_one, one_mul, mul_one]
  · rw [if_neg h2, if_neg h2, pow_one]
    exact mul_eq_of_conj_eq (ktRightStringS_mul_self L x.val)
      (ktRightStringS_conj_onSiteS_of_lt L hxz A)

/-- **Left tail law for a whole word** (the accumulated left string of (8.2.13)–(8.2.14)): if every
letter of `w` sits at or right of `a` and `z` is strictly left of `a`, then the transformed monomial
twists the site-`z` algebra by the axis-3 half turn raised to the number of letters whose axis is
not `1` (Lean index not `0`).  For an even count this is exactly commutation. -/
theorem ktConj_spinMonomialS_left (a : ℕ) {z : Fin L} (hz : z.val < a) :
    ∀ w : List (Fin L × Fin 3), (∀ p ∈ w, a ≤ (p.1 : Fin L).val) →
      ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
        ktUnitaryS L * spinMonomialS w * ktUnitaryS L * onSiteS z A
          = onSiteS z (spinOneHalfTurnS 2 ^ (w.countP fun p => p.2 ≠ 0) * A
              * spinOneHalfTurnS 2 ^ (w.countP fun p => p.2 ≠ 0))
            * (ktUnitaryS L * spinMonomialS w * ktUnitaryS L) := by
  intro w
  induction w with
  | nil =>
    intro _ A
    rw [spinMonomialS_nil, mul_one, ktUnitaryS_sq]
    simp
  | cons p t ih =>
    intro hw A
    have hzx : z.val < (p.1 : Fin L).val := lt_of_lt_of_le hz (hw p (List.mem_cons_self ..))
    rw [spinMonomialS_cons, conj_mul_of_mul_self (ktUnitaryS_sq L), mul_assoc,
      ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)) A, ← mul_assoc,
      ktConj_component_left p.2 hzx, mul_assoc]
    congr 2
    rw [List.countP_cons]
    by_cases h0 : p.2 = 0
    · rw [if_pos h0, if_neg (by simp [h0])]
      exact halfTurn_pow_conj_zero 2 _ A
    · rw [if_neg h0, if_pos (by simpa using h0)]
      exact halfTurn_pow_conj_succ 2 _ A

/-- **Right tail law for a whole word** (the accumulated right string of (8.2.12)–(8.2.13)): if
every letter of `w` sits at or left of `b` and `z` is strictly right of `b`, then the transformed
monomial twists the site-`z` algebra by the axis-1 half turn raised to the number of letters whose
axis is not `3` (Lean index not `2`). -/
theorem ktConj_spinMonomialS_right (b : ℕ) {z : Fin L} (hz : b < z.val) :
    ∀ w : List (Fin L × Fin 3), (∀ p ∈ w, (p.1 : Fin L).val ≤ b) →
      ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
        ktUnitaryS L * spinMonomialS w * ktUnitaryS L * onSiteS z A
          = onSiteS z (spinOneHalfTurnS 0 ^ (w.countP fun p => p.2 ≠ 2) * A
              * spinOneHalfTurnS 0 ^ (w.countP fun p => p.2 ≠ 2))
            * (ktUnitaryS L * spinMonomialS w * ktUnitaryS L) := by
  intro w
  induction w with
  | nil =>
    intro _ A
    rw [spinMonomialS_nil, mul_one, ktUnitaryS_sq]
    simp
  | cons p t ih =>
    intro hw A
    have hxz : (p.1 : Fin L).val < z.val := lt_of_le_of_lt (hw p (List.mem_cons_self ..)) hz
    rw [spinMonomialS_cons, conj_mul_of_mul_self (ktUnitaryS_sq L), mul_assoc,
      ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)) A, ← mul_assoc,
      ktConj_component_right p.2 hxz, mul_assoc]
    congr 2
    rw [List.countP_cons]
    by_cases h2 : p.2 = 2
    · rw [if_pos h2, if_neg (by simp [h2])]
      exact halfTurn_pow_conj_zero 0 _ A
    · rw [if_neg h2, if_pos (by simpa using h2)]
      exact halfTurn_pow_conj_succ 0 _ A

/-! ## The sign law -/

/-- Pulling scalars out of an ordered product. -/
private theorem listProd_map_smul {ι : Type*} (c : ι → ℂ) (f : ι → ManyBodyOpS (Fin L) 2) :
    ∀ l : List ι, (l.map fun i => c i • f i).prod = (l.map c).prod • (l.map f).prod := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The product of the per-letter signs is the parity sign of the axis count. -/
private theorem listProd_sign_eq_pow (alpha : Fin 3) :
    ∀ w : List (Fin L × Fin 3),
      (w.map fun p => if alpha = p.2 then (1 : ℂ) else -1).prod
        = (-1 : ℂ) ^ (w.countP fun p => p.2 ≠ alpha) := by
  intro w
  induction w with
  | nil => simp
  | cons p t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.countP_cons]
    by_cases h : alpha = p.2
    · rw [if_pos h, one_mul, if_neg (by simp [h.symm])]
      simp
    · rw [if_neg h, if_pos (by simpa using fun hc : p.2 = alpha => h hc.symm), pow_succ]
      ring

/-- **The sign law of §8.2.3, p. 250**: conjugating a spin monomial by the `π` rotation about the
axis `α` multiplies it by `(-1)^{#{i | α_i ≠ α}}`.  This is an *identity*, valid for every word — in
particular for words whose monomial vanishes, for which the parity is not recoverable.  The
cross-pairing is worth stating explicitly: for `α = 1` (Lean index `0`) the exponent counts the
axis-`2` and axis-`3` letters, exactly the number of left axis-3 strings of (8.2.13)–(8.2.14). -/
theorem piRotationS_conj_spinMonomialS (alpha : Fin 3) (w : List (Fin L × Fin 3)) :
    piRotationS L alpha * spinMonomialS w * piRotationS L alpha
      = ((-1 : ℂ) ^ (w.countP fun p => p.2 ≠ alpha)) • spinMonomialS w := by
  have hone : ∀ (beta : Fin 3) (y : Fin L),
      piRotationS L alpha * spinSSiteComponentS beta y * piRotationS L alpha
        = (if alpha = beta then (1 : ℂ) else -1) • spinSSiteComponentS beta y := by
    intro beta y
    rw [spinSSiteComponentS_eq_onSiteS, piRotationS,
      halfTurnRegionS_conj_onSiteS_of_mem L alpha _ (Finset.mem_univ y),
      spinOneHalfTurnS_conj_spinOneAxisS, onSiteS_smul]
  have hexp := conj_listProd (piRotationS_mul_self L alpha)
    (w.map fun p => spinSSiteComponentS p.2 p.1)
  have hmap : ((w.map fun p => spinSSiteComponentS p.2 p.1).map
        fun X => piRotationS L alpha * X * piRotationS L alpha)
      = w.map fun p => (if alpha = p.2 then (1 : ℂ) else -1) • spinSSiteComponentS p.2 p.1 := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => hone p.2 p.1
  change piRotationS L alpha * (w.map fun p => spinSSiteComponentS p.2 p.1).prod *
    piRotationS L alpha = _
  rw [hexp, hmap, listProd_map_smul (fun p : Fin L × Fin 3 => if alpha = p.2 then (1 : ℂ) else -1)
    (fun p : Fin L × Fin 3 => spinSSiteComponentS p.2 p.1), listProd_sign_eq_pow]
  rfl

/-! ## Parities and `Z₂ × Z₂` invariance of a monomial -/

/-- Each letter fails exactly two of the three axis tests, so the three axis counts of a word sum to
twice its length.  Consequently two even counts force the third to be even. -/
private theorem countP_axis_sum (w : List (Fin L × Fin 3)) :
    (w.countP fun p => p.2 ≠ 0) + (w.countP fun p => p.2 ≠ 1) + (w.countP fun p => p.2 ≠ 2)
      = 2 * w.length := by
  induction w with
  | nil => simp
  | cons a t ih =>
    obtain ⟨y, b⟩ := a
    rw [List.countP_cons, List.countP_cons, List.countP_cons, List.length_cons]
    revert ih
    generalize (t.countP fun p => p.2 ≠ 0) = c0
    generalize (t.countP fun p => p.2 ≠ 1) = c1
    generalize (t.countP fun p => p.2 ≠ 2) = c2
    intro ih
    fin_cases b <;> simp <;> omega

/-- A monomial whose three axis counts are all even is `Z₂ × Z₂` invariant. -/
theorem isZ2Z2Invariant_spinMonomialS_of_even (w : List (Fin L × Fin 3))
    (h : ∀ alpha : Fin 3, Even (w.countP fun p => p.2 ≠ alpha)) :
    IsZ2Z2Invariant (spinMonomialS w) := by
  rw [isZ2Z2Invariant_iff]
  intro alpha
  rw [piRotationS_conj_spinMonomialS, (h alpha).neg_one_pow, one_smul]

/-- A non-invariant monomial is nonzero: the zero operator is invariant under everything. -/
theorem spinMonomialS_ne_zero_of_not_isZ2Z2Invariant (w : List (Fin L × Fin 3))
    (h : ¬ IsZ2Z2Invariant (spinMonomialS w)) : spinMonomialS w ≠ 0 := by
  intro h0
  refine h ?_
  rw [isZ2Z2Invariant_iff]
  intro alpha
  rw [h0, mul_zero, zero_mul]

/-- For a **nonzero** monomial, `Z₂ × Z₂` invariance forces every axis count to be even. -/
theorem even_countP_of_isZ2Z2Invariant {w : List (Fin L × Fin 3)} (hne : spinMonomialS w ≠ 0)
    (h : IsZ2Z2Invariant (spinMonomialS w)) (alpha : Fin 3) :
    Even (w.countP fun p => p.2 ≠ alpha) := by
  rw [isZ2Z2Invariant_iff] at h
  have hsign := (piRotationS_conj_spinMonomialS alpha w).symm.trans (h alpha)
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow, neg_smul, one_smul, neg_eq_iff_add_eq_zero, ← two_smul ℂ] at hsign
  exact hne (by simpa using (smul_eq_zero.mp hsign).resolve_left (by norm_num))

/-- **The non-invariance dichotomy used by Proposition 8.4**: a monomial that is not `Z₂ × Z₂`
invariant has an odd number of letters off the axis `1`, or an odd number off the axis `3` (Lean
indices `0` and `2`).  The third axis follows from the other two by `countP_axis_sum`. -/
theorem odd_countP_of_not_isZ2Z2Invariant {w : List (Fin L × Fin 3)}
    (h : ¬ IsZ2Z2Invariant (spinMonomialS w)) :
    ¬ Even (w.countP fun p => p.2 ≠ 0) ∨ ¬ Even (w.countP fun p => p.2 ≠ 2) := by
  by_contra hcon
  push Not at hcon
  refine h (isZ2Z2Invariant_spinMonomialS_of_even w ?_)
  have hsum := countP_axis_sum w
  have hmid : Even (w.countP fun p => p.2 ≠ 1) := by
    obtain ⟨k, hk⟩ := hcon.1
    obtain ⟨m, hm⟩ := hcon.2
    exact ⟨w.length - k - m, by omega⟩
  intro alpha
  fin_cases alpha
  · exact hcon.1
  · exact hmid
  · exact hcon.2

/-! ## The vanishing engine -/

/-- A resolution of the identity by matrices anticommuting with the half turn `u_α`: there are
three pairs `(M, A)` with `Σ M (A - u_α A u_α) = 1`.  Since no invertible matrix anticommutes with
a half turn whose `±1` eigenspaces have different dimensions, such a resolution — rather than a
single invertible witness — is what makes the necessity direction of Proposition 8.4 work. -/
private theorem exists_halfTurn_twist_resolution (alpha : Fin 3) :
    ∃ M₁ A₁ M₂ A₂ M₃ A₃ : Matrix (Fin 3) (Fin 3) ℂ,
      M₁ * (A₁ - spinOneHalfTurnS alpha * A₁ * spinOneHalfTurnS alpha)
        + M₂ * (A₂ - spinOneHalfTurnS alpha * A₂ * spinOneHalfTurnS alpha)
        + M₃ * (A₃ - spinOneHalfTurnS alpha * A₃ * spinOneHalfTurnS alpha) = 1 := by
  fin_cases alpha
  · exact ⟨!![1, 0, 0; 0, 0, 0; 0, 0, -1], !![1, 0, 0; 0, 0, 0; 0, 0, 0],
      !![0, 0, 0; 1, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0], 0, 0, by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [spinOneHalfTurnS, spinOnePiRot1]⟩
  · exact ⟨!![1, 0, 0; 0, 0, 0; 0, 0, -1], !![1, 0, 0; 0, 0, 0; 0, 0, 0],
      !![0, 0, 0; 1, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0], 0, 0, by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [spinOneHalfTurnS, spinOnePiRot2]⟩
  · exact ⟨!![0, 1 / 2, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
      !![0, 0, 0; 1 / 2, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0],
      !![0, 0, 0; 0, 0, 0; 0, 1 / 2, 0], !![0, 0, 0; 0, 0, 1; 0, 0, 0], by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [spinOneHalfTurnS, spinOnePiRot3]⟩

/-- **The vanishing engine**: if left multiplication by every half-turn-twisted difference
`A - u_α A u_α` at the site `z` annihilates `C`, then `C = 0`.  This is the step that converts
"the transformed monomial keeps a string" into "the transformed monomial is not local". -/
theorem eq_zero_of_onSiteS_twist (alpha : Fin 3) (z : Fin L) {C : ManyBodyOpS (Fin L) 2}
    (h : ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      onSiteS z (A - spinOneHalfTurnS alpha * A * spinOneHalfTurnS alpha) * C = 0) :
    C = 0 := by
  obtain ⟨M₁, A₁, M₂, A₂, M₃, A₃, hres⟩ := exists_halfTurn_twist_resolution alpha
  have key : ∀ M A : Matrix (Fin 3) (Fin 3) ℂ,
      onSiteS z (M * (A - spinOneHalfTurnS alpha * A * spinOneHalfTurnS alpha)) * C = 0 := by
    intro M A
    rw [← onSiteS_mul_onSiteS_same, mul_assoc, h A, mul_zero]
  calc C = onSiteS z (1 : Matrix (Fin 3) (Fin 3) ℂ) * C := by rw [onSiteS_one, one_mul]
    _ = 0 := by
        rw [← hres, onSiteS_add, onSiteS_add, add_mul, add_mul, key M₁ A₁, key M₂ A₂, key M₃ A₃]
        simp

/-! ## Nonvanishing of on-site products -/

/-- Site embedding commutes with a three-term sum. -/
private theorem onSiteS_sum_fin_three (z : Fin L) (f : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) :
    (∑ b : Fin 3, onSiteS z (f b) : ManyBodyOpS (Fin L) 2) = onSiteS z (∑ b : Fin 3, f b) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, onSiteS_add, onSiteS_add]

/-- A matrix unit resolution: for a matrix with a nonzero `(p, q)` entry, the maps
`X ↦ E_{b p} X E_{q b}` recover the identity after rescaling. -/
private theorem sum_single_conj_eq_one {A : Matrix (Fin 3) (Fin 3) ℂ} {p q : Fin 3}
    (h : A p q ≠ 0) :
    ∑ b : Fin 3, (A p q)⁻¹ • (Matrix.single b p (1 : ℂ) * A * Matrix.single q b (1 : ℂ)) = 1 := by
  have hstep : ∀ b : Fin 3,
      (A p q)⁻¹ • (Matrix.single b p (1 : ℂ) * A * Matrix.single q b (1 : ℂ))
        = Matrix.single b b (1 : ℂ) := by
    intro b
    rw [Matrix.single_mul_mul_single, Matrix.smul_single, one_mul, mul_one, smul_eq_mul,
      inv_mul_cancel₀ h]
  rw [Finset.sum_congr rfl fun b _ => hstep b, Matrix.sum_single_one]

/-- **An ordered product of site embeddings at distinct sites is nonzero** whenever each embedded
matrix is nonzero.  This is the tensor-factor nonvanishing input of the boundary example. -/
private theorem onSiteS_listProd_ne_zero :
    ∀ l : List (Fin L × Matrix (Fin 3) (Fin 3) ℂ), (l.map Prod.fst).Nodup →
      (∀ p ∈ l, p.2 ≠ 0) → (l.map fun p => onSiteS p.1 p.2).prod ≠ 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hnd hne hzero
    rw [List.map_cons, List.prod_cons] at hzero
    obtain ⟨p, q, hpq⟩ : ∃ p q : Fin 3, a.2 p q ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne a (List.mem_cons_self ..) (by ext p q; simp [hcon p q])
    have hcomm : ∀ B : Matrix (Fin 3) (Fin 3) ℂ,
        Commute ((t.map fun p => onSiteS p.1 p.2).prod) (onSiteS a.1 B) := by
      intro B
      refine Commute.list_prod_left _ _ ?_
      intro Y hY
      rw [List.mem_map] at hY
      obtain ⟨r, hr, rfl⟩ := hY
      refine onSiteS_commute_of_ne ?_ _ _
      intro hra
      rw [List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (hra ▸ List.mem_map_of_mem hr)
    have hkey : ∀ b : Fin 3,
        (a.2 p q)⁻¹ • (onSiteS a.1 (Matrix.single b p (1 : ℂ)) *
          (onSiteS a.1 a.2 * (t.map fun p => onSiteS p.1 p.2).prod) *
            onSiteS a.1 (Matrix.single q b (1 : ℂ)))
          = onSiteS a.1 ((a.2 p q)⁻¹ • (Matrix.single b p (1 : ℂ) * a.2 *
              Matrix.single q b (1 : ℂ))) * (t.map fun p => onSiteS p.1 p.2).prod := by
      intro b
      rw [onSiteS_smul, Matrix.smul_mul]
      congr 1
      calc onSiteS a.1 (Matrix.single b p (1 : ℂ)) *
              (onSiteS a.1 a.2 * (t.map fun p => onSiteS p.1 p.2).prod) *
              onSiteS a.1 (Matrix.single q b (1 : ℂ))
          = onSiteS a.1 (Matrix.single b p (1 : ℂ)) * onSiteS a.1 a.2 *
              ((t.map fun p => onSiteS p.1 p.2).prod *
                onSiteS a.1 (Matrix.single q b (1 : ℂ))) := by noncomm_ring
        _ = onSiteS a.1 (Matrix.single b p (1 : ℂ)) * onSiteS a.1 a.2 *
              (onSiteS a.1 (Matrix.single q b (1 : ℂ)) *
                (t.map fun p => onSiteS p.1 p.2).prod) := by rw [(hcomm _).eq]
        _ = onSiteS a.1 (Matrix.single b p (1 : ℂ) * a.2 * Matrix.single q b (1 : ℂ)) *
              (t.map fun p => onSiteS p.1 p.2).prod := by
            rw [onSiteS_mul_onSiteS_same, ← mul_assoc, onSiteS_mul_onSiteS_same]
    have hsum : (t.map fun p => onSiteS p.1 p.2).prod = 0 := by
      have h0 : ∑ b : Fin 3, (a.2 p q)⁻¹ • (onSiteS a.1 (Matrix.single b p (1 : ℂ)) *
          (onSiteS a.1 a.2 * (t.map fun p => onSiteS p.1 p.2).prod) *
            onSiteS a.1 (Matrix.single q b (1 : ℂ))) = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [hzero]
        simp
      rw [Finset.sum_congr rfl fun b _ => hkey b, ← Finset.sum_mul, onSiteS_sum_fin_three,
        sum_single_conj_eq_one hpq, onSiteS_one, one_mul] at h0
      exact h0
    rw [List.map_cons, List.nodup_cons] at hnd
    exact ih hnd.2 (fun r hr => hne r (List.mem_cons_of_mem _ hr)) hsum


/-! ## Nonvanishing of the book's example monomials -/

/-- No spin-one half turn is the identity: each of `u_1, u_2, u_3` has a `-1` on the diagonal. -/
private theorem spinOneHalfTurnS_ne_one (alpha : Fin 3) :
    spinOneHalfTurnS alpha ≠ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  fin_cases alpha
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    norm_num [spinOneHalfTurnS, spinOnePiRot1, Matrix.one_apply] at h11
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    norm_num [spinOneHalfTurnS, spinOnePiRot2, Matrix.one_apply] at h11
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num [spinOneHalfTurnS, spinOnePiRot3, Matrix.one_apply] at h00

/-- The square of a spin-one axis operator is nonzero: otherwise `u_α = 1 - 2 (Ŝ^{(α)})²` would be
the identity. -/
private theorem spinOneAxisS_sq_ne_zero (alpha : Fin 3) :
    spinOneAxisS alpha * spinOneAxisS alpha ≠ 0 := by
  intro h
  refine spinOneHalfTurnS_ne_one alpha ?_
  rw [spinOneHalfTurnS_eq_one_sub_two_smul_sq, pow_two, h, smul_zero, sub_zero]

/-- Each spin-one axis operator is nonzero. -/
private theorem spinOneAxisS_ne_zero (alpha : Fin 3) : spinOneAxisS alpha ≠ 0 := fun h =>
  spinOneAxisS_sq_ne_zero alpha (by rw [h, mul_zero])

/-- **Verification viewpoint 4 (the sign law on the book's own examples, p. 250).** The word
`Ŝ_x^{(1)} Ŝ_{x+1}^{(2)} Ŝ_{x+2}^{(3)}` has axis counts `n₁ = n₂ = n₃ = 1`, so both parities
`p_L = n₂ + n₃ = 2` and `p_R = n₁ + n₂ = 2` are even and it **is** Z₂ × Z₂ invariant.  The word
`Ŝ_x^{(1)} Ŝ_{x+1}^{(2)} (Ŝ_{x+2}^{(3)})²` has `n₁ = n₂ = 1`, `n₃ = 2`, so `p_L = n₂ + n₃ = 3` is
odd and it is **not** Z₂ × Z₂ invariant.  The second half genuinely needs the monomial to be
nonzero, which is where the tensor-factor nonvanishing enters. -/
theorem spinMonomialS_examples_sign_law {L : ℕ} (x : Fin L) (hx : x.val + 2 < L) :
    IsZ2Z2Invariant
        (spinMonomialS [(x, (0 : Fin 3)), (⟨x.val + 1, by omega⟩, (1 : Fin 3)),
          (⟨x.val + 2, hx⟩, (2 : Fin 3))])
      ∧ ¬ IsZ2Z2Invariant
        (spinMonomialS [(x, (0 : Fin 3)), (⟨x.val + 1, by omega⟩, (1 : Fin 3)),
          (⟨x.val + 2, hx⟩, (2 : Fin 3)), (⟨x.val + 2, hx⟩, (2 : Fin 3))]) := by
  refine ⟨isZ2Z2Invariant_spinMonomialS_of_even _ ?_, ?_⟩
  · intro alpha
    fin_cases alpha <;> exact ⟨1, rfl⟩
  · intro hinv
    have hform : spinMonomialS [(x, (0 : Fin 3)), (⟨x.val + 1, by omega⟩, (1 : Fin 3)),
          (⟨x.val + 2, hx⟩, (2 : Fin 3)), (⟨x.val + 2, hx⟩, (2 : Fin 3))]
        = ([(x, spinOneAxisS 0), ((⟨x.val + 1, by omega⟩ : Fin L), spinOneAxisS 1),
            ((⟨x.val + 2, hx⟩ : Fin L), spinOneAxisS 2 * spinOneAxisS 2)].map
              fun p => onSiteS p.1 p.2).prod := by
      simp only [spinMonomialS, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        spinSSiteComponentS_eq_onSiteS, mul_one]
      rw [onSiteS_mul_onSiteS_same]
    have hne : spinMonomialS [(x, (0 : Fin 3)), (⟨x.val + 1, by omega⟩, (1 : Fin 3)),
        (⟨x.val + 2, hx⟩, (2 : Fin 3)), (⟨x.val + 2, hx⟩, (2 : Fin 3))] ≠ 0 := by
      rw [hform]
      refine onSiteS_listProd_ne_zero _ ?_ ?_
      · have h1 : x ≠ (⟨x.val + 1, by omega⟩ : Fin L) := by
          intro he
          have hv : x.val = x.val + 1 := congrArg Fin.val he
          omega
        have h2 : x ≠ (⟨x.val + 2, hx⟩ : Fin L) := by
          intro he
          have hv : x.val = x.val + 2 := congrArg Fin.val he
          omega
        have h3 : (⟨x.val + 1, by omega⟩ : Fin L) ≠ (⟨x.val + 2, hx⟩ : Fin L) := by
          intro he
          have hv : x.val + 1 = x.val + 2 := congrArg Fin.val he
          omega
        simp [h1, h2, h3]
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact spinOneAxisS_ne_zero 0
        · exact spinOneAxisS_ne_zero 1
        · exact spinOneAxisS_sq_ne_zero 2
    obtain ⟨r, hr⟩ := even_countP_of_isZ2Z2Invariant hne hinv 0
    simp only [List.countP_cons, List.countP_nil] at hr
    norm_num at hr
    omega

end LatticeSystem.Quantum
