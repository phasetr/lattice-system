import LatticeSystem.Quantum.SpinS.KennedyTasakiTransformation

/-!
# Tasaki §8.2.2: the Kennedy–Tasaki transformation rules (8.2.12)–(8.2.14)

Conjugating a single spin component by `Û_KT` attaches at most two **strings** of half turns
(Tasaki (8.2.12)–(8.2.14), p. 243):

  `Û_KT Ŝ_x^{(1)} Û_KT = Ŝ_x^{(1)} ∏_{v > x} u_1^{(v)}`,
  `Û_KT Ŝ_x^{(2)} Û_KT = (∏_{u < x} u_3^{(u)}) Ŝ_x^{(2)} (∏_{v > x} u_1^{(v)})`,
  `Û_KT Ŝ_x^{(3)} Û_KT = (∏_{u < x} u_3^{(u)}) Ŝ_x^{(3)}`.

So a letter creates a **left axis-3 string** exactly when its axis is not `1`, and a **right axis-1
string** exactly when its axis is not `3` (in Lean's `Fin 3` indexing: not `0` and not `2`
respectively).  The proof is a single induction over the columns of `Û_KT`: a column `v < x` acts
trivially, the column `v = x` produces the left string, and each column `v > x` contributes one
right-string factor.  Each of those three steps is one instance of the conjugation lemmas for the
half-turn control polynomial.

Both strings are **half-open** — `u < x` on the left, `v > x` on the right — so they are *empty* at
the corresponding edge of an open chain.  That is the mechanism behind the boundary counterexample
which forces the interior-window hypothesis of the single-monomial form of Proposition 8.4.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2, eqs. (8.2.12)–(8.2.15) and (8.2.18)–(8.2.20), pp. 243–244.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **right string** `∏_{v > m} u_1^{(v)}` of the Kennedy–Tasaki rules (8.2.12)–(8.2.13): the
axis-1 half turn on every site strictly to the right of `m`.  Its left companion is the axis-3
prefix rotation `edgeStringPrefixRotationS L 2 m` of §8.1.2, which is reused rather than
restated. -/
noncomputable def ktRightStringS (L : ℕ) (m : ℕ) : ManyBodyOpS (Fin L) 2 :=
  halfTurnRegionS L 0 (Finset.univ.filter fun y : Fin L => m < y.val)

/-- The right string is an involution. -/
theorem ktRightStringS_mul_self (L m : ℕ) : ktRightStringS L m * ktRightStringS L m = 1 :=
  halfTurnRegionS_mul_self L 0 _

/-- **Sites strictly right of `m` are conjugated by the axis-1 half turn.** -/
theorem ktRightStringS_conj_onSiteS_of_lt (L : ℕ) {m : ℕ} {z : Fin L} (h : m < z.val)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ktRightStringS L m * onSiteS z A * ktRightStringS L m
      = onSiteS z (spinOneHalfTurnS 0 * A * spinOneHalfTurnS 0) :=
  halfTurnRegionS_conj_onSiteS_of_mem L 0 _ (by simpa using h) A

/-- **Sites at or left of `m` are untouched by the right string.** -/
theorem ktRightStringS_commute_onSiteS_of_le (L : ℕ) {m : ℕ} {z : Fin L} (h : z.val ≤ m)
    (A : Matrix (Fin 3) (Fin 3) ℂ) : Commute (ktRightStringS L m) (onSiteS z A) :=
  halfTurnRegionS_commute_onSiteS_of_not_mem L 0 _ (by simpa using Nat.not_lt.mpr h) A

/-! ## Conjugation by a single column -/

/-- **A column to the left of the site acts trivially**: for `v < x` neither the control
`∏_{u < v} u_3^{(u)}` nor the target `u_1^{(v)}` of the column touches the site `x`. -/
private theorem ktColumnS_conj_component_of_lt (L : ℕ) (alpha : Fin 3) {x v : Fin L}
    (h : v.val < x.val) :
    ktColumnS L v * spinSSiteComponentS alpha x * ktColumnS L v
      = spinSSiteComponentS alpha x := by
  have hvx : v ≠ x := by intro he; subst he; omega
  rw [ktColumnS_eq_halfTurnCtrlS, spinSSiteComponentS_eq_onSiteS]
  exact halfTurnCtrlS_conj_of_commute (ktColumnTarget_commute_control L v)
    (edgeStringPrefixRotationS_mul_self L 2 v.val) (onSiteS_spinOneHalfTurnS_mul_self L 0 v)
    (edgeStringPrefixRotationS_commute_onSiteS_of_le L 2 v.val (le_of_lt h) _)
    (onSiteS_commute_of_ne hvx _ _)

/-- **The column at the site produces the left string**: the axis-1 half turn at `x` flips
`Ŝ_x^{(α)}` for `α ≠ 1` (Lean index `α ≠ 0`), so the column's control — the axis-3 prefix rotation
`∏_{u < x} u_3^{(u)}` — is left behind.  This is the left string of (8.2.13)–(8.2.14). -/
private theorem ktColumnS_conj_component_self (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    ktColumnS L x * spinSSiteComponentS alpha x * ktColumnS L x
      = (if alpha = 0 then 1 else edgeStringPrefixRotationS L 2 x.val)
        * spinSSiteComponentS alpha x := by
  have hGX : Commute (edgeStringPrefixRotationS L 2 x.val)
      (onSiteS x (spinOneAxisS alpha) : ManyBodyOpS (Fin L) 2) :=
    edgeStringPrefixRotationS_commute_onSiteS_of_le L 2 x.val (le_refl _) _
  have hTX : (onSiteS x (spinOneHalfTurnS 0) : ManyBodyOpS (Fin L) 2)
      * onSiteS x (spinOneAxisS alpha) * onSiteS x (spinOneHalfTurnS 0)
      = onSiteS x ((if (0 : Fin 3) = alpha then (1 : ℂ) else -1) • spinOneAxisS alpha) := by
    rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same, spinOneHalfTurnS_conj_spinOneAxisS]
  rw [ktColumnS_eq_halfTurnCtrlS, spinSSiteComponentS_eq_onSiteS]
  by_cases h0 : alpha = 0
  · subst h0
    rw [if_pos rfl, one_mul]
    refine halfTurnCtrlS_conj_of_commute (ktColumnTarget_commute_control L x)
      (edgeStringPrefixRotationS_mul_self L 2 x.val) (onSiteS_spinOneHalfTurnS_mul_self L 0 x)
      hGX ?_
    change (onSiteS x (spinOneHalfTurnS 0) : ManyBodyOpS (Fin L) 2) *
        onSiteS x (spinOneAxisS 0) = onSiteS x (spinOneAxisS 0) * onSiteS x (spinOneHalfTurnS 0)
    rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same,
      (spinOneHalfTurnS_commute_spinOneAxisS 0).eq]
  · rw [if_neg h0]
    have hanti : (onSiteS x (spinOneHalfTurnS 0) : ManyBodyOpS (Fin L) 2)
        * onSiteS x (spinOneAxisS alpha) * onSiteS x (spinOneHalfTurnS 0)
        = -(onSiteS x (spinOneAxisS alpha)) := by
      rw [hTX, if_neg (Ne.symm h0), neg_smul, one_smul, onSiteS_neg]
    rw [halfTurnCtrlS_conj_of_target_anticomm (ktColumnTarget_commute_control L x)
      (edgeStringPrefixRotationS_mul_self L 2 x.val) (onSiteS_spinOneHalfTurnS_mul_self L 0 x)
      hGX hanti]
    exact hGX.eq.symm

/-- **A column to the right of the site contributes one right-string factor**: for `v > x` the
column's control `∏_{u < v} u_3^{(u)}` flips `Ŝ_x^{(α)}` for `α ≠ 3` (Lean index `α ≠ 2`), leaving
its target `u_1^{(v)}` behind.  This is one factor of the right string of (8.2.12)–(8.2.13). -/
private theorem ktColumnS_conj_component_of_gt (L : ℕ) (alpha : Fin 3) {x v : Fin L}
    (h : x.val < v.val) :
    ktColumnS L v * spinSSiteComponentS alpha x * ktColumnS L v
      = spinSSiteComponentS alpha x
        * (if alpha = 2 then 1 else onSiteS v (spinOneHalfTurnS 0)) := by
  have hvx : v ≠ x := by intro he; subst he; omega
  have hTX : Commute (onSiteS v (spinOneHalfTurnS 0) : ManyBodyOpS (Fin L) 2)
      (onSiteS x (spinOneAxisS alpha)) := onSiteS_commute_of_ne hvx _ _
  have hGX : edgeStringPrefixRotationS L 2 v.val * onSiteS x (spinOneAxisS alpha)
        * edgeStringPrefixRotationS L 2 v.val
      = onSiteS x ((if (2 : Fin 3) = alpha then (1 : ℂ) else -1) • spinOneAxisS alpha) := by
    rw [edgeStringPrefixRotationS_conj_onSiteS_of_lt L 2 v.val h,
      spinOneHalfTurnS_conj_spinOneAxisS]
  rw [ktColumnS_eq_halfTurnCtrlS, spinSSiteComponentS_eq_onSiteS]
  by_cases h2 : alpha = 2
  · subst h2
    rw [if_pos rfl, mul_one]
    refine halfTurnCtrlS_conj_of_commute (ktColumnTarget_commute_control L v)
      (edgeStringPrefixRotationS_mul_self L 2 v.val) (onSiteS_spinOneHalfTurnS_mul_self L 0 v)
      ?_ hTX
    have hfix : edgeStringPrefixRotationS L 2 v.val * onSiteS x (spinOneAxisS 2)
        * edgeStringPrefixRotationS L 2 v.val = onSiteS x (spinOneAxisS 2) := by
      rw [hGX, if_pos rfl, one_smul]
    have hstep := congrArg (fun M => M * edgeStringPrefixRotationS L 2 v.val) hfix
    simp only [mul_assoc, edgeStringPrefixRotationS_mul_self, mul_one] at hstep
    exact hstep
  · rw [if_neg h2]
    refine halfTurnCtrlS_conj_of_control_anticomm (ktColumnTarget_commute_control L v)
      (edgeStringPrefixRotationS_mul_self L 2 v.val) (onSiteS_spinOneHalfTurnS_mul_self L 0 v)
      ?_ hTX
    rw [hGX, if_neg (Ne.symm h2), neg_smul, one_smul, onSiteS_neg]

/-! ## Conjugation by a sublist of columns -/

/-- The induction behind (8.2.12)–(8.2.14): conjugating `Ŝ_x^{(α)}` by the ordered product of the
columns indexed by a duplicate-free list `l` leaves the left string iff `x ∈ l` and `α ≠ 0`, and one
right-string factor for each `v ∈ l` with `v > x` (none when `α = 2`). -/
private theorem ktColumnListProd_conj_component (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    ∀ l : List (Fin L), l.Nodup →
      (l.map (ktColumnS L)).prod * spinSSiteComponentS alpha x * (l.map (ktColumnS L)).prod
        = (if x ∈ l then (if alpha = 0 then 1 else edgeStringPrefixRotationS L 2 x.val) else 1)
          * spinSSiteComponentS alpha x
          * halfTurnRegionS L 0
              (if alpha = 2 then ∅ else l.toFinset.filter fun v => x.val < v.val) := by
  intro l
  induction l with
  | nil => intro _; simp [halfTurnRegionS_empty]
  | cons c t ih =>
    intro hl
    rw [List.nodup_cons] at hl
    have hPinv : ktColumnS L c * ktColumnS L c = 1 := ktColumnS_mul_self L c
    have hPQ : Commute (ktColumnS L c) ((t.map (ktColumnS L)).prod) := by
      refine Commute.list_prod_right _ _ ?_
      intro Y hY
      rw [List.mem_map] at hY
      obtain ⟨w, _, rfl⟩ := hY
      exact ktColumnS_commute L c w
    have hfix : ∀ M : ManyBodyOpS (Fin L) 2, Commute (ktColumnS L c) M →
        ktColumnS L c * M * ktColumnS L c = M := by
      intro M hM
      rw [hM.eq, mul_assoc, hPinv, mul_one]
    have hcomLf : Commute (ktColumnS L c)
        (if x ∈ t then (if alpha = 0 then 1 else edgeStringPrefixRotationS L 2 x.val) else 1) := by
      split
      · split
        · exact Commute.one_right _
        · rw [edgeStringPrefixRotationS]
          exact ktColumnS_commute_halfTurnRegionS L c 2 _
      · exact Commute.one_right _
    have hcomRf : Commute (ktColumnS L c)
        (halfTurnRegionS L 0 (if alpha = 2 then ∅ else t.toFinset.filter fun v => x.val < v.val)) :=
      ktColumnS_commute_halfTurnRegionS L c 0 _
    have hsplit : ∀ Y : ManyBodyOpS (Fin L) 2,
        (ktColumnS L c * (t.map (ktColumnS L)).prod) * Y *
            (ktColumnS L c * (t.map (ktColumnS L)).prod)
          = ktColumnS L c * ((t.map (ktColumnS L)).prod * Y * (t.map (ktColumnS L)).prod) *
            ktColumnS L c := by
      intro Y
      have h1 : (t.map (ktColumnS L)).prod * Y * (ktColumnS L c * (t.map (ktColumnS L)).prod)
          = (t.map (ktColumnS L)).prod * Y * ((t.map (ktColumnS L)).prod * ktColumnS L c) := by
        rw [hPQ.eq]
      calc (ktColumnS L c * (t.map (ktColumnS L)).prod) * Y *
              (ktColumnS L c * (t.map (ktColumnS L)).prod)
          = ktColumnS L c * ((t.map (ktColumnS L)).prod * Y *
              (ktColumnS L c * (t.map (ktColumnS L)).prod)) := by noncomm_ring
        _ = ktColumnS L c * ((t.map (ktColumnS L)).prod * Y *
              ((t.map (ktColumnS L)).prod * ktColumnS L c)) := by rw [h1]
        _ = ktColumnS L c * ((t.map (ktColumnS L)).prod * Y * (t.map (ktColumnS L)).prod) *
              ktColumnS L c := by noncomm_ring
    rw [List.map_cons, List.prod_cons, hsplit, ih hl.2, conj_mul_of_mul_self hPinv,
      conj_mul_of_mul_self hPinv, hfix _ hcomLf, hfix _ hcomRf]
    rcases lt_trichotomy c.val x.val with hcx | hcx | hcx
    · have hne : x ≠ c := by intro he; subst he; omega
      have hmem : (x ∈ c :: t) = (x ∈ t) := by
        simp only [List.mem_cons, eq_iff_iff]
        constructor
        · rintro (rfl | h)
          · exact absurd rfl hne
          · exact h
        · exact Or.inr
      have hfil : (if alpha = 2 then (∅ : Finset (Fin L))
            else (c :: t).toFinset.filter fun v => x.val < v.val)
          = (if alpha = 2 then (∅ : Finset (Fin L))
            else t.toFinset.filter fun v => x.val < v.val) := by
        split
        · rfl
        · rw [List.toFinset_cons, Finset.filter_insert, if_neg (by omega)]
      rw [ktColumnS_conj_component_of_lt L alpha hcx, hfil]
      congr 2
      simp only [hmem]
    · have hcxe : c = x := Fin.ext hcx
      subst hcxe
      have hxt : c ∉ t := hl.1
      have hfil : (if alpha = 2 then (∅ : Finset (Fin L))
            else (c :: t).toFinset.filter fun v => c.val < v.val)
          = (if alpha = 2 then (∅ : Finset (Fin L))
            else t.toFinset.filter fun v => c.val < v.val) := by
        split
        · rfl
        · rw [List.toFinset_cons, Finset.filter_insert, if_neg (by omega)]
      rw [ktColumnS_conj_component_self L alpha c, hfil, if_neg (by simpa using hxt),
        if_pos (List.mem_cons_self ..), one_mul]
    · have hne : x ≠ c := by intro he; subst he; omega
      have hmem : (x ∈ c :: t) = (x ∈ t) := by
        simp only [List.mem_cons, eq_iff_iff]
        constructor
        · rintro (rfl | h)
          · exact absurd rfl hne
          · exact h
        · exact Or.inr
      rw [ktColumnS_conj_component_of_gt L alpha hcx]
      by_cases h2 : alpha = 2
      · subst h2
        rw [if_pos rfl, if_pos rfl, if_pos rfl, mul_one]
        congr 2
        simp only [hmem]
      · have hcnot : c ∉ t.toFinset.filter fun v => x.val < v.val := by
          simp only [Finset.mem_filter, List.mem_toFinset]
          exact fun hc => hl.1 hc.1
        simp only [if_neg h2]
        rw [List.toFinset_cons, Finset.filter_insert, if_pos hcx,
          halfTurnRegionS_insert L 0 _ hcnot,
          show ∀ A B C D : ManyBodyOpS (Fin L) 2, A * (B * C) * D = A * B * (C * D) from
            fun A B C D => by noncomm_ring]
        congr 2
        simp only [hmem]

/-! ## The transformation rules -/

/-- **Tasaki (8.2.12)–(8.2.14), p. 243**: conjugation of a single spin component by the
Kennedy–Tasaki unitary,

  `Û_KT Ŝ_x^{(α)} Û_KT = (∏_{u < x} u_3^{(u)})^{[α ≠ 1]} Ŝ_x^{(α)} (∏_{v > x} u_1^{(v)})^{[α ≠ 3]}`,

with the left axis-3 string present exactly when `α ≠ 1` (Lean index `α ≠ 0`) and the right axis-1
string present exactly when `α ≠ 3` (Lean index `α ≠ 2`).  Both strings are half-open, hence empty
at the corresponding edge of the chain. -/
theorem ktUnitaryS_conj_spinSSiteComponentS (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    ktUnitaryS L * spinSSiteComponentS alpha x * ktUnitaryS L
      = (if alpha = 0 then 1 else edgeStringPrefixRotationS L 2 x.val)
        * spinSSiteComponentS alpha x
        * (if alpha = 2 then 1 else ktRightStringS L x.val) := by
  have huniv : (List.finRange L).toFinset = (Finset.univ : Finset (Fin L)) := by
    ext y; simp
  have h := ktColumnListProd_conj_component L alpha x (List.finRange L) (List.nodup_finRange L)
  rw [← List.ofFn_eq_map] at h
  rw [ktUnitaryS, h, if_pos (List.mem_finRange x), huniv]
  by_cases h2 : alpha = 2
  · rw [if_pos h2, if_pos h2, halfTurnRegionS_empty]
  · rw [if_neg h2, if_neg h2, ktRightStringS]

/-- **Verification viewpoint 3 (Red regression guard for the interior-window hypothesis).**
(8.2.14) at `x = 0`: the left string `∏_{u < x} u_3^{(u)}` is empty at the left edge of the chain,
so the transformed operator is literally the untransformed `Ŝ_0^{(3)}`, not merely local in some
window around `0`.  This is the cheapest instance of the boundary counterexample: it is a direct
witness that the hypothesis `0 < a` of `tasaki_prop_8_4_local_monomial` is not removable, and it
must never be discharged by later weakening that hypothesis. -/
theorem ktUnitaryS_conj_site0_axis3 {L : ℕ} :
    ktUnitaryS (L + 1) * spinSSiteComponentS 2 (0 : Fin (L + 1)) * ktUnitaryS (L + 1)
      = spinSSiteComponentS 2 (0 : Fin (L + 1)) := by
  rw [ktUnitaryS_conj_spinSSiteComponentS, if_neg (by decide : ¬(2 : Fin 3) = 0), if_pos rfl,
    mul_one]
  change edgeStringPrefixRotationS (L + 1) 2 0 * _ = _
  rw [edgeStringPrefixRotationS_zero, one_mul]

/-- **Verification viewpoint 5 ((8.2.15), the book's worked cancellation, p. 243).**
`Û_KT Ŝ_x^{(3)} Ŝ_{x+1}^{(3)} Û_KT = -Ŝ_x^{(3)} Ŝ_{x+1}^{(3)}`: the two axis-3 strings generated by
(8.2.14) on each factor pair up and collapse via the `S = 1` identity
`Ŝ^{(α)} exp(iπ Ŝ^{(α)}) = -Ŝ^{(α)}`, leaving a bare sign rather than the identity. -/
theorem ktUnitaryS_conj_ss3_ss3_eq_neg {L : ℕ} (x : Fin L) (hx : x.val + 1 < L) :
    ktUnitaryS L * (spinSSiteComponentS 2 x * spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L)) *
        ktUnitaryS L
      = -(spinSSiteComponentS 2 x * spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L)) := by
  have hne : (2 : Fin 3) ≠ 0 := by decide
  have hcomm : Commute (edgeStringPrefixRotationS L 2 x.val)
      (spinSSiteComponentS 2 x) :=
    edgeStringPrefixRotationS_commute_component L 2 x.val x
  have hflip : spinSSiteComponentS 2 x * onSiteS x (spinOneHalfTurnS 2)
      = -spinSSiteComponentS 2 x := by
    rw [spinSSiteComponentS_eq_onSiteS, onSiteS_mul_onSiteS_same,
      spinOneAxisS_mul_spinOneHalfTurnS, onSiteS_neg]
  rw [conj_mul_of_mul_self (ktUnitaryS_sq L), ktUnitaryS_conj_spinSSiteComponentS,
    ktUnitaryS_conj_spinSSiteComponentS, if_neg hne, if_pos rfl, if_neg hne, if_pos rfl, mul_one,
    mul_one]
  have hsucc : edgeStringPrefixRotationS L 2 (⟨x.val + 1, hx⟩ : Fin L).val
      = onSiteS x (spinOneHalfTurnS 2) * edgeStringPrefixRotationS L 2 x.val :=
    edgeStringPrefixRotationS_succ L 2 x
  rw [hsucc]
  calc edgeStringPrefixRotationS L 2 x.val * spinSSiteComponentS 2 x *
        (onSiteS x (spinOneHalfTurnS 2) * edgeStringPrefixRotationS L 2 x.val *
          spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L))
      = edgeStringPrefixRotationS L 2 x.val *
          (spinSSiteComponentS 2 x * onSiteS x (spinOneHalfTurnS 2)) *
          edgeStringPrefixRotationS L 2 x.val *
          spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L) := by noncomm_ring
    _ = edgeStringPrefixRotationS L 2 x.val * (-spinSSiteComponentS 2 x) *
          edgeStringPrefixRotationS L 2 x.val *
          spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L) := by rw [hflip]
    _ = -(spinSSiteComponentS 2 x * spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L)) := by
        rw [mul_neg, neg_mul, neg_mul, hcomm.eq, mul_assoc, mul_assoc,
          ← mul_assoc (edgeStringPrefixRotationS L 2 x.val),
          edgeStringPrefixRotationS_mul_self, one_mul]

end LatticeSystem.Quantum
