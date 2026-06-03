import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopAction
import Mathlib.Algebra.BigOperators.Fin

/-!
# Uniform-sign hole-filling action in the Tasaki basis (11.2.4)

This file proves the boxed result of Tasaki eq. (11.2.4): in the ordered
creation-operator basis `|Φ_{x,σ}⟩` of (11.2.3), a hole-filling hopping term
`ĉ†_{(x,s)} ĉ_{(z,s)}` (creating at the hole `x`, annihilating the spin-`s`
electron at an occupied site `z`) acts with a *uniform* sign `-1`:

  `ĉ†_{(x,s)} ĉ_{(z,s)} |Φ_{x,σ}⟩ = - |Φ_{z, σ_{z→x}}⟩`.

In the sign-free `basisVec` convention (file `HopAction.lean`) the same term
carries a configuration-dependent Jordan–Wigner sign `jwSign · jwSign`; the
content here is that, once the states are taken in the Tasaki basis, the four
fermion signs (the two basis signs `ε` of `|Φ_{x,σ}⟩` and `|Φ_{z,σ_{z→x}}⟩`
and the two hop string signs) combine to the constant `-1`. This is exactly
Tasaki's stated reason for the redundant ordered-creation construction, and it
is the uniform off-diagonal sign needed for the Perron–Frobenius step
(Theorems 11.5/11.7).

The sign computation reduces, via `jwSign = (-1)^{(occupied modes below)}`, to
the parity count

  `E₁ + E₂ + E₃ + E₄ = x + z + (z - [x<z]) + (x - [z<x]) = 2(x+z) - 1`,

which is odd because `x ≠ z` forces exactly one of `[x<z]`, `[z<x]` to hold.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.4), pp. 383-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Jordan–Wigner string sign as a parity of occupied modes -/

/-- The Jordan–Wigner string sign is `(-1)` raised to the number of occupied
modes strictly below `j`: `jwSign N j c = (-1)^{∑_{k < j} (c k).val}`. Each
factor `(if c k = 0 then 1 else -1)` equals `(-1)^{(c k).val}`. -/
theorem jwSign_eq_neg_one_pow (N : ℕ) (j : Fin (N + 1)) (c : Fin (N + 1) → Fin 2) :
    jwSign N j c =
      (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter
        (fun k => k.val < j.val), (c k).val) := by
  unfold jwSign
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  by_cases h : c k = 0
  · rw [h]; simp
  · have h1 : c k = 1 := Fin.ext (by
      have := (c k).isLt
      have : (c k).val ≠ 0 := fun hh => h (Fin.ext hh)
      omega)
    rw [h1]; simp

/-! ## Reindexing a sum over spin-orbitals to a double sum over sites -/

/-- Reindex a sum over the `2N+2` Jordan–Wigner modes into the double sum over
sites `t ∈ Fin (N+1)` and spin labels `r ∈ Fin 2`, via the bijection
`(t, r) ↦ spinfulIndex N t r`. -/
theorem sum_spinful_reindex {β : Type*} [AddCommMonoid β] (N : ℕ)
    (g : Fin (2 * N + 2) → β) :
    ∑ k : Fin (2 * N + 2), g k =
      ∑ t : Fin (N + 1), ∑ r : Fin 2, g (spinfulIndex N t r) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (fun k _ => (⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr
        (by have := k.isLt; omega)⟩,
      ⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩))
    (fun p _ => spinfulIndex N p.1 p.2)
    (fun a _ => Finset.mem_univ _) (fun a _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k _
    apply Fin.ext
    simp only [spinfulIndex]
    omega
  · intro p _
    obtain ⟨t, r⟩ := p
    have := r.isLt
    refine Prod.ext ?_ ?_ <;> apply Fin.ext <;> simp only [spinfulIndex] <;> omega
  · intro k _
    congr 1
    apply Fin.ext
    simp only [spinfulIndex]
    omega

/-- The exponent of a `jwSign` rewritten as a double site/spin sum below the
mode bound `b`. -/
private theorem exp_reindex (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) (b : ℕ) :
    (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k => k.val < b),
      (c k).val) =
      ∑ t : Fin (N + 1), ∑ r : Fin 2,
        if 2 * t.val + r.val < b then (c (spinfulIndex N t r)).val else 0 := by
  rw [Finset.sum_filter,
    sum_spinful_reindex N (fun k => if k.val < b then (c k).val else 0)]
  refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun r _ => ?_))
  simp only [spinfulIndex]

/-! ## Counting sites below a bound -/

/-- The number of sites with index value below `m ≤ N + 1` is `m`. -/
private theorem card_sites_lt (N m : ℕ) (hm : m ≤ N + 1) :
    ((Finset.univ : Finset (Fin (N + 1))).filter (fun t => t.val < m)).card = m := by
  refine Eq.trans (Finset.card_bij (fun t _ => t.val) ?_ ?_ ?_) (Finset.card_range m)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact Finset.mem_range.mpr ht
  · intro a _ b _ hab; exact Fin.ext hab
  · intro b hb
    rw [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, by simp [Finset.mem_filter, hb], rfl⟩

/-- The number of sites below `m ≤ N + 1` other than a fixed site `w`. -/
private theorem card_sites_lt_erase (N m : ℕ) (hm : m ≤ N + 1) (w : Fin (N + 1)) :
    ((Finset.univ : Finset (Fin (N + 1))).filter
        (fun t => t.val < m ∧ t ≠ w)).card = if w.val < m then m - 1 else m := by
  have heq : (Finset.univ.filter (fun t : Fin (N + 1) => t.val < m ∧ t ≠ w))
      = (Finset.univ.filter (fun t => t.val < m)).erase w := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [heq, Finset.card_erase_eq_ite, card_sites_lt N m hm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## The exponent of a single-electron-per-site configuration -/

/-- For a configuration that places one electron at orbital `orb t` on every
site `t ∉ holes` (and leaves the sites in `holes` empty), the parity exponent
of `jwSign` below the mode bound `b` equals the number of non-hole sites whose
occupied orbital index lies below `b`. -/
private theorem config_exp_eq_card (N : ℕ) (b : ℕ) (holes : Finset (Fin (N + 1)))
    (orb : Fin (N + 1) → Fin 2) (c : Fin (2 * N + 2) → Fin 2)
    (hc : ∀ (t : Fin (N + 1)) (r : Fin 2),
      (c (spinfulIndex N t r)).val =
        if t ∈ holes then 0 else if r = orb t then 1 else 0) :
    (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k => k.val < b),
      (c k).val) =
      ((Finset.univ : Finset (Fin (N + 1))).filter
        (fun t => t ∉ holes ∧ 2 * t.val + (orb t).val < b)).card := by
  rw [exp_reindex, Finset.card_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_two]
  simp only [hc]
  by_cases hh : t ∈ holes
  · simp [hh]
  · simp only [hh, if_false, not_false_eq_true, true_and]
    have ho : orb t = 0 ∨ orb t = 1 := by
      rcases orb t with ⟨ov, hov⟩; interval_cases ov
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ho with ho | ho <;> rw [ho] <;>
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, add_zero] <;>
      split_ifs <;> simp_all

/-! ## Auxiliary identities for the one-hole configuration -/

/-- Occupation-value form of the one-hole configuration, expressed in the
hole-set / orbital format consumed by `config_exp_eq_card`. -/
private theorem onehole_hc (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool)
    (t : Fin (N + 1)) (r : Fin 2) :
    (hubbardOneHoleConfig N x σ (spinfulIndex N t r)).val =
      if t ∈ ({x} : Finset (Fin (N + 1))) then 0
      else if r = (if σ t then (0 : Fin 2) else 1) then 1 else 0 := by
  rcases (show r = 0 ∨ r = 1 from by
    rcases r with ⟨rv, hrv⟩; interval_cases rv; exacts [Or.inl rfl, Or.inr rfl])
    with rfl | rfl
  · rw [hubbardOneHoleConfig_apply_up]
    by_cases hx : t = x <;> by_cases hσ : σ t <;>
      simp_all [Finset.mem_singleton, Fin.ext_iff]
  · rw [hubbardOneHoleConfig_apply_down]
    by_cases hx : t = x <;> by_cases hσ : σ t <;>
      simp_all [Finset.mem_singleton, Fin.ext_iff]

/-! ## The four parity exponents -/

/-- The Tasaki basis sign is the explicit parity `(-1)^x`: independent of the
spin configuration `σ`. There are exactly `x` electrons (one per site below `x`)
beneath the hole's up-orbital `2x` in the all-filled configuration. -/
theorem hubbardTasakiBasisSign_eq (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    hubbardTasakiBasisSign N x σ = (-1 : ℂ) ^ x.val := by
  unfold hubbardTasakiBasisSign
  rw [jwSign_eq_neg_one_pow]
  congr 1
  have hb : (spinfulIndex N x 0).val = 2 * x.val := by simp [spinfulIndex]
  rw [hb,
    config_exp_eq_card N (2 * x.val) ∅
      (fun t => if (Function.update σ x true) t then 0 else 1) _ (fun t r => by
        simp only [occupationOf, if_neg (Finset.notMem_empty t),
          mem_tasakiIndexList_iff]
        split_ifs <;> rfl)]
  rw [show ((Finset.univ : Finset (Fin (N + 1))).filter
      (fun t => t ∉ (∅ : Finset (Fin (N + 1))) ∧
        2 * t.val + (if (Function.update σ x true) t then (0 : Fin 2) else 1).val
          < 2 * x.val))
      = (Finset.univ : Finset (Fin (N + 1))).filter (fun t => t.val < x.val) from
    Finset.filter_congr (fun t _ => by
      simp only [Finset.notMem_empty, not_false_eq_true, true_and]
      have : (if (Function.update σ x true) t then (0 : Fin 2) else 1).val < 2 := Fin.isLt _
      omega)]
  exact card_sites_lt N x.val (by have := x.isLt; omega)

/-- Parity of the first hop string sign `jwSign` at the source orbital `(z, s)`
in `|Φ_{x,σ}⟩`: `(-1)` to the number of occupied sites below `z` other than the
hole `x`. -/
theorem hop_jwSign_source (N : ℕ) (x z : Fin (N + 1)) (σ : Fin (N + 1) → Bool)
    (s : Fin 2) (hxz : x ≠ z)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N z s) = 1) :
    jwSign (2 * N + 1) (spinfulIndex N z s) (hubbardOneHoleConfig N x σ) =
      (-1 : ℂ) ^ (if x.val < z.val then z.val - 1 else z.val) := by
  -- the source spin equals the orbital selected by `σ z`
  have hzx : z ≠ x := fun h => hxz h.symm
  have hoz : (if σ z then (0 : Fin 2) else 1) = s := by
    have h1 : (hubbardOneHoleConfig N x σ (spinfulIndex N z s)).val = 1 := by simp [hs]
    rw [onehole_hc] at h1
    simp only [Finset.mem_singleton, if_neg hzx] at h1
    by_cases h : s = (if σ z then (0 : Fin 2) else 1)
    · exact h.symm
    · rw [if_neg h] at h1; simp at h1
  rw [jwSign_eq_neg_one_pow]
  congr 1
  rw [config_exp_eq_card N (spinfulIndex N z s).val {x}
      (fun t => if σ t then 0 else 1) _ (fun t r => onehole_hc N x σ t r)]
  rw [show ((Finset.univ : Finset (Fin (N + 1))).filter
      (fun t => t ∉ ({x} : Finset (Fin (N + 1))) ∧
        2 * t.val + (if σ t then (0 : Fin 2) else 1).val < (spinfulIndex N z s).val))
      = (Finset.univ : Finset (Fin (N + 1))).filter
          (fun t => t.val < z.val ∧ t ≠ x) from
    Finset.filter_congr (fun t _ => by
      rw [Finset.mem_singleton]
      have hsv : s.val < 2 := s.isLt
      have hb : (spinfulIndex N z s).val = 2 * z.val + s.val := by simp [spinfulIndex]
      rw [hb]
      have ho : (if σ t then (0 : Fin 2) else 1).val < 2 := Fin.isLt _
      rcases lt_trichotomy t.val z.val with h | h | h
      · exact ⟨fun hk => ⟨by omega, hk.1⟩, fun hk => ⟨hk.2, by omega⟩⟩
      · have htz : t = z := Fin.ext h
        subst htz
        rw [hoz]
        exact ⟨fun hk => absurd hk.2 (by omega), fun hk => absurd hk.1 (by omega)⟩
      · exact ⟨fun hk => absurd hk.2 (by omega), fun hk => absurd hk.1 (by omega)⟩)]
  rw [card_sites_lt_erase N z.val (by have := z.isLt; omega) x]

/-- Parity of the second hop string sign `jwSign` at the target orbital `(x, s)`
in the configuration with the source electron removed: `(-1)` to the number of
occupied sites below `x` other than the source `z`. -/
theorem hop_jwSign_target (N : ℕ) (x z : Fin (N + 1)) (σ : Fin (N + 1) → Bool)
    (s : Fin 2) (hxz : x ≠ z)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N z s) = 1) :
    jwSign (2 * N + 1) (spinfulIndex N x s)
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N z s) 0) =
      (-1 : ℂ) ^ (if z.val < x.val then x.val - 1 else x.val) := by
  have hzx : z ≠ x := fun h => hxz h.symm
  have hoz : (if σ z then (0 : Fin 2) else 1) = s := by
    have h1 : (hubbardOneHoleConfig N x σ (spinfulIndex N z s)).val = 1 := by simp [hs]
    rw [onehole_hc] at h1
    simp only [Finset.mem_singleton, if_neg hzx] at h1
    by_cases h : s = (if σ z then (0 : Fin 2) else 1)
    · exact h.symm
    · rw [if_neg h] at h1; simp at h1
  rw [jwSign_eq_neg_one_pow]
  congr 1
  rw [config_exp_eq_card N (spinfulIndex N x s).val {x, z}
      (fun t => if σ t then 0 else 1) _ (fun t r => by
        rw [Function.update_apply]
        by_cases hk : spinfulIndex N t r = spinfulIndex N z s
        · obtain ⟨rfl, rfl⟩ := (spinfulIndex_eq_iff N t z r s).mp hk
          simp [Finset.mem_insert, Finset.mem_singleton]
        · rw [if_neg hk, onehole_hc]
          by_cases htz : t = z
          · have htx : t ≠ x := by rw [htz]; exact hzx
            have hrs : r ≠ (if σ t then (0 : Fin 2) else 1) := by
              rw [htz, hoz]; exact fun h => hk (by rw [htz, h])
            rw [if_neg (show t ∉ ({x} : Finset (Fin (N + 1))) by
                simp [Finset.mem_singleton, htx]),
              if_neg hrs,
              if_pos (show t ∈ ({x, z} : Finset (Fin (N + 1))) by
                simp [Finset.mem_insert, Finset.mem_singleton, htz])]
          · simp only [Finset.mem_insert, Finset.mem_singleton, htz, or_false])]
  rw [show ((Finset.univ : Finset (Fin (N + 1))).filter
      (fun t => t ∉ ({x, z} : Finset (Fin (N + 1))) ∧
        2 * t.val + (if σ t then (0 : Fin 2) else 1).val < (spinfulIndex N x s).val))
      = (Finset.univ : Finset (Fin (N + 1))).filter
          (fun t => t.val < x.val ∧ t ≠ z) from
    Finset.filter_congr (fun t _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      have hsv : s.val < 2 := s.isLt
      have ho : (if σ t then (0 : Fin 2) else 1).val < 2 := Fin.isLt _
      have hb : (spinfulIndex N x s).val = 2 * x.val + s.val := by simp [spinfulIndex]
      rw [hb]
      constructor
      · rintro ⟨⟨hnx, hnz⟩, hlt⟩
        have hnx' : t.val ≠ x.val := fun h => hnx (Fin.ext h)
        exact ⟨by omega, hnz⟩
      · rintro ⟨hlt, hnz⟩
        exact ⟨⟨fun h => by rw [h] at hlt; omega, hnz⟩, by omega⟩)]
  rw [card_sites_lt_erase N x.val (by have := x.isLt; omega) z]

/-! ## Uniform-sign hole-filling action (11.2.4) -/

/-- Tasaki eq. (11.2.4): in the Tasaki basis the hole-filling hopping term
`ĉ†_{(x,s)} ĉ_{(z,s)}` acts on `|Φ_{x,σ}⟩` with the uniform sign `-1`,
producing `-|Φ_{z, σ_{z→x}}⟩`. The four fermion signs (the two basis signs and
the two hop string signs) combine to the constant `-1` because the total parity
exponent `2(x+z) - 1` is odd. -/
theorem hubbardTasakiHop_mulVec (N : ℕ) (x z : Fin (N + 1)) (σ : Fin (N + 1) → Bool)
    (s : Fin 2) (hxz : x ≠ z)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N z s) = 1) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N x s) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N z s)).mulVec
        (hubbardTasakiBasisState N x σ) =
      - hubbardTasakiBasisState N z (hubbardSpinMove N σ x z) := by
  rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
    show basisVec (hubbardOneHoleConfig N x σ) = hubbardHardcoreBasisState N x σ from rfl,
    hubbardHop_mulVec_hardcoreBasisState N x z σ s hxz hs, smul_smul,
    hubbardTasakiBasisState_eq_smul_basisVec N z (hubbardSpinMove N σ x z),
    show basisVec (hubbardOneHoleConfig N z (hubbardSpinMove N σ x z))
      = hubbardHardcoreBasisState N z (hubbardSpinMove N σ x z) from rfl,
    ← neg_smul]
  congr 1
  -- scalar identity: ε(x,σ) · (hopSign₁ · hopSign₂) = - ε(z, σ_{z→x})
  rw [hubbardTasakiBasisSign_eq, hop_jwSign_source N x z σ s hxz hs,
    hop_jwSign_target N x z σ s hxz hs, hubbardTasakiBasisSign_eq]
  have hz2 : (-1 : ℂ) ^ z.val * (-1) ^ z.val = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨z.val, rfl⟩
  have key : (-1 : ℂ) ^ x.val *
      ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
        (-1) ^ (if z.val < x.val then x.val - 1 else x.val)) * (-1) ^ z.val = -1 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    refine Odd.neg_one_pow ?_
    rw [Nat.odd_iff]
    rcases lt_or_gt_of_ne (fun h => hxz (Fin.ext h)) with h | h
    · rw [if_pos h, if_neg (by omega)]; omega
    · rw [if_neg (by omega), if_pos h]; omega
  calc (-1 : ℂ) ^ x.val *
        ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
          (-1) ^ (if z.val < x.val then x.val - 1 else x.val))
      = (-1 : ℂ) ^ x.val *
        ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
          (-1) ^ (if z.val < x.val then x.val - 1 else x.val)) *
          ((-1) ^ z.val * (-1) ^ z.val) := by rw [hz2, mul_one]
    _ = ((-1 : ℂ) ^ x.val *
        ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
          (-1) ^ (if z.val < x.val then x.val - 1 else x.val)) * (-1) ^ z.val)
          * (-1) ^ z.val := by ring
    _ = -1 * (-1) ^ z.val := by rw [key]
    _ = -(-1 : ℂ) ^ z.val := by ring

end LatticeSystem.Fermion
