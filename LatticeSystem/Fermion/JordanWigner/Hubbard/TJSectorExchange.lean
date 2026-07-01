import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopConfig
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopSignBetween
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin

/-!
# Tasaki 11.5: the exchange spin-flip on the t-J sector basis (Prop 11.24 PR-B1)

The exchange term `Ŝ_x·Ŝ_y` of the t-J Hamiltonian has the ladder part `½(Ŝ⁺_xŜ⁻_y + Ŝ⁻_xŜ⁺_y)`.
The off-diagonal piece `Ŝ⁺_i Ŝ⁻_j = ĉ†_{i↑}ĉ_{i↓}ĉ†_{j↓}ĉ_{j↑}` swaps the spins of an antiparallel
nearest-neighbour pair: acting on `|Φ_s⟩` with `s i = ↓`, `s j = ↑` (`i ≠ j`) it produces
`|Φ_{tJSpinSwap s i j}⟩` with **net Jordan–Wigner sign `+1`** — the two same-site
creation/annihilation pairs `(j↑,j↓)` and `(i↓,i↑)` each cancel (equal string exponents at adjacent
modes), with no dependence on the electrons between `i` and `j`.

This file builds the configuration-level identity; the operator action and the `+1` sign follow.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The spin-swap move on site-states: exchange the entries at sites `i` and `j`. -/
def tJSpinSwap (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) : Fin (N + 1) → Fin 3 :=
  fun k => if k = i then s j else if k = j then s i else s k

/-- An antiparallel pair (`s i = ↓`, `s j = ↑`) sits at distinct sites. -/
theorem tJ_spinSwap_ne (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) (hi : s i = 2)
    (hj : s j = 1) : i ≠ j := by
  rintro rfl; rw [hi] at hj; exact absurd hj (by decide)

/-- **Exchange config identity**: for `s i = ↓`, `s j = ↑`, the spinful occupation of
`tJSpinSwap s i j` is `tJConfigOf s` with the four orbitals `(j↑,j↓,i↓,i↑)` updated to
`(0,1,0,1)` — i.e. `i` becomes ↑ and `j` becomes ↓. -/
theorem tJConfigOf_tJSpinSwap (N : ℕ) (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1))
    (hi : s i = 2) (hj : s j = 1) :
    Function.update (Function.update (Function.update (Function.update (tJConfigOf N s)
        (spinfulIndex N j 0) 0) (spinfulIndex N j 1) 1) (spinfulIndex N i 1) 0)
        (spinfulIndex N i 0) 1
      = tJConfigOf N (tJSpinSwap s i j) := by
  have hij : i ≠ j := tJ_spinSwap_ne s i j hi hj
  funext k
  obtain ⟨t, r, rfl⟩ := exists_spinfulIndex N k
  simp only [Function.update_apply, spinfulIndex_eq_iff]
  rcases (show r = 0 ∨ r = 1 from tJ_fin2_eq r) with rfl | rfl <;>
    rcases eq_or_ne t i with rfl | hti <;> rcases eq_or_ne t j with rfl | htj <;>
    simp_all [tJConfigOf_apply_up, tJConfigOf_apply_down, tJSpinSwap]

/-! ### The same-site Jordan–Wigner string cancellations -/

/-- The modes below the successor `q` (`q.val = p.val + 1`) are those below `p` together with `p`.
-/
theorem tJ_filt_succ (M : ℕ) (p q : Fin (M + 1)) (hq : q.val = p.val + 1) :
    (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val))
      = insert p (Finset.univ.filter (fun k => k.val < p.val)) := by
  ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hk; rcases eq_or_ne k p with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by have : k.val ≠ p.val := fun he => h (Fin.ext he); omega)
  · rintro (rfl | hk) <;> omega

/-- `p` lies above all the modes strictly below it. -/
theorem tJ_p_notmem (M : ℕ) (p : Fin (M + 1)) :
    p ∉ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

/-- **Adjacent-pair cancellation, low mode first.**  For successive modes `p, q` (`q.val =
p.val + 1`), `jwSign p c · jwSign q (update c p 0) = 1`: the string exponents agree (the upper bound
only adds the zeroed mode `p`), so the parity doubles. -/
private theorem jwSign_succ_cancel_low (M : ℕ) (c : Fin (M + 1) → Fin 2) (p q : Fin (M + 1))
    (hq : q.val = p.val + 1) :
    jwSign M p c * jwSign M q (Function.update c p 0) = 1 := by
  rw [jwSign_eq_neg_one_pow, jwSign_eq_neg_one_pow, ← pow_add]
  have hB : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val)),
      ((Function.update c p 0) k).val)
      = ∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)), (c k).val := by
    have h1 : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val)),
        ((Function.update c p 0) k).val)
        = ((Function.update c p 0) p).val
          + ∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)),
              ((Function.update c p 0) k).val := by
      rw [tJ_filt_succ M p q hq]; exact Finset.sum_insert (tJ_p_notmem M p)
    rw [h1, Function.update_self]
    refine (zero_add _).trans (Finset.sum_congr rfl fun k hk => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [Function.update_of_ne (fun h => by rw [h] at hk; omega)]
  rw [hB, show ∀ a : ℕ, a + a = 2 * a from fun a => by ring, pow_mul]; norm_num

/-- **Adjacent-pair cancellation, high mode first.**  For successive modes `p, q` (`q.val =
p.val + 1`) with `c p = 0`, `jwSign q c · jwSign p (update c q 0) = 1`. -/
theorem jwSign_succ_cancel_high (M : ℕ) (c : Fin (M + 1) → Fin 2) (p q : Fin (M + 1))
    (hq : q.val = p.val + 1) (hcp : c p = 0) :
    jwSign M q c * jwSign M p (Function.update c q 0) = 1 := by
  rw [jwSign_eq_neg_one_pow, jwSign_eq_neg_one_pow, ← pow_add]
  have hA : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val)), (c k).val)
      = ∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)), (c k).val := by
    have h1 : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val)), (c k).val)
        = (c p).val + ∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)),
            (c k).val := by
      rw [tJ_filt_succ M p q hq]; exact Finset.sum_insert (tJ_p_notmem M p)
    rw [h1, hcp]; simp
  have hB : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)),
      ((Function.update c q 0) k).val)
      = ∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)), (c k).val :=
    Finset.sum_congr rfl fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [Function.update_of_ne (fun h => by rw [h] at hk; omega)]
  rw [hA, hB, show ∀ a : ℕ, a + a = 2 * a from fun a => by ring, pow_mul]; norm_num

/-! ### The exchange spin-flip operator action -/

/-- **The exchange ladder `Ŝ⁺_i Ŝ⁻_j` is sign-free on the sector basis.**  For an antiparallel pair
`s i = ↓`, `s j = ↑` (`i ≠ j`), `Ŝ⁺_i Ŝ⁻_j |Φ_s⟩ = |Φ_{tJSpinSwap s i j}⟩` with net Jordan–Wigner
sign `+1`: the two same-site creation/annihilation pairs `(j↑,j↓)` and `(i↓,i↑)` each contribute a
squared string sign `= 1`. -/
theorem fermionSiteSpinPlus_mul_Minus_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (hi : s i = 2) (hj : s j = 1) :
    (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSpinSwap s i j)) := by
  have hij : i ≠ j := tJ_spinSwap_ne s i j hi hj
  have hijm : spinfulIndex N i 0 ≠ spinfulIndex N j 0 := fun h =>
    hij ((spinfulIndex_eq_iff N i j 0 0).mp h).1
  -- the relevant orbital occupations of c = tJConfigOf s
  have hju : tJConfigOf N s (spinfulIndex N j 0) = 1 := by rw [tJConfigOf_apply_up, if_pos hj]
  have hjd : tJConfigOf N s (spinfulIndex N j 1) = 0 := by
    rw [tJConfigOf_apply_down, if_neg (by rw [hj]; decide)]
  have hid : tJConfigOf N s (spinfulIndex N i 1) = 1 := by rw [tJConfigOf_apply_down, if_pos hi]
  have hiu : tJConfigOf N s (spinfulIndex N i 0) = 0 := by
    rw [tJConfigOf_apply_up, if_neg (by rw [hi]; decide)]
  -- the successor relations between the same-site up/down orbital modes
  have hqj : (spinfulIndex N j 1).val = (spinfulIndex N j 0).val + 1 := by simp [spinfulIndex]
  have hqi : (spinfulIndex N i 1).val = (spinfulIndex N i 0).val + 1 := by simp [spinfulIndex]
  -- abbreviate the intermediate configs
  set c := tJConfigOf N s with hcdef
  set c1 := Function.update c (spinfulIndex N j 0) 0 with hc1
  set c2 := Function.update c1 (spinfulIndex N j 1) 1 with hc2
  set c3 := Function.update c2 (spinfulIndex N i 1) 0 with hc3
  -- orbital values through the updates (i ≠ j keeps the i-modes equal to c)
  have hc1jd : c1 (spinfulIndex N j 1) = 0 := by
    rw [hc1, Function.update_of_ne (by
      rw [ne_eq, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)), hjd]
  have hc2id : c2 (spinfulIndex N i 1) = 1 := by
    rw [hc2, Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 1 1).mp h).1),
      hc1, Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 1 0).mp h).1), hid]
  have hc3iu : c3 (spinfulIndex N i 0) = 0 := by
    rw [hc3, Function.update_of_ne (by
      rw [ne_eq, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)),
      hc2, Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 0 1).mp h).1),
      hc1, Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 0 0).mp h).1), hiu]
  have hc2iu : c2 (spinfulIndex N i 0) = 0 := by
    rw [hc2, Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 0 1).mp h).1),
      hc1, Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 0 0).mp h).1), hiu]
  -- the four single-mode actions
  have step1 : (fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j 0)).mulVec (basisVec c)
      = jwSign (2 * N + 1) (spinfulIndex N j 0) c • basisVec c1 := by
    rw [fermionMultiAnnihilation_mulVec_basisVec, if_pos hju]
  have step2 : (fermionMultiCreation (2 * N + 1) (spinfulIndex N j 1)).mulVec (basisVec c1)
      = jwSign (2 * N + 1) (spinfulIndex N j 1) c1 • basisVec c2 := by
    rw [fermionMultiCreation_mulVec_basisVec, if_pos hc1jd]
  have step3 : (fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 1)).mulVec (basisVec c2)
      = jwSign (2 * N + 1) (spinfulIndex N i 1) c2 • basisVec c3 := by
    rw [fermionMultiAnnihilation_mulVec_basisVec, if_pos hc2id]
  have step4 : (fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0)).mulVec (basisVec c3)
      = jwSign (2 * N + 1) (spinfulIndex N i 0) c3 • basisVec (tJConfigOf N (tJSpinSwap s i j)) :=
          by
    rw [fermionMultiCreation_mulVec_basisVec, if_pos hc3iu]
    congr 2
    rw [hc3, hc2, hc1, hcdef]; exact tJConfigOf_tJSpinSwap N s i j hi hj
  -- compose: split the operator product, push all scalars out, apply each action
  unfold fermionSiteSpinPlus fermionSiteSpinMinus fermionUpCreation fermionDownAnnihilation
    fermionDownCreation fermionUpAnnihilation
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    step1]
  simp only [Matrix.mulVec_smul]
  rw [step2]
  simp only [Matrix.mulVec_smul]
  rw [step3]
  simp only [Matrix.mulVec_smul]
  rw [step4, smul_smul, smul_smul, smul_smul]
  -- the net sign is (j-pair) · (i-pair) = 1 · 1
  rw [show jwSign (2 * N + 1) (spinfulIndex N j 0) c *
          jwSign (2 * N + 1) (spinfulIndex N j 1) c1 *
          jwSign (2 * N + 1) (spinfulIndex N i 1) c2 *
          jwSign (2 * N + 1) (spinfulIndex N i 0) c3
        = (jwSign (2 * N + 1) (spinfulIndex N j 0) c *
            jwSign (2 * N + 1) (spinfulIndex N j 1) c1) *
          (jwSign (2 * N + 1) (spinfulIndex N i 1) c2 *
            jwSign (2 * N + 1) (spinfulIndex N i 0) c3) from by ring,
    hc1, jwSign_succ_cancel_low (2 * N + 1) c (spinfulIndex N j 0) (spinfulIndex N j 1) hqj,
    hc3, jwSign_succ_cancel_high (2 * N + 1) c2 (spinfulIndex N i 0) (spinfulIndex N i 1) hqi
      hc2iu, one_mul, one_smul]

end LatticeSystem.Fermion
