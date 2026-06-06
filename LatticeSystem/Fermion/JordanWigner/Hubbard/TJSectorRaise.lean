import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorExchange

/-!
# Tasaki 11.5: the single-site spin-raising operator is sign-free on the sector basis (Prop 11.24)

The per-site raising operator `Ŝ^+_x = ĉ†_{x↑} ĉ_{x↓}` acts on a t-J sector basis state with
**net Jordan–Wigner sign `+1`**: for `s x = ↓`, `Ŝ^+_x |Φ_s⟩ = |Φ_{s with x ↦ ↑}⟩`.  The
two orbitals `(x↑, x↓) = (2x, 2x+1)` are adjacent in the spinful Jordan–Wigner ordering
(`spinfulIndex N x σ = 2x + σ`), and the up-orbital `2x` is empty before the move, so the
two strings collapse (`jwSign_succ_cancel_high`).  This is the Marshall structure underpinning the
positivity of the iterated raising `(Ŝ^+)^m` used to lift the strictly-positive Perron–Frobenius
ground vector to a nonzero highest weight (E3b).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The modes below the successor `q` (`q.val = p.val + 1`) are those below `p` together with `p`.
Local copy of the `TJSectorExchange` private helper (module-boundary convention). -/
private theorem tJ_filt_succ (M : ℕ) (p q : Fin (M + 1)) (hq : q.val = p.val + 1) :
    (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val))
      = insert p (Finset.univ.filter (fun k => k.val < p.val)) := by
  ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hk; rcases eq_or_ne k p with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by have : k.val ≠ p.val := fun he => h (Fin.ext he); omega)
  · rintro (rfl | hk) <;> omega

/-- `p` lies above all the modes strictly below it. Local copy of the `TJSectorExchange` helper. -/
private theorem tJ_p_notmem (M : ℕ) (p : Fin (M + 1)) :
    p ∉ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

/-- **Adjacent-pair cancellation, high mode first.**  For successive modes `p, q`
(`q.val = p.val + 1`) with `c p = 0`, `jwSign q c · jwSign p (update c q 0) = 1`.  Local copy of the
`TJSectorExchange` private helper (module-boundary convention). -/
private theorem jwSign_succ_cancel_high (M : ℕ) (c : Fin (M + 1) → Fin 2) (p q : Fin (M + 1))
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

/-- **Single-site raise config identity**: for `s x = ↓`, the spinful occupation of `s` with `x`
raised to `↑` is `tJConfigOf s` with the down-orbital emptied and the up-orbital filled. -/
theorem tJConfigOf_update_raise (N : ℕ) (s : Fin (N + 1) → Fin 3) (x : Fin (N + 1)) (hx : s x = 2) :
    Function.update (Function.update (tJConfigOf N s) (spinfulIndex N x 1) 0) (spinfulIndex N x 0) 1
      = tJConfigOf N (Function.update s x 1) := by
  funext k
  obtain ⟨t, r, rfl⟩ := exists_spinfulIndex N k
  simp only [Function.update_apply, spinfulIndex_eq_iff]
  rcases (show r = 0 ∨ r = 1 from tJ_fin2_eq r) with rfl | rfl <;>
    rcases eq_or_ne t x with rfl | htx <;>
    simp_all [tJConfigOf_apply_up, tJConfigOf_apply_down]

/-- **The single-site raising operator `Ŝ^+_x` is sign-free on the sector basis.**  For `s x = ↓`,
`Ŝ^+_x |Φ_s⟩ = |Φ_{s with x ↦ ↑}⟩` with net Jordan–Wigner sign `+1`. -/
theorem fermionSiteSpinPlus_mulVec_tJConfigOf_of_down (N : ℕ) (s : Fin (N + 1) → Fin 3)
    (x : Fin (N + 1)) (hx : s x = 2) :
    (fermionSiteSpinPlus N x).mulVec (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (Function.update s x 1)) := by
  have hid : tJConfigOf N s (spinfulIndex N x 1) = 1 := by rw [tJConfigOf_apply_down, if_pos hx]
  have hiu : tJConfigOf N s (spinfulIndex N x 0) = 0 := by
    rw [tJConfigOf_apply_up, if_neg (by rw [hx]; decide)]
  have hqx : (spinfulIndex N x 1).val = (spinfulIndex N x 0).val + 1 := by simp [spinfulIndex]
  set c := tJConfigOf N s with hcdef
  set c1 := Function.update c (spinfulIndex N x 1) 0 with hc1
  have hc1iu : c1 (spinfulIndex N x 0) = 0 := by
    rw [hc1, Function.update_of_ne (by
      rw [ne_eq, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)), hiu]
  have step1 : (fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1)).mulVec (basisVec c)
      = jwSign (2 * N + 1) (spinfulIndex N x 1) c • basisVec c1 := by
    rw [fermionMultiAnnihilation_mulVec_basisVec, if_pos hid]
  have step2 : (fermionMultiCreation (2 * N + 1) (spinfulIndex N x 0)).mulVec (basisVec c1)
      = jwSign (2 * N + 1) (spinfulIndex N x 0) c1
          • basisVec (tJConfigOf N (Function.update s x 1)) := by
    rw [fermionMultiCreation_mulVec_basisVec, if_pos hc1iu]
    congr 2
    rw [hc1, hcdef]; exact tJConfigOf_update_raise N s x hx
  unfold fermionSiteSpinPlus fermionUpCreation fermionDownAnnihilation
  rw [← Matrix.mulVec_mulVec, step1]
  simp only [Matrix.mulVec_smul]
  rw [step2, smul_smul, hc1,
    jwSign_succ_cancel_high (2 * N + 1) c (spinfulIndex N x 0) (spinfulIndex N x 1) hqx hiu,
    one_smul]

/-- **The single-site raising operator annihilates a non-down site.**  When `s x ≠ ↓` the
down-orbital `x↓` is empty, so `ĉ_{x↓}` (hence `Ŝ^+_x`) kills `|Φ_s⟩`. -/
theorem fermionSiteSpinPlus_mulVec_tJConfigOf_of_not_down (N : ℕ) (s : Fin (N + 1) → Fin 3)
    (x : Fin (N + 1)) (hx : s x ≠ 2) :
    (fermionSiteSpinPlus N x).mulVec (basisVec (tJConfigOf N s)) = 0 := by
  have hid : tJConfigOf N s (spinfulIndex N x 1) = 0 := by
    rw [tJConfigOf_apply_down, if_neg hx]
  have hann : (fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1)).mulVec
      (basisVec (tJConfigOf N s)) = 0 := by
    rw [fermionMultiAnnihilation_mulVec_basisVec, if_neg (by rw [hid]; decide)]
  unfold fermionSiteSpinPlus fermionUpCreation fermionDownAnnihilation
  rw [← Matrix.mulVec_mulVec, hann, Matrix.mulVec_zero]

end LatticeSystem.Fermion
