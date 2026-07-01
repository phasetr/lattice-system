import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOccupationCount
import LatticeSystem.Math.FinCases
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopNN

/-!
# Tasaki 11.5: the wrap bond is sign-free for odd `Ne` (Prop 11.24 PR3c-7)

The d=1 cycle's wrap bond `{0, N}` gives a forward hop `0 → N` whose source and target orbitals are
*not* mode-adjacent: the Jordan–Wigner string between them runs over all the other electrons.  The
strictly-between occupation therefore equals `Ne − 1`, so the hop sign is `(-1)^(Ne-1) = +1` for
**odd** `Ne` — the filling parity Tasaki imposes.

The count `Ne − 1` comes from the three-way mode split (`sum_split_le_between_ge`) and the total
electron number (`tJConfigOf_total_count`): the boundary sums are `1` (the source) below and `0`
(the empty target) above.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The occupation of `tJConfigOf s` over modes at-or-above the `σ`-orbital of the last site `b`
(`b.val = N`) is `0` when `b` is empty: those modes all belong to the (empty) site `b`. -/
private theorem tJ_wrap_ge_eq_zero (N : ℕ) (s : Fin (N + 1) → Fin 3) (b : Fin (N + 1)) (σ : Fin 2)
    (hbN : b.val = N) (hsb : s b = 0) :
    (∑ k ∈ Finset.univ.filter (fun k => (spinfulIndex N b σ).val ≤ k.val),
      (tJConfigOf N s k).val) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, spinfulIndex] at hk
  obtain ⟨i, r, rfl⟩ := exists_spinfulIndex N k
  have hi : i = b := by
    have h2 : (spinfulIndex N i r).val = 2 * i.val + r.val := by simp [spinfulIndex]
    have hir := i.isLt; have hrr := r.isLt; have hσ := σ.isLt
    rw [h2] at hk
    exact Fin.ext (by omega)
  subst hi
  rcases fin2_eq_zero_or_one r with rfl | rfl
  · rw [tJConfigOf_apply_up, if_neg (by rw [hsb]; decide)]
    rfl
  · rw [tJConfigOf_apply_down, if_neg (by rw [hsb]; decide)]
    rfl

/-- The occupation of `tJConfigOf s` over modes below-or-at the up-orbital of the first site `a`
(`a.val = 0`) is `1` when `a` is ↑: that range is the single mode `0`, the (occupied) up-orbital. -/
private theorem tJ_wrap_uphop_le_eq_one (N : ℕ) (s : Fin (N + 1) → Fin 3) (a : Fin (N + 1))
    (ha0 : a.val = 0) (ha : s a = 1) :
    (∑ k ∈ Finset.univ.filter (fun k => k.val ≤ (spinfulIndex N a 0).val),
      (tJConfigOf N s k).val) = 1 := by
  have hq0 : (spinfulIndex N a 0).val = 0 := by simp [spinfulIndex, ha0]
  have hfilter : Finset.univ.filter (fun k => k.val ≤ (spinfulIndex N a 0).val)
      = {spinfulIndex N a 0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hq0]
    constructor
    · intro hk0; exact Fin.ext (by rw [hq0]; omega)
    · intro hk; rw [hk, hq0]
  rw [hfilter, Finset.sum_singleton, tJConfigOf_apply_up, if_pos ha]
  rfl

/-- **Wrap up-hop is sign-free for odd `Ne`.**  For the cycle's wrap bond (`a.val = 0`, `b.val =
N`),
source `a` ↑, target `b` empty, and an odd electron number `Ne = #↑ + #↓`, the strictly-between
occupation is `Ne − 1` (even), so `ĉ†_{b↑}ĉ_{a↑} |Φ_s⟩ = |Φ_{tJSiteHop s a b}⟩`. -/
theorem tJ_uphop_wrap_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s a = 1) (hsb : s b = 0)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N b 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 0)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s a b)) := by
  have hab : a.val < b.val := by omega
  have hqp : (spinfulIndex N a 0).val < (spinfulIndex N b 0).val := by
    simp only [spinfulIndex]; omega
  rw [tJ_uphop_forward_mulVec N s a b hab ha hsb]
  have hbtw : (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
      (tJConfigOf N s k).val) = Ne - 1 := by
    have hsplit := sum_split_le_between_ge (2 * N + 1) (tJConfigOf N s)
      (spinfulIndex N a 0) (spinfulIndex N b 0) hqp
    rw [tJ_wrap_uphop_le_eq_one N s a ha0 ha, tJ_wrap_ge_eq_zero N s b 0 hbN hsb,
      tJConfigOf_total_count, hNe] at hsplit
    set X := (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
      (tJConfigOf N s k).val) with hX
    omega
  rw [hbtw, (Nat.Odd.sub_odd hodd odd_one).neg_one_pow, one_smul]

/-- The occupation of `tJConfigOf s` over modes below-or-at the down-orbital of the first site `a`
(`a.val = 0`) is `1` when `a` is ↓: that range is the two orbitals of site `0`, of which only the
(occupied) down-orbital contributes. -/
private theorem tJ_wrap_downhop_le_eq_one (N : ℕ) (s : Fin (N + 1) → Fin 3) (a : Fin (N + 1))
    (ha0 : a.val = 0) (ha : s a = 2) :
    (∑ k ∈ Finset.univ.filter (fun k => k.val ≤ (spinfulIndex N a 1).val),
      (tJConfigOf N s k).val) = 1 := by
  have hq0 : (spinfulIndex N a 0).val = 0 := by simp [spinfulIndex, ha0]
  have hq1 : (spinfulIndex N a 1).val = 1 := by simp [spinfulIndex, ha0]
  have hne : spinfulIndex N a 0 ≠ spinfulIndex N a 1 := fun h =>
    absurd ((spinfulIndex_eq_iff N a a 0 1).mp h).2 (by decide)
  have hfilter : Finset.univ.filter (fun k => k.val ≤ (spinfulIndex N a 1).val)
      = {spinfulIndex N a 0, spinfulIndex N a 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hq1]
    constructor
    · intro hk1
      rcases Nat.lt_or_ge k.val 1 with h | h
      · exact Or.inl (Fin.ext (by rw [hq0]; omega))
      · exact Or.inr (Fin.ext (by rw [hq1]; omega))
    · rintro (hk | hk) <;> subst hk <;> omega
  rw [hfilter, Finset.sum_insert (by simp [Finset.mem_singleton, hne]), Finset.sum_singleton,
    tJConfigOf_apply_up, if_neg (by rw [ha]; decide), tJConfigOf_apply_down, if_pos ha]
  decide

/-- **Wrap down-hop is sign-free for odd `Ne`.**  For the cycle's wrap bond (`a.val = 0`,
`b.val = N`), source `a` ↓, target `b` empty, and an odd electron number `Ne = #↑ + #↓`, the
strictly-between occupation is `Ne − 1` (even), so `ĉ†_{b↓}ĉ_{a↓} |Φ_s⟩ = |Φ_{tJSiteHop s a b}⟩`. -/
theorem tJ_downhop_wrap_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s a = 2) (hsb : s b = 0)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N b 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 1)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s a b)) := by
  have hab : a.val < b.val := by omega
  have hqp : (spinfulIndex N a 1).val < (spinfulIndex N b 1).val := by
    simp only [spinfulIndex]; omega
  rw [tJ_downhop_forward_mulVec N s a b hab ha hsb]
  have hbtw : (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
      (tJConfigOf N s k).val) = Ne - 1 := by
    have hsplit := sum_split_le_between_ge (2 * N + 1) (tJConfigOf N s)
      (spinfulIndex N a 1) (spinfulIndex N b 1) hqp
    rw [tJ_wrap_downhop_le_eq_one N s a ha0 ha, tJ_wrap_ge_eq_zero N s b 1 hbN hsb,
      tJConfigOf_total_count, hNe] at hsplit
    set X := (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
      (tJConfigOf N s k).val) with hX
    omega
  rw [hbtw, (Nat.Odd.sub_odd hodd odd_one).neg_one_pow, one_smul]

end LatticeSystem.Fermion
