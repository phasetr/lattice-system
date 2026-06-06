import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOccupationCount
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopBackward

/-!
# Tasaki 11.5: the leftward wrap hop is sign-free for odd `Ne` (Prop 11.24 PR-B7-3c)

The cycle's wrap bond `{0, N}` also carries the *leftward* hop `ĉ†_{0σ}ĉ_{Nσ}` (the electron hops
from the last site `N` to the first site `0`).  Like the rightward wrap hop, it is sign-free `+1` for
**odd** `Ne`: the strictly-between Jordan–Wigner occupation is `Ne − 1` (the empty target `0`
contributes nothing below, the occupied source `N` contributes one above), so the backward sign
parity collapses to `(-1)^(Ne-1) = +1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- Modes below-or-at the `σ`-orbital of the first site `a` (`a.val = 0`) are empty when `a` is
empty: those modes all belong to the empty site `0`. -/
private theorem tJ_bwrap_le_eq_zero (N : ℕ) (s : Fin (N + 1) → Fin 3) (a : Fin (N + 1)) (σ : Fin 2)
    (ha0 : a.val = 0) (hsa : s a = 0) :
    (∑ k ∈ Finset.univ.filter (fun k => k.val ≤ (spinfulIndex N a σ).val),
      (tJConfigOf N s k).val) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, spinfulIndex] at hk
  obtain ⟨i, r, rfl⟩ := exists_spinfulIndex N k
  have hi : i = a := by
    have h2 : (spinfulIndex N i r).val = 2 * i.val + r.val := by simp [spinfulIndex]
    have hrr := r.isLt; have hσ := σ.isLt
    rw [h2] at hk
    exact Fin.ext (by omega)
  subst hi
  rcases tJ_fin2_eq r with rfl | rfl
  · rw [tJConfigOf_apply_up, if_neg (by rw [hsa]; decide)]; rfl
  · rw [tJConfigOf_apply_down, if_neg (by rw [hsa]; decide)]; rfl

/-- Modes at-or-above the up-orbital of the last site `b` (`b.val = N`) sum to `1` when `b` is ↑:
the two site-`b` orbitals are up (occupied) and down (empty). -/
private theorem tJ_bwrap_ge_eq_one_up (N : ℕ) (s : Fin (N + 1) → Fin 3) (b : Fin (N + 1))
    (hbN : b.val = N) (hsb : s b = 1) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin (2 * N + 2) => (spinfulIndex N b 0).val ≤ k.val),
      (tJConfigOf N s k).val) = 1 := by
  have hne : spinfulIndex N b 0 ≠ spinfulIndex N b 1 := fun h =>
    absurd ((spinfulIndex_eq_iff N b b 0 1).mp h).2 (by decide)
  have hb0 : (spinfulIndex N b 0).val = 2 * b.val := by simp [spinfulIndex]
  have hb1 : (spinfulIndex N b 1).val = 2 * b.val + 1 := by simp [spinfulIndex]
  have hfilter : Finset.univ.filter (fun k : Fin (2 * N + 2) => (spinfulIndex N b 0).val ≤ k.val)
      = {spinfulIndex N b 0, spinfulIndex N b 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hb0]
    constructor
    · intro hk
      have hklt := k.isLt
      rcases (by omega : k.val = 2 * b.val ∨ k.val = 2 * b.val + 1) with h | h
      · exact Or.inl (Fin.ext (by rw [hb0]; omega))
      · exact Or.inr (Fin.ext (by rw [hb1]; omega))
    · rintro (rfl | rfl) <;> omega
  rw [hfilter, Finset.sum_insert (by simp [Finset.mem_singleton, hne]), Finset.sum_singleton,
    tJConfigOf_apply_up, if_pos hsb, tJConfigOf_apply_down, if_neg (by rw [hsb]; decide)]
  decide

/-- Modes at-or-above the down-orbital of the last site `b` (`b.val = N`) sum to `1` when `b` is ↓:
the only such mode is the (occupied) down-orbital. -/
private theorem tJ_bwrap_ge_eq_one_down (N : ℕ) (s : Fin (N + 1) → Fin 3) (b : Fin (N + 1))
    (hbN : b.val = N) (hsb : s b = 2) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin (2 * N + 2) => (spinfulIndex N b 1).val ≤ k.val),
      (tJConfigOf N s k).val) = 1 := by
  have hb1 : (spinfulIndex N b 1).val = 2 * b.val + 1 := by simp [spinfulIndex]
  have hfilter : Finset.univ.filter (fun k : Fin (2 * N + 2) => (spinfulIndex N b 1).val ≤ k.val)
      = {spinfulIndex N b 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hb1]
    constructor
    · intro hk; have hklt := k.isLt; exact Fin.ext (by rw [hb1]; omega)
    · rintro rfl; omega
  rw [hfilter, Finset.sum_singleton, tJConfigOf_apply_down, if_pos hsb]
  rfl

/-- **Leftward wrap up-hop is sign-free for odd `Ne`.**  Source `N` ↑, target `0` empty: the electron
hops `N → 0` with no sign for odd `Ne`. -/
theorem tJ_uphop_backward_wrap_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s b = 1) (hsa : s a = 0)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N a 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 0)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s b a)) := by
  have hqp : (spinfulIndex N a 0).val < (spinfulIndex N b 0).val := by
    simp only [spinfulIndex]; omega
  have hne : a ≠ b := fun h => by rw [h] at ha0; omega
  have hpne : spinfulIndex N a 0 ≠ spinfulIndex N b 0 := fun h =>
    hne ((spinfulIndex_eq_iff N a b 0 0).mp h).1
  have hcq : tJConfigOf N s (spinfulIndex N b 0) = 1 := by rw [tJConfigOf_apply_up, if_pos ha]
  have hcpz : tJConfigOf N s (spinfulIndex N a 0) = 0 := by
    rw [tJConfigOf_apply_up, if_neg (by rw [hsa]; decide)]
  have hcp : (Function.update (tJConfigOf N s) (spinfulIndex N b 0) 0) (spinfulIndex N a 0) = 0 := by
    rw [Function.update_of_ne hpne, hcpz]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec, if_pos ⟨hcq, hcp⟩,
    jwSign_mul_jwSign_update_backward (2 * N + 1) (spinfulIndex N b 0) (spinfulIndex N a 0)
      (tJConfigOf N s) hqp hcpz, tJConfigOf_tJSiteHop_up N s b a ha hsa]
  have hbtw : (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
      (tJConfigOf N s k).val) = Ne - 1 := by
    have hsplit := sum_split_le_between_ge (2 * N + 1) (tJConfigOf N s)
      (spinfulIndex N a 0) (spinfulIndex N b 0) hqp
    rw [tJ_bwrap_le_eq_zero N s a 0 ha0 hsa, tJ_bwrap_ge_eq_one_up N s b hbN ha,
      tJConfigOf_total_count, hNe] at hsplit
    set X := (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
      (tJConfigOf N s k).val) with hX
    omega
  rw [hbtw, (Nat.Odd.sub_odd hodd odd_one).neg_one_pow, one_smul]

/-- **Leftward wrap down-hop is sign-free for odd `Ne`.** -/
theorem tJ_downhop_backward_wrap_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s b = 2) (hsa : s a = 0)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N a 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 1)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s b a)) := by
  have hqp : (spinfulIndex N a 1).val < (spinfulIndex N b 1).val := by
    simp only [spinfulIndex]; omega
  have hne : a ≠ b := fun h => by rw [h] at ha0; omega
  have hpne : spinfulIndex N a 1 ≠ spinfulIndex N b 1 := fun h =>
    hne ((spinfulIndex_eq_iff N a b 1 1).mp h).1
  have hcq : tJConfigOf N s (spinfulIndex N b 1) = 1 := by rw [tJConfigOf_apply_down, if_pos ha]
  have hcpz : tJConfigOf N s (spinfulIndex N a 1) = 0 := by
    rw [tJConfigOf_apply_down, if_neg (by rw [hsa]; decide)]
  have hcp : (Function.update (tJConfigOf N s) (spinfulIndex N b 1) 0) (spinfulIndex N a 1) = 0 := by
    rw [Function.update_of_ne hpne, hcpz]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec, if_pos ⟨hcq, hcp⟩,
    jwSign_mul_jwSign_update_backward (2 * N + 1) (spinfulIndex N b 1) (spinfulIndex N a 1)
      (tJConfigOf N s) hqp hcpz, tJConfigOf_tJSiteHop_down N s b a ha hsa]
  have hbtw : (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
      (tJConfigOf N s k).val) = Ne - 1 := by
    have hsplit := sum_split_le_between_ge (2 * N + 1) (tJConfigOf N s)
      (spinfulIndex N a 1) (spinfulIndex N b 1) hqp
    rw [tJ_bwrap_le_eq_zero N s a 1 ha0 hsa, tJ_bwrap_ge_eq_one_down N s b hbN ha,
      tJConfigOf_total_count, hNe] at hsplit
    set X := (∑ k ∈ Finset.univ.filter (fun k =>
      (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
      (tJConfigOf N s k).val) with hX
    omega
  rw [hbtw, (Nat.Odd.sub_odd hodd odd_one).neg_one_pow, one_smul]

/-- **Leftward wrap up-hop matrix element.** -/
theorem tJ_uphop_backward_wrap_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (a b : Fin (N + 1)) (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s b = 1)
    (hsa : s a = 0) (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N a 0) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 0)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s b a then 1 else 0 := by
  rw [tJ_uphop_backward_wrap_mulVec N s a b hpos ha0 hbN ha hsa Ne hNe hodd]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s b a)

/-- **Leftward wrap down-hop matrix element.** -/
theorem tJ_downhop_backward_wrap_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (a b : Fin (N + 1)) (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s b = 2)
    (hsa : s a = 0) (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N a 1) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 1)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s b a then 1 else 0 := by
  rw [tJ_downhop_backward_wrap_mulVec N s a b hpos ha0 hbN ha hsa Ne hNe hodd]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s b a)

end LatticeSystem.Fermion
