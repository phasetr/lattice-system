import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundState

/-!
# Tasaki §11.5: the `Ŝ³_tot = ½` sector basis for the t-J model (Prop 11.24 PR2b)

The spin-charge-separated basis for the ferromagnetic t-J model: each site is empty, ↑, or ↓
(hard-core), encoded by a *site-state* function `s : Fin (N+1) → Fin 3` (`0 = empty`, `1 = ↑`,
`2 = ↓`).  The computational basis vector is `basisVec (tJConfigOf s)`, where `tJConfigOf` maps the
site state to the spinful orbital occupation (`spinfulIndex i 0` occupied iff `s i = 1`,
`spinfulIndex i 1` iff `s i = 2`).

This file establishes the *basis skeleton* (codex-validated design): the configuration is always
hard-core (each site occupies at most one orbital), and the total electron number equals the number
of occupied sites.  The `Ŝ³_tot = ½` constraint, injectivity/orthonormality, and the hop matrix
elements (with the wrap-hop fermion sign `(-1)^(Ne-1)`) follow in later steps.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The spinful occupation configuration of a site-state function `s : Fin (N+1) → Fin 3`
(`0 = empty`, `1 = ↑`, `2 = ↓`): the up-orbital of site `i` is occupied iff `s i = 1`, the
down-orbital iff `s i = 2`.  Hard-core by construction. -/
def tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) : Fin (2 * N + 2) → Fin 2 :=
  fun k =>
    let i : Fin (N + 1) :=
      ⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by have := k.isLt; omega)⟩
    if k.val % 2 = 0 then (if s i = 1 then 1 else 0)
    else (if s i = 2 then 1 else 0)

/-- Value of `tJConfigOf` at the up-orbital `2 i` of site `i`: occupied iff `s i = ↑`. -/
theorem tJConfigOf_apply_up (N : ℕ) (s : Fin (N + 1) → Fin 3) (i : Fin (N + 1)) :
    tJConfigOf N s (spinfulIndex N i 0) = if s i = 1 then 1 else 0 := by
  have hsite : (spinfulIndex N i 0).val / 2 = i.val := by simp [spinfulIndex]
  have hmod : (spinfulIndex N i 0).val % 2 = 0 := by simp [spinfulIndex]
  simp only [tJConfigOf, hsite, hmod, if_true]

/-- Value of `tJConfigOf` at the down-orbital `2 i + 1` of site `i`: occupied iff `s i = ↓`. -/
theorem tJConfigOf_apply_down (N : ℕ) (s : Fin (N + 1) → Fin 3) (i : Fin (N + 1)) :
    tJConfigOf N s (spinfulIndex N i 1) = if s i = 2 then 1 else 0 := by
  have hval : (spinfulIndex N i 1).val = 2 * i.val + 1 := by simp [spinfulIndex]
  have hsite : (spinfulIndex N i 1).val / 2 = i.val := by
    rw [hval, Nat.mul_add_div (by norm_num)]; norm_num
  have hmod : (spinfulIndex N i 1).val % 2 = 1 := by rw [hval, Nat.mul_add_mod]
  simp only [tJConfigOf, hsite, hmod, if_neg (by norm_num : ¬ (1 = 0))]

/-- The double-occupancy operator vanishes on `basisVec c` when the up-orbital is empty (duplicated
private helper from `HardcoreBasis.lean`). -/
private theorem tJ_doubleOcc_vanish_up (N : ℕ) (i : Fin (N + 1)) (c : Fin (2 * N + 2) → Fin 2)
    (h : c (spinfulIndex N i 0) = 0) : (hubbardDoubleOccupancy N i).mulVec (basisVec c) = 0 := by
  unfold hubbardDoubleOccupancy
  rw [(fermionUpNumber_commute_fermionDownNumber N i).eq, ← Matrix.mulVec_mulVec]
  unfold fermionUpNumber
  rw [fermionMultiNumber_mulVec_basisVec, h]
  simp

/-- The double-occupancy operator vanishes on `basisVec c` when the down-orbital is empty. -/
private theorem tJ_doubleOcc_vanish_down (N : ℕ) (i : Fin (N + 1)) (c : Fin (2 * N + 2) → Fin 2)
    (h : c (spinfulIndex N i 1) = 0) : (hubbardDoubleOccupancy N i).mulVec (basisVec c) = 0 := by
  unfold hubbardDoubleOccupancy fermionDownNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiNumber_mulVec_basisVec, h]
  simp

/-- **Every `tJConfigOf` basis state is hard-core**: at each site at least one orbital is empty
(since `s i ∈ {0,1,2}` occupies at most one), so the double-occupancy operator vanishes. -/
theorem tJConfigOf_mem_hardcore (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    basisVec (tJConfigOf N s) ∈ hubbardHardcoreSubspace N := by
  rw [mem_hubbardHardcoreSubspace_iff]
  intro i
  by_cases h : s i = 2
  · refine tJ_doubleOcc_vanish_up N i _ ?_
    rw [tJConfigOf_apply_up, if_neg (by rw [h]; decide)]
  · refine tJ_doubleOcc_vanish_down N i _ ?_
    rw [tJConfigOf_apply_down, if_neg h]

/-- `tJConfigOf` is injective: the spinful occupation determines the site state (the up-orbital
recovers "`s i = ↑`", the down-orbital recovers "`s i = ↓`"). -/
theorem tJConfigOf_injective (N : ℕ) : Function.Injective (tJConfigOf N) := by
  intro s s' h
  funext i
  have hup := congrFun h (spinfulIndex N i 0)
  have hdn := congrFun h (spinfulIndex N i 1)
  rw [tJConfigOf_apply_up, tJConfigOf_apply_up] at hup
  rw [tJConfigOf_apply_down, tJConfigOf_apply_down] at hdn
  have h1 : (s i = 1) ↔ (s' i = 1) := by
    constructor
    · intro hs; by_contra hs'; rw [if_pos hs, if_neg hs'] at hup; exact absurd hup (by decide)
    · intro hs; by_contra hs'; rw [if_neg hs', if_pos hs] at hup; exact absurd hup (by decide)
  have h2 : (s i = 2) ↔ (s' i = 2) := by
    constructor
    · intro hs; by_contra hs'; rw [if_pos hs, if_neg hs'] at hdn; exact absurd hdn (by decide)
    · intro hs; by_contra hs'; rw [if_neg hs', if_pos hs] at hdn; exact absurd hdn (by decide)
  have key : ∀ a b : Fin 3, (a = 1 ↔ b = 1) → (a = 2 ↔ b = 2) → a = b := by decide
  exact key (s i) (s' i) h1 h2

/-- The `tJConfigOf` basis states are orthonormal: `⟨Φ_s | Φ_s'⟩ = δ_{s,s'}` (computational basis
vectors at injective configurations). -/
theorem tJConfigOf_basisVec_inner (N : ℕ) (s s' : Fin (N + 1) → Fin 3) :
    (∑ τ : Fin (2 * N + 2) → Fin 2, basisVec (tJConfigOf N s) τ * basisVec (tJConfigOf N s') τ)
      = if s = s' then 1 else 0 := by
  rw [basisVec_inner]
  by_cases h : s = s'
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hc => h ((tJConfigOf_injective N hc).symm))]

end LatticeSystem.Fermion
