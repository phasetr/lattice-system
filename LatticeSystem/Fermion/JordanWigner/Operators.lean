/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.String
import LatticeSystem.Quantum.SpinHalfBasis

/-!
# Multi-mode JW fermion operators

The JW string from `String.lean` lifts to multi-mode creation /
annihilation operators

  `c_i  = jwString N i · σ^+_i`
  `c_i† = jwString N i · σ^-_i`

This file collects:
- multi-mode operator definitions and their commutation with
  on-site operators,
- on-site CAR vanishing `c_i² = 0`, `(c_i†)² = 0`,
- JW string Hermiticity and the multi-mode adjoint,
- the site-occupation number operator `n_i = c_i† · c_i`.

(Refactor Phase 2 PR 11 — second step of the JordanWigner 5-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Multi-mode creation and annihilation operators -/

/-- The multi-mode fermion annihilation operator at site `i`:
`c_i = jwString_i · σ^+_i`. -/
noncomputable def fermionMultiAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  jwString N i * onSite i spinHalfOpPlus

/-- The multi-mode fermion creation operator at site `i`:
`c_i† = jwString_i · σ^-_i`. -/
noncomputable def fermionMultiCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  jwString N i * onSite i spinHalfOpMinus

/-- At site `0` the JW string is the identity, so `c_0 = σ^+_0`. -/
theorem fermionMultiAnnihilation_zero (N : ℕ) :
    fermionMultiAnnihilation N (0 : Fin (N + 1))
      = onSite (0 : Fin (N + 1)) spinHalfOpPlus := by
  unfold fermionMultiAnnihilation
  rw [jwString_zero, Matrix.one_mul]

/-- At site `0` the JW string is the identity, so `c_0† = σ^-_0`. -/
theorem fermionMultiCreation_zero (N : ℕ) :
    fermionMultiCreation N (0 : Fin (N + 1))
      = onSite (0 : Fin (N + 1)) spinHalfOpMinus := by
  unfold fermionMultiCreation
  rw [jwString_zero, Matrix.one_mul]

/-! ## On-site CAR vanishing -/

/-- The Jordan–Wigner string at site `i` commutes with any single-site
operator at site `i`: the string lives on sites strictly less than
`i`, so each factor `σ^z_j` (for `j.val < i.val`, hence `j ≠ i`)
commutes with the site-`i` operator via `onSite_mul_onSite_of_ne`. -/
theorem jwString_commute_onSite (N : ℕ) (i : Fin (N + 1))
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (jwString N i) (onSite i A) := by
  unfold jwString
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro j hj
  rw [Finset.mem_filter] at hj
  exact onSite_mul_onSite_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hj.2).symm) A pauliZ

/-- `c_i² = 0`: cannot annihilate the same fermion mode twice
(Pauli exclusion at a single mode). -/
theorem fermionMultiAnnihilation_sq (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiAnnihilation N i = 0 := by
  unfold fermionMultiAnnihilation
  have hcomm : Commute (onSite i spinHalfOpPlus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpPlus).symm
  rw [show jwString N i * onSite i spinHalfOpPlus *
          (jwString N i * onSite i spinHalfOpPlus)
        = jwString N i * jwString N i *
          (onSite i spinHalfOpPlus * onSite i spinHalfOpPlus) by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpPlus),
          hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
  rw [onSite_mul_onSite_same]
  have h_sq : spinHalfOpPlus * spinHalfOpPlus = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold spinHalfOpPlus
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h_sq]
  have h_zero : onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ)
              = (0 : ManyBodyOp (Fin (N + 1))) := by
    ext σ' σ
    simp [onSite_apply]
  rw [h_zero, Matrix.mul_zero]

/-! ## JW string Hermiticity and adjoint of multi-mode operators -/

/-- The conjugate transpose distributes through `onSite`:
`(onSite i A)ᴴ = onSite i Aᴴ`. Holds entrywise since the `onSite`
matrix element is `A (σ' i) (σ i)` (or `0`), and conjTranspose acts
entrywise as `star`. -/
lemma onSite_conjTranspose {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (i : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i A : ManyBodyOp Λ)ᴴ = onSite i Aᴴ := by
  ext σ' σ
  simp only [Matrix.conjTranspose_apply, onSite_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · have h' : ∀ k, k ≠ i → σ k = σ' k := fun k hki => (h k hki).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ (∀ k, k ≠ i → σ k = σ' k) :=
      fun hp => h (fun k hki => (hp k hki).symm)
    rw [if_neg h, if_neg h', star_zero]

/-- A noncomm-product of pairwise-commuting Hermitian matrices is
Hermitian. Used here for the JW string, which is a product of
mutually commuting Hermitian `σ^z_j` factors. -/
private lemma noncommProd_isHermitian_of_pairwise_commute_of_isHermitian
    {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (hHerm : ∀ a ∈ s, (f a).IsHermitian) :
    (s.noncommProd f hcomm).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.noncommProd_empty]
    exact Matrix.isHermitian_one
  | @insert a t hat ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat]
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hHerm_t : ∀ b ∈ t, (f b).IsHermitian :=
      fun b hb => hHerm b (Finset.mem_insert_of_mem hb)
    refine Matrix.IsHermitian.mul_of_commute
      (hHerm a (Finset.mem_insert_self a t)) (ih hcomm_t hHerm_t) ?_
    apply Finset.noncommProd_commute
    intro b hb
    have hab : a ≠ b := fun h => hat (h ▸ hb)
    exact hcomm (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hb) hab

/-- The Jordan–Wigner string is Hermitian: `(jwString N i)ᴴ = jwString N i`. -/
theorem jwString_isHermitian (N : ℕ) (i : Fin (N + 1)) :
    (jwString N i).IsHermitian := by
  unfold jwString
  apply noncommProd_isHermitian_of_pairwise_commute_of_isHermitian
  intro j _
  exact onSite_isHermitian j pauliZ_isHermitian

/-- `(c_i)ᴴ = c_i†`: the adjoint of the multi-mode annihilation operator
equals the multi-mode creation operator. -/
theorem fermionMultiAnnihilation_conjTranspose (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i)ᴴ = fermionMultiCreation N i := by
  unfold fermionMultiAnnihilation fermionMultiCreation
  rw [Matrix.conjTranspose_mul, (jwString_isHermitian N i).eq,
    onSite_conjTranspose, spinHalfOpPlus_conjTranspose]
  exact (jwString_commute_onSite N i spinHalfOpMinus).eq.symm

/-- `(c_i†)ᴴ = c_i`: the adjoint of the multi-mode creation operator
equals the multi-mode annihilation operator. -/
theorem fermionMultiCreation_conjTranspose (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiCreation N i)ᴴ = fermionMultiAnnihilation N i := by
  unfold fermionMultiAnnihilation fermionMultiCreation
  rw [Matrix.conjTranspose_mul, (jwString_isHermitian N i).eq,
    onSite_conjTranspose, spinHalfOpMinus_conjTranspose]
  exact (jwString_commute_onSite N i spinHalfOpPlus).eq.symm

/-! ## Site-occupation number operator -/

/-- A noncomm-product of pairwise-commuting matrices, each squaring to
the identity, itself squares to the identity. Used here for the JW
string, where each `σ^z_j` satisfies `σ^z² = 1`. -/
private lemma noncommProd_sq_of_pairwise_commute_of_sq_one
    {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (hSq : ∀ a ∈ s, f a * f a = 1) :
    s.noncommProd f hcomm * s.noncommProd f hcomm = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.noncommProd_empty]
    rw [Matrix.one_mul]
  | @insert a t hat ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat]
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hSq_t : ∀ b ∈ t, f b * f b = 1 :=
      fun b hb => hSq b (Finset.mem_insert_of_mem hb)
    have hcomm_a : Commute (f a) (t.noncommProd f hcomm_t) := by
      apply Finset.noncommProd_commute
      intro b hb
      have hab : a ≠ b := fun h => hat (h ▸ hb)
      exact hcomm (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hb) hab
    -- (f a · ∏)·(f a · ∏) = f a · (∏ · f a) · ∏ = f a · (f a · ∏) · ∏ = (f a · f a) · ∏²
    -- = 1 · 1 = 1
    rw [show f a * t.noncommProd f hcomm_t * (f a * t.noncommProd f hcomm_t)
          = (f a * f a) * (t.noncommProd f hcomm_t * t.noncommProd f hcomm_t) by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (t.noncommProd f hcomm_t) (f a),
            ← hcomm_a.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hSq a (Finset.mem_insert_self a t), Matrix.one_mul, ih hcomm_t hSq_t]

/-- `(jwString N i)² = 1`: the JW string squares to the identity, since
each `σ^z` factor satisfies `(σ^z)² = 1`. -/
theorem jwString_sq (N : ℕ) (i : Fin (N + 1)) :
    jwString N i * jwString N i = 1 := by
  unfold jwString
  apply noncommProd_sq_of_pairwise_commute_of_sq_one
  intro j _
  rw [onSite_mul_onSite_same, pauliZ_mul_self, onSite_one]

/-- The multi-mode fermion site-occupation number operator at site `i`:
`n_i = c_i† · c_i`. -/
noncomputable def fermionMultiNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  fermionMultiCreation N i * fermionMultiAnnihilation N i

/-- The multi-mode number operator at site `i` equals
`onSite i (σ^- · σ^+)`: the JW strings cancel via `J² = 1`, leaving
the single-site number operator. -/
theorem fermionMultiNumber_eq_onSite (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i
      = onSite i (spinHalfOpMinus * spinHalfOpPlus) := by
  unfold fermionMultiNumber fermionMultiAnnihilation fermionMultiCreation
  -- (J · σ^-)·(J · σ^+) = J · (σ^- · J) · σ^+ = J · (J · σ^-) · σ^+ = J² · (σ^- · σ^+)
  have hcomm : Commute (jwString N i) (onSite i spinHalfOpMinus) :=
    jwString_commute_onSite N i spinHalfOpMinus
  rw [show jwString N i * onSite i spinHalfOpMinus *
          (jwString N i * onSite i spinHalfOpPlus)
        = jwString N i * jwString N i *
          (onSite i spinHalfOpMinus * onSite i spinHalfOpPlus) by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpMinus),
          ← hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
  rw [jwString_sq, Matrix.one_mul, onSite_mul_onSite_same]

/-- The multi-mode number operator is Hermitian. -/
theorem fermionMultiNumber_isHermitian (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiNumber N i).IsHermitian := by
  rw [fermionMultiNumber_eq_onSite]
  -- σ^- · σ^+ is Hermitian (it equals the diagonal !![0,0;0,1])
  have h_sq : (spinHalfOpMinus * spinHalfOpPlus).IsHermitian := by
    unfold spinHalfOpMinus spinHalfOpPlus
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  exact onSite_isHermitian i h_sq

/-- The multi-mode number operator is idempotent: `n_i² = n_i`
(eigenvalues `0, 1` giving the site occupation count). -/
theorem fermionMultiNumber_sq (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiNumber N i = fermionMultiNumber N i := by
  rw [fermionMultiNumber_eq_onSite, onSite_mul_onSite_same]
  congr 1
  -- (σ^- · σ^+)² = σ^- · σ^+ as 2×2 matrices
  unfold spinHalfOpMinus spinHalfOpPlus
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `(c_i†)² = 0`: cannot create the same fermion mode twice. -/
theorem fermionMultiCreation_sq (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiCreation N i * fermionMultiCreation N i = 0 := by
  unfold fermionMultiCreation
  have hcomm : Commute (onSite i spinHalfOpMinus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpMinus).symm
  rw [show jwString N i * onSite i spinHalfOpMinus *
          (jwString N i * onSite i spinHalfOpMinus)
        = jwString N i * jwString N i *
          (onSite i spinHalfOpMinus * onSite i spinHalfOpMinus) by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpMinus),
          hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
  rw [onSite_mul_onSite_same]
  have h_sq : spinHalfOpMinus * spinHalfOpMinus = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold spinHalfOpMinus
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h_sq]
  have h_zero : onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ)
              = (0 : ManyBodyOp (Fin (N + 1))) := by
    ext σ' σ
    simp [onSite_apply]
  rw [h_zero, Matrix.mul_zero]


end LatticeSystem.Fermion
