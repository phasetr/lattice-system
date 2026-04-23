/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner

/-!
# Abstract Jordan–Wigner string

The Jordan–Wigner construction needs a total order on the vertex
set (to fix the ordering of the string factors). This module
defines the JW string for any `[Fintype Λ] [LinearOrder Λ]
[DecidableEq Λ]`, generalising the `Fin (N+1)`-specific version in
`LatticeSystem.Fermion.JordanWigner`.

Stage 1 of the JW abstraction (initial Phase 2 work). Downstream
operators (`fermionAnnihilation`, `fermionCreation`, …) are ported
in subsequent PRs.
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-- Abstract Jordan-Wigner string at site `i`: the product of
`σ^z_j` over all sites `j` strictly below `i` in the linear order. -/
noncomputable def jwStringAbstract (i : Λ) : ManyBodyOp Λ :=
  ((Finset.univ : Finset Λ).filter (fun j => j < i)).noncommProd
    (fun j => onSite j pauliZ)
    (fun _ _ _ _ hab => onSite_mul_onSite_of_ne hab pauliZ pauliZ)

/-- A noncomm-product of pairwise-commuting Hermitian matrices is
Hermitian. Public version of the private helper in
`JordanWigner.lean`. -/
theorem noncommProd_isHermitian
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

/-- A noncomm-product of pairwise-commuting matrices, each
squaring to the identity, itself squares to the identity. -/
theorem noncommProd_sq_of_sq_one
    {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (hSq : ∀ a ∈ s, f a * f a = 1) :
    s.noncommProd f hcomm * s.noncommProd f hcomm = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; rw [Matrix.one_mul]
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
    rw [show f a * t.noncommProd f hcomm_t * (f a * t.noncommProd f hcomm_t)
          = (f a * f a) * (t.noncommProd f hcomm_t * t.noncommProd f hcomm_t) by
        rw [Matrix.mul_assoc,
          ← Matrix.mul_assoc (t.noncommProd f hcomm_t) (f a),
          ← hcomm_a.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hSq a (Finset.mem_insert_self a t), Matrix.one_mul,
      ih hcomm_t hSq_t]

/-- The abstract JW string is Hermitian. -/
theorem jwStringAbstract_isHermitian (i : Λ) :
    (jwStringAbstract i).IsHermitian := by
  unfold jwStringAbstract
  apply noncommProd_isHermitian
  intro j _
  exact onSite_isHermitian j pauliZ_isHermitian

/-- The abstract JW string squares to the identity. -/
theorem jwStringAbstract_sq (i : Λ) :
    jwStringAbstract i * jwStringAbstract i = 1 := by
  unfold jwStringAbstract
  apply noncommProd_sq_of_sq_one
  intro j _
  rw [onSite_mul_onSite_same, pauliZ_mul_self, onSite_one]

/-- The abstract JW string on `Λ = Fin (N+1)` coincides with the
existing `Fin (N+1)`-specific `jwString N i` definitionally: the
`LinearOrder (Fin (N+1))` instance's `<` matches `j.val < i.val`. -/
theorem jwStringAbstract_eq_jwString (N : ℕ) (i : Fin (N + 1)) :
    jwStringAbstract i = jwString N i :=
  rfl

/-! ## Abstract fermion creation / annihilation / number operators -/

open LatticeSystem.Quantum in
/-- Abstract fermion annihilation at site `i`: JW string times
single-site raising operator `σ^+`. -/
noncomputable def fermionAnnihilationAbstract (i : Λ) : ManyBodyOp Λ :=
  jwStringAbstract i * onSite i spinHalfOpPlus

open LatticeSystem.Quantum in
/-- Abstract fermion creation at site `i`: JW string times
single-site lowering operator `σ^-`. -/
noncomputable def fermionCreationAbstract (i : Λ) : ManyBodyOp Λ :=
  jwStringAbstract i * onSite i spinHalfOpMinus

open LatticeSystem.Quantum in
/-- Abstract fermion site-occupation number `n_i = c_i† · c_i`. -/
noncomputable def fermionNumberAbstract (i : Λ) : ManyBodyOp Λ :=
  fermionCreationAbstract i * fermionAnnihilationAbstract i

/-- Bridge: abstract annihilation on `Fin (N+1)` equals the
existing `fermionMultiAnnihilation`. -/
theorem fermionAnnihilationAbstract_eq_fermionMultiAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionAnnihilationAbstract i = fermionMultiAnnihilation N i :=
  rfl

/-- Bridge: abstract creation on `Fin (N+1)` equals the existing
`fermionMultiCreation`. -/
theorem fermionCreationAbstract_eq_fermionMultiCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionCreationAbstract i = fermionMultiCreation N i :=
  rfl

/-- Bridge for the number operator. -/
theorem fermionNumberAbstract_eq_fermionMultiNumber
    (N : ℕ) (i : Fin (N + 1)) :
    fermionNumberAbstract i = fermionMultiNumber N i :=
  rfl

/-- The JW string at site `i` commutes with any single-site
operator at the same site `i`: the string only touches sites
`j < i`, which are all distinct from `i`. -/
theorem jwStringAbstract_commute_onSite (i : Λ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (jwStringAbstract i) (onSite i A) := by
  unfold jwStringAbstract
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro j hj
  have hji : j ≠ i := by
    intro heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [heq] at hj
    exact lt_irrefl i hj
  exact onSite_mul_onSite_of_ne hji.symm A pauliZ

/-- `(onSite i A)ᴴ = onSite i Aᴴ` (public copy of the `private`
helper in `JordanWigner.lean`). -/
theorem onSite_conjTransposeAbstract
    {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ']
    (i : Λ') (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i A : ManyBodyOp Λ')ᴴ = onSite i Aᴴ := by
  ext σ σ'
  simp only [onSite_apply, Matrix.conjTranspose_apply]
  by_cases h : ∀ k, k ≠ i → σ k = σ' k
  · have h' : ∀ k, k ≠ i → σ' k = σ k := fun k hki => (h k hki).symm
    rw [if_pos h', if_pos h]
  · have h' : ¬ (∀ k, k ≠ i → σ' k = σ k) :=
      fun hp => h (fun k hki => (hp k hki).symm)
    rw [if_neg h, if_neg h', star_zero]

/-- `(c_i)ᴴ = c_i†`. -/
theorem fermionAnnihilationAbstract_conjTranspose (i : Λ) :
    (fermionAnnihilationAbstract i)ᴴ = fermionCreationAbstract i := by
  unfold fermionAnnihilationAbstract fermionCreationAbstract
  rw [Matrix.conjTranspose_mul, onSite_conjTransposeAbstract,
    spinHalfOpPlus_conjTranspose, (jwStringAbstract_isHermitian i).eq,
    (jwStringAbstract_commute_onSite i spinHalfOpMinus).eq]

/-- `(c_i†)ᴴ = c_i`. -/
theorem fermionCreationAbstract_conjTranspose (i : Λ) :
    (fermionCreationAbstract i)ᴴ = fermionAnnihilationAbstract i := by
  unfold fermionAnnihilationAbstract fermionCreationAbstract
  rw [Matrix.conjTranspose_mul, onSite_conjTransposeAbstract,
    spinHalfOpMinus_conjTranspose, (jwStringAbstract_isHermitian i).eq,
    (jwStringAbstract_commute_onSite i spinHalfOpPlus).eq]

/-- `n_i` is Hermitian. -/
theorem fermionNumberAbstract_isHermitian (i : Λ) :
    (fermionNumberAbstract i).IsHermitian := by
  unfold fermionNumberAbstract Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, fermionAnnihilationAbstract_conjTranspose,
    fermionCreationAbstract_conjTranspose]

/-- General helper: if `X² = 1` and `X, Y` commute, then
`(X·Y)² = Y²`. -/
private lemma commute_sq_lemma {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) (hX_sq : X * X = 1) (hcomm : Commute X Y) :
    X * Y * (X * Y) = Y * Y := by
  have : X * Y * (X * Y) = X * X * (Y * Y) := by
    show X * Y * (X * Y) = X * X * (Y * Y)
    rw [show X * Y * (X * Y) = X * (Y * X) * Y by noncomm_ring,
        ← hcomm.eq]
    noncomm_ring
  rw [this, hX_sq, Matrix.one_mul]

/-- `c_i² = 0` (fermion exclusion). -/
theorem fermionAnnihilationAbstract_sq (i : Λ) :
    fermionAnnihilationAbstract i * fermionAnnihilationAbstract i = 0 := by
  unfold fermionAnnihilationAbstract
  rw [commute_sq_lemma _ _ (jwStringAbstract_sq i)
    (jwStringAbstract_commute_onSite i spinHalfOpPlus)]
  rw [onSite_mul_onSite_same, spinHalfOpPlus_mul_self, onSite_zero]

/-- `c_i†² = 0`. -/
theorem fermionCreationAbstract_sq (i : Λ) :
    fermionCreationAbstract i * fermionCreationAbstract i = 0 := by
  unfold fermionCreationAbstract
  rw [commute_sq_lemma _ _ (jwStringAbstract_sq i)
    (jwStringAbstract_commute_onSite i spinHalfOpMinus)]
  have h : spinHalfOpMinus * spinHalfOpMinus =
      (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [spinHalfOpMinus, Matrix.mul_apply, Fin.sum_univ_two]
  rw [onSite_mul_onSite_same, h, onSite_zero]

/-- General helper: if `X² = 1` and `X, Y_i` commute (for
i=1,2), then `(X·Y_1)·(X·Y_2) = Y_1·Y_2`. -/
private lemma commute_sq_lemma_two {n : Type*} [Fintype n] [DecidableEq n]
    (X Y1 Y2 : Matrix n n ℂ) (hX_sq : X * X = 1)
    (hcomm1 : Commute X Y1) :
    X * Y1 * (X * Y2) = Y1 * Y2 := by
  have : X * Y1 * (X * Y2) = X * X * (Y1 * Y2) := by
    rw [show X * Y1 * (X * Y2) = X * (Y1 * X) * Y2 by noncomm_ring,
      ← hcomm1.eq]
    noncomm_ring
  rw [this, hX_sq, Matrix.one_mul]

/-- Same-site mixed anticommutator: `{c_i, c_i†} = c_i · c_i† +
c_i† · c_i = 1`. -/
theorem fermionMultiAnticommAbstract_self (i : Λ) :
    fermionAnnihilationAbstract i * fermionCreationAbstract i
        + fermionCreationAbstract i * fermionAnnihilationAbstract i = 1 := by
  unfold fermionAnnihilationAbstract fermionCreationAbstract
  rw [commute_sq_lemma_two _ _ _ (jwStringAbstract_sq i)
    (jwStringAbstract_commute_onSite i spinHalfOpPlus)]
  rw [commute_sq_lemma_two _ _ _ (jwStringAbstract_sq i)
    (jwStringAbstract_commute_onSite i spinHalfOpMinus)]
  rw [onSite_mul_onSite_same, onSite_mul_onSite_same, ← onSite_add]
  have h_sum : spinHalfOpPlus * spinHalfOpMinus +
      spinHalfOpMinus * spinHalfOpPlus
    = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [spinHalfOpPlus, spinHalfOpMinus]
  rw [h_sum, onSite_one]

/-- `n_i² = n_i` (idempotent). -/
theorem fermionNumberAbstract_sq (i : Λ) :
    fermionNumberAbstract i * fermionNumberAbstract i
      = fermionNumberAbstract i := by
  unfold fermionNumberAbstract
  have anticomm := fermionMultiAnticommAbstract_self i
  have cd_eq : fermionAnnihilationAbstract i * fermionCreationAbstract i
      = 1 - fermionCreationAbstract i * fermionAnnihilationAbstract i :=
    eq_sub_of_add_eq anticomm
  calc fermionCreationAbstract i * fermionAnnihilationAbstract i *
        (fermionCreationAbstract i * fermionAnnihilationAbstract i)
      = fermionCreationAbstract i *
          (fermionAnnihilationAbstract i * fermionCreationAbstract i) *
          fermionAnnihilationAbstract i := by noncomm_ring
    _ = fermionCreationAbstract i *
          (1 - fermionCreationAbstract i * fermionAnnihilationAbstract i) *
          fermionAnnihilationAbstract i := by rw [cd_eq]
    _ = fermionCreationAbstract i * fermionAnnihilationAbstract i
          - fermionCreationAbstract i * fermionCreationAbstract i
          * (fermionAnnihilationAbstract i * fermionAnnihilationAbstract i) := by
        noncomm_ring
    _ = fermionCreationAbstract i * fermionAnnihilationAbstract i := by
        rw [fermionCreationAbstract_sq, Matrix.zero_mul, sub_zero]

end LatticeSystem.Fermion
