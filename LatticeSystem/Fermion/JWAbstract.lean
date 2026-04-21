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

Stage 1 of the JW abstraction plan (see
`.self-local/docs/jw-abstract-plan.md`). Downstream operators
(`fermionAnnihilation`, `fermionCreation`, …) are ported in
subsequent PRs.
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

end LatticeSystem.Fermion
