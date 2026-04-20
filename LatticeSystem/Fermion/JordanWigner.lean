/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Fermion.Mode

/-!
# Multi-mode fermion via Jordan–Wigner mapping

This module lifts the single-mode CAR algebra (see
`LatticeSystem/Fermion/Mode.lean`) to a multi-mode fermion system on
the linearly-ordered lattice `Λ = Fin (N + 1)` via the Jordan–Wigner
mapping.

## Conventions

The Hilbert space is the spin-1/2 many-body space
`ManyBodyOp (Fin (N + 1)) = Matrix (Fin (N + 1) → Fin 2) (...) ℂ`,
with the convention from `Fermion/Mode.lean`:
`|0⟩` (vacuum) on each site corresponds to spin-up,
`|1⟩` (occupied) to spin-down.

## Definitions

The Jordan–Wigner string at site `i` is

```
jwString N i = ∏_{j : Fin (N+1), j.val < i.val} σ^z_j
```

and the multi-mode fermion operators are

```
c_i  = jwString N i · σ^+_i
c_i† = jwString N i · σ^-_i
```

The string makes the otherwise-bosonic spin raising / lowering
operators anticommute across distinct sites, giving the correct
fermion statistics.

## Results

* `jwString_zero` — `jwString N 0 = 1` (empty product at the leftmost
  site).
* `fermionMultiAnnihilation_zero`, `fermionMultiCreation_zero` —
  `c_0 = σ^+_0`, `c_0† = σ^-_0` (no JW string at the leftmost site).
* `jwString_commute_onSite` — `[jwString N i, onSite i A] = 0` for
  any `A`.
* `fermionMultiAnnihilation_sq` — `c_i² = 0` (Pauli exclusion).
* `fermionMultiCreation_sq` — `(c_i†)² = 0`.

The cross-site anticommutation relations
`{c_i, c_j†} = δ_ij` and `{c_i, c_j} = 0` for `i ≠ j` are deferred
to follow-up PRs (they require sign-cancellation tracking through
the JW string acting on intermediate sites).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Jordan–Wigner string -/

/-- The Jordan–Wigner string at site `i` on a chain of `N + 1` sites:
the product `∏_{j.val < i.val} σ^z_j` of `σ^z` operators on all
sites strictly to the left of `i`.

Uses `Finset.noncommProd` because `ManyBodyOp` is a non-commutative
ring. The pairwise-commutativity certificate comes from
`onSite_mul_onSite_of_ne` (different-site `σ^z` operators commute). -/
noncomputable def jwString (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  ((Finset.univ.filter fun j : Fin (N + 1) => j.val < i.val)).noncommProd
    (fun j => onSite j pauliZ)
    (fun _ _ _ _ hab => onSite_mul_onSite_of_ne hab pauliZ pauliZ)

/-- The Jordan–Wigner string at site `0` is the identity (empty
product, since no `j` satisfies `j.val < 0`). -/
theorem jwString_zero (N : ℕ) :
    jwString N (0 : Fin (N + 1)) = 1 := by
  unfold jwString
  simp

/-- Recursive factorisation of the JW string: adding a new site `i`
at the right extends the product by one `σ^z_i` factor.
`jwString N ⟨i.val + 1, _⟩ = jwString N i * onSite i pauliZ`. -/
theorem jwString_succ_eq (N : ℕ) (i : Fin (N + 1)) (hi : i.val + 1 < N + 1) :
    jwString N ⟨i.val + 1, hi⟩ = jwString N i * onSite i pauliZ := by
  unfold jwString
  have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
      (fun j => j.val < (⟨i.val + 1, hi⟩ : Fin (N + 1)).val) =
      insert i ((Finset.univ : Finset (Fin (N + 1))).filter
        (fun j => j.val < i.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      show k = i ∨ k.val < i.val
      by_cases heq : k.val = i.val
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (by omega)
    · intro h
      rcases h with h | h
      · rw [h]; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  have hi_notmem : i ∉ (Finset.univ : Finset (Fin (N + 1))).filter
      (fun j => j.val < i.val) := by
    simp
  rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
  rw [Finset.noncommProd_insert_of_notMem' _ _ _ _ hi_notmem]

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
private lemma onSite_conjTranspose {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
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

/-! ## Number operator: commutativity and total -/

/-- Site-occupation number operators commute for any sites
`i, j : Fin (N + 1)`: they are simultaneously diagonal in the
occupation-number basis. -/
theorem fermionMultiNumber_commute (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (fermionMultiNumber N j) := by
  rw [fermionMultiNumber_eq_onSite, fermionMultiNumber_eq_onSite]
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · exact onSite_mul_onSite_of_ne hij _ _

/-- The total particle-number operator on `Fin (N + 1)`:
`N̂ := Σ_i n_i`. -/
noncomputable def fermionTotalNumber (N : ℕ) : ManyBodyOp (Fin (N + 1)) :=
  ∑ i : Fin (N + 1), fermionMultiNumber N i

/-- The total particle-number operator is Hermitian (sum of
Hermitian summands). -/
theorem fermionTotalNumber_isHermitian (N : ℕ) :
    (fermionTotalNumber N).IsHermitian := by
  unfold fermionTotalNumber
  classical
  induction (Finset.univ : Finset (Fin (N + 1))) using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
    rw [Finset.sum_insert hat]
    exact (fermionMultiNumber_isHermitian N a).add ih

/-! ## Same-site canonical anticommutation -/

/-- The single-site identity `σ^+ · σ^- + σ^- · σ^+ = I`. This is the
spin-1/2 raising/lowering anticommutator, equal to the identity. -/
private lemma spinHalfOpPlus_anticomm_spinHalfOpMinus :
    spinHalfOpPlus * spinHalfOpMinus + spinHalfOpMinus * spinHalfOpPlus
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold spinHalfOpPlus spinHalfOpMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The same-site canonical anticommutation relation:
`c_i · c_i† + c_i† · c_i = 1`. Combined with `c_i² = 0` and
`(c_i†)² = 0`, this constitutes the full single-site CAR algebra in
the multi-mode setting. -/
theorem fermionMultiAnticomm_self (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiCreation N i
      + fermionMultiCreation N i * fermionMultiAnnihilation N i = 1 := by
  unfold fermionMultiAnnihilation fermionMultiCreation
  have hcomm_plus : Commute (onSite i spinHalfOpPlus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpPlus).symm
  have hcomm_minus : Commute (onSite i spinHalfOpMinus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpMinus).symm
  have h1 : jwString N i * onSite i spinHalfOpPlus *
              (jwString N i * onSite i spinHalfOpMinus)
          = jwString N i * jwString N i *
              (onSite i spinHalfOpPlus * onSite i spinHalfOpMinus) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpPlus),
        hcomm_plus.eq, Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : jwString N i * onSite i spinHalfOpMinus *
              (jwString N i * onSite i spinHalfOpPlus)
          = jwString N i * jwString N i *
              (onSite i spinHalfOpMinus * onSite i spinHalfOpPlus) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpMinus),
        hcomm_minus.eq, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h1, h2, jwString_sq, Matrix.one_mul, Matrix.one_mul,
    onSite_mul_onSite_same, onSite_mul_onSite_same, ← onSite_add,
    spinHalfOpPlus_anticomm_spinHalfOpMinus, onSite_one]

/-! ## Cross-site CAR on `Fin 2` (simplest nontrivial JW case)

For the 2-site lattice `Fin 2`, the Jordan-Wigner string at site 1 is
exactly `σ^z_0` (the single factor), so
`c_0 = σ^+_0` and `c_1 = σ^z_0 · σ^+_1`. Combining the Pauli identities
`σ^+ σ^z = -σ^+` and `σ^z σ^+ = σ^+` with the `onSite` algebra,
`{c_0, c_1} = 0`. -/

/-- Cross-site CAR on `Fin 2`: `c_0 · c_1 + c_1 · c_0 = 0`. The
simplest nontrivial Jordan-Wigner cross-site anticommutator. -/
theorem fermionMultiAnnihilation_anticomm_two_site_cross :
    fermionMultiAnnihilation 1 (0 : Fin 2) *
        fermionMultiAnnihilation 1 1 +
      fermionMultiAnnihilation 1 1 *
        fermionMultiAnnihilation 1 0 = 0 := by
  -- c_0 = σ^+_0 via jwString_zero.
  rw [fermionMultiAnnihilation_zero]
  -- c_1 = jwString 1 1 * σ^+_1. The JW string has one factor (site 0).
  have hjw : jwString 1 (1 : Fin 2) = onSite (0 : Fin 2) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin 2)).filter
        (fun j : Fin 2 => j.val < (1 : Fin 2).val) = ({0} : Finset (Fin 2)) := by
      ext k; fin_cases k <;> simp
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  show onSite (0 : Fin 2) spinHalfOpPlus *
        fermionMultiAnnihilation 1 1 +
      fermionMultiAnnihilation 1 1 *
        onSite (0 : Fin 2) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw]
  -- Goal: σ^+_0 · (σ^z_0 · σ^+_1) + (σ^z_0 · σ^+_1) · σ^+_0 = 0
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- Compute c_0 · c_1 = σ^+_0 · σ^z_0 · σ^+_1 = (σ^+ σ^z)_0 · σ^+_1 = -σ^+_0 · σ^+_1
  have hfirst : onSite (0 : Fin 2) spinHalfOpPlus *
      (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpPlus) =
        -(onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpPlus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    -- Goal: onSite 0 (-σ^+) * onSite 1 σ^+ = -(onSite 0 σ^+ * onSite 1 σ^+)
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- Compute c_1 · c_0 = σ^z_0 · σ^+_1 · σ^+_0 = σ^z_0 · σ^+_0 · σ^+_1 = σ^+_0 · σ^+_1
  have hsecond : (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpPlus) *
      onSite (0 : Fin 2) spinHalfOpPlus =
        onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpPlus := by
    -- Swap σ^+_1 past σ^+_0 (disjoint sites 0 and 1), then combine σ^z σ^+ = σ^+
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Cross-site CAR for the creation operators on `Fin 2`:
`c_0† · c_1† + c_1† · c_0† = 0`. Direct consequence of the
annihilation-operator version
(`fermionMultiAnnihilation_anticomm_two_site_cross`) by taking the
matrix `conjTranspose`. -/
theorem fermionMultiCreation_anticomm_two_site_cross :
    fermionMultiCreation 1 (0 : Fin 2) *
        fermionMultiCreation 1 1 +
      fermionMultiCreation 1 1 *
        fermionMultiCreation 1 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_two_site_cross
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  -- h2 : c_1† · c_0† + c_0† · c_1† = 0, goal: c_0† · c_1† + c_1† · c_0† = 0
  rw [show fermionMultiCreation 1 (0 : Fin 2) * fermionMultiCreation 1 1 +
        fermionMultiCreation 1 1 * fermionMultiCreation 1 (0 : Fin 2) =
      fermionMultiCreation 1 1 * fermionMultiCreation 1 (0 : Fin 2) +
        fermionMultiCreation 1 (0 : Fin 2) * fermionMultiCreation 1 1 from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR on `Fin 2`: `c_0 · c_1† + c_1† · c_0 = 0`.
Same proof structure as PR #108 with `σ^+_1` replaced by `σ^-_1` at
site 1 (the site-0 Pauli identities are unchanged). -/
theorem fermionMultiAnnihilation_creation_anticomm_two_site_cross :
    fermionMultiAnnihilation 1 (0 : Fin 2) *
        fermionMultiCreation 1 1 +
      fermionMultiCreation 1 1 *
        fermionMultiAnnihilation 1 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw : jwString 1 (1 : Fin 2) = onSite (0 : Fin 2) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin 2)).filter
        (fun j : Fin 2 => j.val < (1 : Fin 2).val) = ({0} : Finset (Fin 2)) := by
      ext k; fin_cases k <;> simp
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  show onSite (0 : Fin 2) spinHalfOpPlus *
        fermionMultiCreation 1 1 +
      fermionMultiCreation 1 1 *
        onSite (0 : Fin 2) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- c_0 · c_1† = σ^+_0 · σ^z_0 · σ^-_1 = -σ^+_0 · σ^-_1
  have hfirst : onSite (0 : Fin 2) spinHalfOpPlus *
      (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpMinus) =
        -(onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpMinus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- c_1† · c_0 = σ^z_0 · σ^-_1 · σ^+_0 = σ^z_0 · σ^+_0 · σ^-_1 = σ^+_0 · σ^-_1
  have hsecond : (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpMinus) *
      onSite (0 : Fin 2) spinHalfOpPlus =
        onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpMinus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Cross-site CAR for any chain length `N ≥ 1`:
`c_0 · c_1 + c_1 · c_0 = 0` on `Fin (N+1)`. Generalises the `Fin 2`
case to arbitrary `N`, since the JW string at site 1 only depends on
the filter `{j : j.val < 1} = {0}`, independent of `N`. -/
theorem fermionMultiAnnihilation_anticomm_zero_one
    (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
        (fun j : Fin (N + 1) => j.val < (⟨1, by omega⟩ : Fin (N + 1)).val) =
        ({(0 : Fin (N + 1))} : Finset (Fin (N + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · apply Fin.ext
        have : (k.val : ℕ) < 1 := h
        have : (k.val : ℕ) = 0 := by omega
        rw [this]; rfl
      · rw [h]; show (0 : ℕ) < 1; omega
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  show onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    have := Fin.val_eq_of_eq h
    simp at this
  -- c_0 · c_1 = σ^+_0 · σ^z_0 · σ^+_1 = -σ^+_0 · σ^+_1
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- c_1 · c_0 = σ^z_0 · σ^+_1 · σ^+_0 = σ^z_0 · σ^+_0 · σ^+_1 = σ^+_0 · σ^+_1
  have hsecond : (onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Dual cross-site CAR for creation operators on `Fin (N+1)`, `N ≥ 1`:
`c_0† · c_1† + c_1† · c_0† = 0`. Obtained from PR #112 by taking
`conjTranspose`. -/
theorem fermionMultiCreation_anticomm_zero_one (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_one N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR on `Fin (N+1)`, `N ≥ 1`:
`c_0 · c_1† + c_1† · c_0 = 0`. Same template as PR #112 with
`σ^+_1` replaced by `σ^-_1` at site 1. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_one
    (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
        (fun j : Fin (N + 1) => j.val < (⟨1, by omega⟩ : Fin (N + 1)).val) =
        ({(0 : Fin (N + 1))} : Finset (Fin (N + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · apply Fin.ext
        have : (k.val : ℕ) < 1 := h
        have : (k.val : ℕ) = 0 := by omega
        rw [this]; rfl
      · rw [h]; show (0 : ℕ) < 1; omega
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  show onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    have := Fin.val_eq_of_eq h
    simp at this
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : (onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Mixed cross-site CAR on `Fin (N+1)`, `N ≥ 1`:
`c_0† · c_1 + c_1 · c_0† = 0`. Obtained by `conjTranspose` of the
previous. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_one
    (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_one N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩
    from add_comm _ _]
  exact h2

/-- Cross-site CAR `{c_0, c_2} = 0` on `Fin 3`. First 3-site case,
using `jwString_succ_eq` to factor
`jwString 2 2 = onSite 0 pauliZ * onSite 1 pauliZ`. -/
theorem fermionMultiAnnihilation_anticomm_zero_two_fin_three :
    fermionMultiAnnihilation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        fermionMultiAnnihilation 2 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  -- jwString 2 2 via succ_eq: jwString 2 (1+1) = jwString 2 1 * onSite 1 pauliZ
  have hjw1 : jwString 2 (1 : Fin 3) = onSite (0 : Fin 3) pauliZ := by
    have := jwString_succ_eq 2 (0 : Fin 3) (by decide)
    simpa [jwString_zero] using this
  have hjw2 : jwString 2 (2 : Fin 3) =
      onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ := by
    have h := jwString_succ_eq 2 (1 : Fin 3) (by decide)
    -- h : jwString 2 ⟨2, _⟩ = jwString 2 1 * onSite 1 pauliZ
    rw [hjw1] at h
    -- h : jwString 2 ⟨2, _⟩ = onSite 0 pauliZ * onSite 1 pauliZ
    convert h using 2
  show onSite (0 : Fin 3) spinHalfOpPlus *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        onSite (0 : Fin 3) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw2]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  -- c_0 · c_2 = σ^+_0 · (σ^z_0 · σ^z_1) · σ^+_2
  --           = (σ^+_0 · σ^z_0) · σ^z_1 · σ^+_2 = -σ^+_0 · σ^z_1 · σ^+_2.
  have hfirst : onSite (0 : Fin 3) spinHalfOpPlus *
      (onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
        onSite (2 : Fin 3) spinHalfOpPlus) =
        -(onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus)) := by
    rw [show onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpPlus =
        onSite (0 : Fin 3) pauliZ *
            (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin 3) spinHalfOpPlus), onSite_mul_onSite_same,
      spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- c_2 · c_0 = (σ^z_0 · σ^z_1 · σ^+_2) · σ^+_0 = σ^+_0 · σ^z_1 · σ^+_2.
  have hsecond : onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
      onSite (2 : Fin 3) spinHalfOpPlus *
      onSite (0 : Fin 3) spinHalfOpPlus =
        onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
    have step1 : onSite (2 : Fin 3) spinHalfOpPlus *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (2 : Fin 3) spinHalfOpPlus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpPlus spinHalfOpPlus
    have step2 : onSite (1 : Fin 3) pauliZ *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (1 : Fin 3) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          onSite (2 : Fin 3) spinHalfOpPlus *
          onSite (0 : Fin 3) spinHalfOpPlus
        = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (2 : Fin 3) spinHalfOpPlus *
            onSite (0 : Fin 3) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpPlus) := by rw [step1]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ *
            (onSite (0 : Fin 3) spinHalfOpPlus *
              onSite (2 : Fin 3) spinHalfOpPlus)) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpPlus) := by rw [step2]
      _ = onSite (0 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) (pauliZ * spinHalfOpPlus) *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
          rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
          rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Mixed cross-site CAR `{c_0, c_2†} = 0` on `Fin 3`. Same template
as PR #116 with `σ^+_2` replaced by `σ^-_2`. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_two_fin_three :
    fermionMultiAnnihilation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        fermionMultiAnnihilation 2 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw1 : jwString 2 (1 : Fin 3) = onSite (0 : Fin 3) pauliZ := by
    have := jwString_succ_eq 2 (0 : Fin 3) (by decide)
    simpa [jwString_zero] using this
  have hjw2 : jwString 2 (2 : Fin 3) =
      onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ := by
    have h := jwString_succ_eq 2 (1 : Fin 3) (by decide)
    rw [hjw1] at h
    convert h using 2
  show onSite (0 : Fin 3) spinHalfOpPlus *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        onSite (0 : Fin 3) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw2]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hfirst : onSite (0 : Fin 3) spinHalfOpPlus *
      (onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
        onSite (2 : Fin 3) spinHalfOpMinus) =
        -(onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus)) := by
    rw [show onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpMinus =
        onSite (0 : Fin 3) pauliZ *
            (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin 3) spinHalfOpPlus), onSite_mul_onSite_same,
      spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
      onSite (2 : Fin 3) spinHalfOpMinus *
      onSite (0 : Fin 3) spinHalfOpPlus =
        onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
    have step1 : onSite (2 : Fin 3) spinHalfOpMinus *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (2 : Fin 3) spinHalfOpMinus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpMinus spinHalfOpPlus
    have step2 : onSite (1 : Fin 3) pauliZ *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (1 : Fin 3) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          onSite (2 : Fin 3) spinHalfOpMinus *
          onSite (0 : Fin 3) spinHalfOpPlus
        = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (2 : Fin 3) spinHalfOpMinus *
            onSite (0 : Fin 3) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpMinus) := by rw [step1]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ *
            (onSite (0 : Fin 3) spinHalfOpPlus *
              onSite (2 : Fin 3) spinHalfOpMinus)) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpMinus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpMinus) := by rw [step2]
      _ = onSite (0 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) (pauliZ * spinHalfOpPlus) *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
          rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
          rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Cross-site CAR `{c_0, c_2} = 0` for any chain length `N ≥ 2`.
Generalises PR #116 (Fin 3) to arbitrary `Fin (N+1)` using the same
`jwString_succ_eq` factorisation. -/
theorem fermionMultiAnnihilation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  -- jwString at sites 1 and 2 via jwString_succ_eq
  have hjw1 : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (0 : Fin (N + 1))
      (show (0 : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    simpa [jwString_zero] using h
  have hjw2 : jwString N ⟨2, by omega⟩ =
      onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (⟨1, by omega⟩ : Fin (N + 1))
      (show (⟨1, _⟩ : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    rw [hjw1] at h
    convert h using 2
  show onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw2]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      show (0 : Fin (N + 1)).val ≠ (⟨1, _⟩ : Fin (N + 1)).val
      simp)
  have h02 : (0 : Fin (N + 1)) ≠ ⟨2, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      show (0 : Fin (N + 1)).val ≠ (⟨2, _⟩ : Fin (N + 1)).val
      simp)
  -- Same as PR #116 structure
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus)) := by
    rw [show onSite (0 : Fin (N + 1)) pauliZ *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) pauliZ *
            (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin (N + 1)) spinHalfOpPlus),
      onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
      onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
    have step1 : onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpPlus spinHalfOpPlus
    have step2 : onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus
        = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by rw [step1]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus)) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by rw [step2]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) (pauliZ * spinHalfOpPlus) *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Dual `{c_0†, c_2†} = 0` for any `N ≥ 2` via adjoint of PR #123. -/
theorem fermionMultiCreation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_two_general N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ from add_comm _ _]
  exact h2

/-- Mixed `{c_0, c_2†} = 0` for any `N ≥ 2`. Same template as PR #123
with `σ^+_2` replaced by `σ^-_2`. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw1 : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (0 : Fin (N + 1))
      (show (0 : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    simpa [jwString_zero] using h
  have hjw2 : jwString N ⟨2, by omega⟩ =
      onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (⟨1, by omega⟩ : Fin (N + 1))
      (show (⟨1, _⟩ : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    rw [hjw1] at h
    convert h using 2
  show onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw2]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      show (0 : Fin (N + 1)).val ≠ (⟨1, _⟩ : Fin (N + 1)).val
      simp)
  have h02 : (0 : Fin (N + 1)) ≠ ⟨2, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      show (0 : Fin (N + 1)).val ≠ (⟨2, _⟩ : Fin (N + 1)).val
      simp)
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus)) := by
    rw [show onSite (0 : Fin (N + 1)) pauliZ *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus =
        onSite (0 : Fin (N + 1)) pauliZ *
            (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin (N + 1)) spinHalfOpPlus),
      onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
      onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
    have step1 : onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpMinus spinHalfOpPlus
    have step2 : onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus
        = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by rw [step1]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus)) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by rw [step2]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) (pauliZ * spinHalfOpPlus) *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Mixed dual `{c_0†, c_2} = 0` for any `N ≥ 2` via adjoint. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_two_general N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR `{c_0†, c_2} = 0` on `Fin 3` via adjoint of
PR #119. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_two_fin_three :
    fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        fermionMultiCreation 2 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_two_fin_three
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) =
      fermionMultiAnnihilation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) +
      fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 from add_comm _ _]
  exact h2

/-- Cross-site CAR `{c_0†, c_2†} = 0` on `Fin 3`. Direct consequence
of PR #116 via `conjTranspose`. -/
theorem fermionMultiCreation_anticomm_zero_two_fin_three :
    fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        fermionMultiCreation 2 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_two_fin_three
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) =
      fermionMultiCreation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) +
      fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 from add_comm _ _]
  exact h2

/-- Fourth off-diagonal CAR on `Fin 2`: `c_0† · c_1 + c_1 · c_0† = 0`.
Obtained from PR #110's mixed annihilation/creation version by taking
`conjTranspose`. Completes the 2-site off-diagonal CAR relations. -/
theorem fermionMultiCreation_annihilation_anticomm_two_site_cross :
    fermionMultiCreation 1 (0 : Fin 2) *
        fermionMultiAnnihilation 1 1 +
      fermionMultiAnnihilation 1 1 *
        fermionMultiCreation 1 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_two_site_cross
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  -- h2 : c_1 · c_0† + c_0† · c_1 = 0, goal: c_0† · c_1 + c_1 · c_0† = 0
  rw [show fermionMultiCreation 1 (0 : Fin 2) * fermionMultiAnnihilation 1 1 +
        fermionMultiAnnihilation 1 1 * fermionMultiCreation 1 (0 : Fin 2) =
      fermionMultiAnnihilation 1 1 * fermionMultiCreation 1 (0 : Fin 2) +
        fermionMultiCreation 1 (0 : Fin 2) * fermionMultiAnnihilation 1 1
    from add_comm _ _]
  exact h2

/-! ## Number / annihilation-creation commutators -/

/-- Standard fermion algebra: `[n_i, c_i] = -c_i`. -/
theorem fermionMultiNumber_commutator_fermionMultiAnnihilation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiAnnihilation N i -
        fermionMultiAnnihilation N i * fermionMultiNumber N i =
      -fermionMultiAnnihilation N i := by
  rw [fermionMultiNumber_eq_onSite]
  unfold fermionMultiAnnihilation
  -- n_i · c_i = onSite i (σ^- σ^+) · jwString N i · onSite i σ^+
  --         = jwString N i · onSite i (σ^- σ^+ · σ^+) = 0  (σ^+ σ^+ = 0)
  have hcomm_jw_minusPlus : Commute (jwString N i)
      (onSite i (spinHalfOpMinus * spinHalfOpPlus)) :=
    jwString_commute_onSite N i (spinHalfOpMinus * spinHalfOpPlus)
  have hncv : onSite i (spinHalfOpMinus * spinHalfOpPlus) *
      (jwString N i * onSite i spinHalfOpPlus) = 0 := by
    rw [← Matrix.mul_assoc, ← hcomm_jw_minusPlus.eq, Matrix.mul_assoc,
      onSite_mul_onSite_same]
    rw [show spinHalfOpMinus * spinHalfOpPlus * spinHalfOpPlus = 0 from by
      rw [Matrix.mul_assoc, spinHalfOpPlus_mul_self, Matrix.mul_zero]]
    rw [show onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ) =
        (0 : ManyBodyOp (Fin (N + 1))) from by ext σ' σ; simp [onSite_apply]]
    rw [Matrix.mul_zero]
  -- c_i · n_i = jwString N i · onSite i (σ^+ · σ^- σ^+) = jwString N i · onSite i σ^+ = c_i.
  have hcvn : (jwString N i * onSite i spinHalfOpPlus) *
      onSite i (spinHalfOpMinus * spinHalfOpPlus) =
      jwString N i * onSite i spinHalfOpPlus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_same]
    rw [show spinHalfOpPlus * (spinHalfOpMinus * spinHalfOpPlus) = spinHalfOpPlus from
      by rw [← Matrix.mul_assoc, spinHalfOpPlus_mul_spinHalfOpMinus_mul_spinHalfOpPlus]]
  rw [hncv, hcvn, zero_sub]

/-- Dual: `[n_i, c_i†] = c_i†`. Direct consequence of
`fermionMultiNumber_commutator_fermionMultiAnnihilation_self` by
taking `conjTranspose`. -/
theorem fermionMultiNumber_commutator_fermionMultiCreation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiCreation N i -
        fermionMultiCreation N i * fermionMultiNumber N i =
      fermionMultiCreation N i := by
  have h := fermionMultiNumber_commutator_fermionMultiAnnihilation_self N i
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_neg,
    fermionMultiAnnihilation_conjTranspose,
    (fermionMultiNumber_isHermitian N i).eq] at h2
  -- h2 : c_i† · n_i - n_i · c_i† = -c_i†
  -- Rewrite goal as negation of h2.
  rw [show fermionMultiNumber N i * fermionMultiCreation N i -
        fermionMultiCreation N i * fermionMultiNumber N i =
      -(fermionMultiCreation N i * fermionMultiNumber N i -
          fermionMultiNumber N i * fermionMultiCreation N i) from by abel]
  rw [h2]
  exact neg_neg _

/-- For `i ≠ j`, `n_i` commutes with `c_j` as operators. The `σ^z_i`
factor inside `jwString N j` commutes with `n_i` (since `[n, σ^z] = 0`
as matrices); disjoint-site factors commute trivially. -/
theorem fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i) (fermionMultiAnnihilation N j) := by
  rw [fermionMultiNumber_eq_onSite]
  unfold fermionMultiAnnihilation
  have hcomm_onSite_i_j : Commute (onSite i (spinHalfOpMinus * spinHalfOpPlus))
      (onSite j spinHalfOpPlus) := by
    show onSite i (spinHalfOpMinus * spinHalfOpPlus) * onSite j spinHalfOpPlus =
      onSite j spinHalfOpPlus * onSite i (spinHalfOpMinus * spinHalfOpPlus)
    exact onSite_mul_onSite_of_ne hij (spinHalfOpMinus * spinHalfOpPlus)
      spinHalfOpPlus
  have hcomm_onSite_i_jwString :
      Commute (onSite i (spinHalfOpMinus * spinHalfOpPlus)) (jwString N j) := by
    unfold jwString
    apply Finset.noncommProd_commute
    intro k _
    by_cases hki : k = i
    · subst hki
      show onSite k (spinHalfOpMinus * spinHalfOpPlus) * onSite k pauliZ =
        onSite k pauliZ * onSite k (spinHalfOpMinus * spinHalfOpPlus)
      rw [onSite_mul_onSite_same, onSite_mul_onSite_same,
        spinHalfOpMinus_mul_spinHalfOpPlus_commute_pauliZ.eq]
    · exact onSite_mul_onSite_of_ne (Ne.symm hki)
        (spinHalfOpMinus * spinHalfOpPlus) pauliZ
  exact hcomm_onSite_i_jwString.mul_right hcomm_onSite_i_j

/-- `[N̂, c_j] = -c_j`: the total particle-number operator shifts
annihilation operators down by one. Sum of the diagonal contribution
`[n_j, c_j] = -c_j` with the vanishing off-diagonal terms `[n_i, c_j] = 0`
for `i ≠ j`. -/
theorem fermionTotalNumber_commutator_fermionMultiAnnihilation
    (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalNumber N * fermionMultiAnnihilation N j -
        fermionMultiAnnihilation N j * fermionTotalNumber N =
      -fermionMultiAnnihilation N j := by
  unfold fermionTotalNumber
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ i : Fin (N + 1),
        (fermionMultiNumber N i * fermionMultiAnnihilation N j -
          fermionMultiAnnihilation N j * fermionMultiNumber N i)) =
      (fermionMultiNumber N j * fermionMultiAnnihilation N j -
          fermionMultiAnnihilation N j * fermionMultiNumber N j) from by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    rw [show (∑ i ∈ (Finset.univ : Finset (Fin (N + 1))).erase j,
          (fermionMultiNumber N i * fermionMultiAnnihilation N j -
            fermionMultiAnnihilation N j * fermionMultiNumber N i)) = 0 from by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_erase] at hi
      have h : fermionMultiNumber N i * fermionMultiAnnihilation N j =
          fermionMultiAnnihilation N j * fermionMultiNumber N i :=
        (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hi.1)
      rw [h, sub_self]]
    rw [zero_add]]
  exact fermionMultiNumber_commutator_fermionMultiAnnihilation_self N j

/-- Dual: `Commute (n_i) (c_j†)` for `i ≠ j`. Direct consequence of
`fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne` by taking
matrix `conjTranspose`. -/
theorem fermionMultiNumber_commute_fermionMultiCreation_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i) (fermionMultiCreation N j) := by
  have h := fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hij
  -- Commute A B means A * B = B * A
  -- Take conjTranspose: B† * A† = A† * B†, i.e. Commute A† B†.
  have h_eq : fermionMultiNumber N i * fermionMultiAnnihilation N j =
      fermionMultiAnnihilation N j * fermionMultiNumber N i := h
  have h2 := congrArg Matrix.conjTranspose h_eq
  simp only [Matrix.conjTranspose_mul, fermionMultiAnnihilation_conjTranspose,
    (fermionMultiNumber_isHermitian N i).eq] at h2
  -- h2 : c_j† * n_i = n_i * c_j†, i.e. Commute (fermionMultiCreation N j) (fermionMultiNumber N i).
  -- Flip for target form.
  exact h2.symm

/-- `[N̂, c_j†] = c_j†`: dual of PR #130 via adjoint. -/
theorem fermionTotalNumber_commutator_fermionMultiCreation
    (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalNumber N * fermionMultiCreation N j -
        fermionMultiCreation N j * fermionTotalNumber N =
      fermionMultiCreation N j := by
  have h := fermionTotalNumber_commutator_fermionMultiAnnihilation N j
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_neg,
    fermionMultiAnnihilation_conjTranspose,
    (fermionTotalNumber_isHermitian N).eq] at h2
  -- h2 : c_j† · N̂ - N̂ · c_j† = -c_j†
  rw [show fermionTotalNumber N * fermionMultiCreation N j -
        fermionMultiCreation N j * fermionTotalNumber N =
      -(fermionMultiCreation N j * fermionTotalNumber N -
          fermionTotalNumber N * fermionMultiCreation N j) from by abel]
  rw [h2]
  exact neg_neg _

/-- The hopping operator `c_i† · c_j` commutes with the total
particle-number operator `N̂`. Follows from `[N̂, c_i†] = c_i†`
and `[N̂, c_j] = -c_j`: the shifts cancel. -/
theorem fermionTotalNumber_commute_hopping (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalNumber N)
      (fermionMultiCreation N i * fermionMultiAnnihilation N j) := by
  -- From [N̂, c_i†] = c_i†: N̂ · c_i† = c_i† · N̂ + c_i†.
  have h_cr : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i := by
    have h := fermionTotalNumber_commutator_fermionMultiCreation N i
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  -- From [N̂, c_j] = -c_j: N̂ · c_j = c_j · N̂ - c_j.
  have h_an : fermionTotalNumber N * fermionMultiAnnihilation N j =
      fermionMultiAnnihilation N j * fermionTotalNumber N -
        fermionMultiAnnihilation N j := by
    have h := fermionTotalNumber_commutator_fermionMultiAnnihilation N j
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  -- Combine: N̂ · c_i† · c_j = c_i† · N̂ · c_j + c_i† · c_j
  --                        = c_i† · (c_j · N̂ - c_j) + c_i† · c_j
  --                        = c_i† · c_j · N̂ - c_i† · c_j + c_i† · c_j
  --                        = c_i† · c_j · N̂.
  show fermionTotalNumber N *
      (fermionMultiCreation N i * fermionMultiAnnihilation N j) =
    (fermionMultiCreation N i * fermionMultiAnnihilation N j) *
      fermionTotalNumber N
  calc fermionTotalNumber N *
        (fermionMultiCreation N i * fermionMultiAnnihilation N j)
      = (fermionTotalNumber N * fermionMultiCreation N i) *
          fermionMultiAnnihilation N j := by rw [Matrix.mul_assoc]
    _ = (fermionMultiCreation N i * fermionTotalNumber N +
          fermionMultiCreation N i) * fermionMultiAnnihilation N j := by rw [h_cr]
    _ = fermionMultiCreation N i * fermionTotalNumber N *
          fermionMultiAnnihilation N j +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [Matrix.add_mul]
    _ = fermionMultiCreation N i *
          (fermionTotalNumber N * fermionMultiAnnihilation N j) +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [Matrix.mul_assoc]
    _ = fermionMultiCreation N i *
          (fermionMultiAnnihilation N j * fermionTotalNumber N -
            fermionMultiAnnihilation N j) +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [h_an]
    _ = fermionMultiCreation N i *
          (fermionMultiAnnihilation N j * fermionTotalNumber N) -
        fermionMultiCreation N i * fermionMultiAnnihilation N j +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [Matrix.mul_sub]
    _ = fermionMultiCreation N i *
          (fermionMultiAnnihilation N j * fermionTotalNumber N) := by abel
    _ = (fermionMultiCreation N i * fermionMultiAnnihilation N j) *
          fermionTotalNumber N := by rw [← Matrix.mul_assoc]

/-- The site-occupation number `n_i` commutes with the total
particle-number operator `N̂ = Σ_j n_j`: since `n_i` commutes with each
`n_j` (`fermionMultiNumber_commute`), it commutes with their sum. -/
theorem fermionMultiNumber_commute_fermionTotalNumber (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (fermionTotalNumber N) := by
  unfold fermionTotalNumber
  exact Commute.sum_right _ _ _ (fun j _ => fermionMultiNumber_commute N i j)

/-- The density-density operator `n_i · n_j` commutes with the total
particle-number operator `N̂ = Σ_k n_k`. Since both `n_i` and `n_j`
individually commute with `N̂`
(`fermionMultiNumber_commute_fermionTotalNumber`), so does their
product. This is the foundational identity that makes any
density–density interaction (e.g. the Hubbard `U Σ_i n_{i,↑} n_{i,↓}`,
once two species are introduced) particle-number conserving. -/
theorem fermionDensityDensity_commute_fermionTotalNumber
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i * fermionMultiNumber N j)
      (fermionTotalNumber N) :=
  (fermionMultiNumber_commute_fermionTotalNumber N i).mul_left
    (fermionMultiNumber_commute_fermionTotalNumber N j)

/-- The general single-particle hopping operator on `Fin (N + 1)`
modes with arbitrary complex coefficients
`t : Fin (N+1) → Fin (N+1) → ℂ`:
`H_hop = Σ_{i,j} t_{i,j} · c_i† c_j`. This is the kinetic part of
any tight-binding or Hubbard-style Hamiltonian. -/
noncomputable def fermionHopping (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (N + 1)) :=
  ∑ i, ∑ j, t i j •
    (fermionMultiCreation N i * fermionMultiAnnihilation N j)

/-- The general hopping operator commutes with the total particle-
number operator `N̂`: every term `c_i† c_j` commutes with `N̂`
(`fermionTotalNumber_commute_hopping`), the scalar action `t_{ij} •`
preserves the commute, and finite sums of pairwise commuting
operators commute with `N̂`. This is charge conservation for the
kinetic Hamiltonian. -/
theorem fermionHopping_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionHopping N t) (fermionTotalNumber N) := by
  unfold fermionHopping
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact ((fermionTotalNumber_commute_hopping N i j).symm).smul_left (t i j)

end LatticeSystem.Fermion
