/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.GibbsState
import LatticeSystem.Fermion.Mode
import LatticeSystem.Lattice.Graph

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
  change onSite (0 : Fin 2) spinHalfOpPlus *
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
  change onSite (0 : Fin 2) spinHalfOpPlus *
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
      · rw [h]; change (0 : ℕ) < 1; omega
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
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
      · rw [h]; change (0 : ℕ) < 1; omega
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
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
  change onSite (0 : Fin 3) spinHalfOpPlus *
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
  change onSite (0 : Fin 3) spinHalfOpPlus *
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
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw2]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨1, _⟩ : Fin (N + 1)).val
      simp)
  have h02 : (0 : Fin (N + 1)) ≠ ⟨2, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨2, _⟩ : Fin (N + 1)).val
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
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw2]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨1, _⟩ : Fin (N + 1)).val
      simp)
  have h02 : (0 : Fin (N + 1)) ≠ ⟨2, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨2, _⟩ : Fin (N + 1)).val
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

/-! ## General cross-site CAR at site zero (`{c_0, c_k} = 0`, `k ≥ 1`)

For every `k : Fin (N + 1)` with `0 < k.val`, the Jordan-Wigner
string at site `k` anticommutes with the single-site raising
operator at site `0`:

  `σ^+_0 · jwString N k + jwString N k · σ^+_0 = 0`.

The proof is by induction on the number of factors in the string.
At one factor (`k.val = 1`) the string is exactly `σ^z_0`, and the
single-site Pauli identity `σ^+ σ^z + σ^z σ^+ = 0` closes the base
case. The inductive step appends one more `σ^z_j` at a site
`j ≥ 1` which commutes with `σ^+_0` (different sites), so the
anticommutation propagates unchanged.

Combined with the fact that `σ^+_0` commutes with the site-`k`
raising operator `σ^+_k` for `k ≠ 0`, this yields the full
cross-site CAR

  `c_0 · c_k + c_k · c_0 = 0` for every `k : Fin (N + 1)`
  with `0 < k.val`,

generalising the already-established
`fermionMultiAnnihilation_anticomm_zero_{one,two_general}` special
cases. The three companion off-diagonal CAR relations
(`{c_0, c_k†}`, `{c_0†, c_k}`, `{c_0†, c_k†}`) follow by
replacing `σ^+` with `σ^-` in the same argument — or by taking
matrix `conjTranspose` of the annihilation/annihilation version. -/

/-- Inductive helper: for every `m : ℕ` with `m + 1 < N + 1`, the
Jordan-Wigner string `jwString N ⟨m + 1, _⟩` anticommutes with
`σ^+_0`. Proof by induction on `m`. -/
private lemma jwString_anticomm_onSite_zero_spinHalfOpPlus
    (N : ℕ) (m : ℕ) :
    ∀ (hm : m + 1 < N + 1),
      onSite (0 : Fin (N + 1)) spinHalfOpPlus * jwString N ⟨m + 1, hm⟩ +
        jwString N ⟨m + 1, hm⟩ *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0 := by
  induction m with
  | zero =>
    intro hm
    have hjw : jwString N (⟨1, hm⟩ : Fin (N + 1)) =
        onSite (0 : Fin (N + 1)) pauliZ := by
      have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
          (fun j : Fin (N + 1) => j.val < (⟨1, hm⟩ : Fin (N + 1)).val) =
          ({(0 : Fin (N + 1))} : Finset (Fin (N + 1))) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · apply Fin.ext
          have : (k.val : ℕ) < 1 := h
          change k.val = 0
          omega
        · rw [h]; change (0 : ℕ) < 1; omega
      unfold jwString
      rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
      exact Finset.noncommProd_singleton _ _
    rw [hjw, onSite_mul_onSite_same, onSite_mul_onSite_same,
      ← onSite_add, spinHalfOpPlus_mul_pauliZ, pauliZ_mul_spinHalfOpPlus,
      neg_add_cancel, onSite_zero]
  | succ m' ih =>
    intro hm
    have hm' : m' + 1 < N + 1 := by omega
    have IH := ih hm'
    have hm'' : (⟨m' + 1, hm'⟩ : Fin (N + 1)).val + 1 < N + 1 := by
      change m' + 1 + 1 < N + 1; exact hm
    have hrec : jwString N (⟨m' + 1 + 1, hm⟩ : Fin (N + 1)) =
        jwString N (⟨m' + 1, hm'⟩ : Fin (N + 1)) *
          onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ := by
      have h := jwString_succ_eq N (⟨m' + 1, hm'⟩ : Fin (N + 1)) hm''
      convert h using 2
    have h_ne : (0 : Fin (N + 1)) ≠ ⟨m' + 1, hm'⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) (by
        change (0 : ℕ) ≠ m' + 1
        omega)
    have hcomm : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ =
      onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus :=
      onSite_mul_onSite_of_ne h_ne _ _
    rw [hrec]
    -- Goal: σ^+_0 * (JW_{m'+1} * σ^z_{m'+1}) + JW_{m'+1} * σ^z_{m'+1} * σ^+_0 = 0
    set A := onSite (0 : Fin (N + 1)) spinHalfOpPlus
    set B := jwString N (⟨m' + 1, hm'⟩ : Fin (N + 1))
    set Z := onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ
    have hstep : A * (B * Z) + B * Z * A = (A * B + B * A) * Z := by
      calc A * (B * Z) + B * Z * A
          = A * B * Z + B * Z * A := by rw [← Matrix.mul_assoc]
        _ = A * B * Z + B * (Z * A) := by rw [Matrix.mul_assoc B]
        _ = A * B * Z + B * (A * Z) := by rw [← hcomm]
        _ = A * B * Z + B * A * Z := by rw [← Matrix.mul_assoc B]
        _ = (A * B + B * A) * Z := by rw [Matrix.add_mul]
    rw [hstep, IH, Matrix.zero_mul]

/-- General cross-site CAR at site zero: for every `N : ℕ` and every
`k : Fin (N + 1)` with `0 < k.val`,

  `c_0 · c_k + c_k · c_0 = 0`.

Generalises `fermionMultiAnnihilation_anticomm_zero_one` (the
`k.val = 1` special case) and
`fermionMultiAnnihilation_anticomm_zero_two_general` (the
`k.val = 2` special case). The proof reduces the cross-site
anticommutator of the fermion operators to the anticommutator
`{σ^+_0, jwString N k}`, which vanishes by
`jwString_anticomm_onSite_zero_spinHalfOpPlus`. -/
theorem fermionMultiAnnihilation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N k +
      fermionMultiAnnihilation N k *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  -- Reduce to σ^+_0 anticommuting with jwString_k, modulo commuting
  -- σ^+_0 past σ^+_k (different sites).
  have hm : k.val - 1 + 1 < N + 1 := by
    have := k.isLt; omega
  have hkeq : k = ⟨k.val - 1 + 1, hm⟩ := by
    apply Fin.ext
    change k.val = k.val - 1 + 1
    omega
  have h_ne : (0 : Fin (N + 1)) ≠ k := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : ℕ) ≠ k.val
      omega)
  have h_ne_sym : k ≠ (0 : Fin (N + 1)) := h_ne.symm
  -- c_k = jwString N k * onSite k σ^+
  unfold fermionMultiAnnihilation
  -- Goal: σ^+_0 * (JW_k * σ^+_k) + (JW_k * σ^+_k) * σ^+_0 = 0
  set A := onSite (0 : Fin (N + 1)) spinHalfOpPlus
  set B := jwString N k
  set P := onSite k spinHalfOpPlus
  have hcomm_AP : A * P = P * A :=
    onSite_mul_onSite_of_ne h_ne _ _
  have hanticomm : A * B + B * A = 0 := by
    change onSite (0 : Fin (N + 1)) spinHalfOpPlus * jwString N k +
      jwString N k * onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
    rw [hkeq]
    exact jwString_anticomm_onSite_zero_spinHalfOpPlus N (k.val - 1) hm
  -- Goal: A * (B * P) + B * P * A = 0
  calc A * (B * P) + B * P * A
      = A * B * P + B * P * A := by rw [← Matrix.mul_assoc]
    _ = A * B * P + B * (P * A) := by rw [Matrix.mul_assoc B]
    _ = A * B * P + B * (A * P) := by rw [← hcomm_AP]
    _ = A * B * P + B * A * P := by rw [← Matrix.mul_assoc B]
    _ = (A * B + B * A) * P := by rw [Matrix.add_mul]
    _ = 0 * P := by rw [hanticomm]
    _ = 0 := Matrix.zero_mul _

/-- Dual `{c_0†, c_k†} = 0` for any `k : Fin (N + 1)` with
`0 < k.val`, via `conjTranspose` of
`fermionMultiAnnihilation_anticomm_zero_pos`. -/
theorem fermionMultiCreation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N k +
      fermionMultiCreation N k *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_pos N k hk
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiCreation N k +
        fermionMultiCreation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiCreation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) +
        fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiCreation N k from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR `{c_0, c_k†} = 0` for every `k : Fin (N + 1)`
with `0 < k.val`. Proof: identical structure to
`fermionMultiAnnihilation_anticomm_zero_pos`, since `c_k†` differs
from `c_k` only by the single-site factor at `k` (`σ^-_k` instead of
`σ^+_k`); the JW-string part is unchanged. Generalises
`fermionMultiAnnihilation_creation_anticomm_zero_one` and
`fermionMultiAnnihilation_creation_anticomm_zero_two_general`. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N k +
      fermionMultiCreation N k *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hm : k.val - 1 + 1 < N + 1 := by
    have := k.isLt; omega
  have hkeq : k = ⟨k.val - 1 + 1, hm⟩ := by
    apply Fin.ext
    change k.val = k.val - 1 + 1
    omega
  have h_ne : (0 : Fin (N + 1)) ≠ k := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : ℕ) ≠ k.val
      omega)
  unfold fermionMultiCreation
  set A := onSite (0 : Fin (N + 1)) spinHalfOpPlus
  set B := jwString N k
  set M := onSite k spinHalfOpMinus
  have hcomm_AM : A * M = M * A :=
    onSite_mul_onSite_of_ne h_ne _ _
  have hanticomm : A * B + B * A = 0 := by
    change onSite (0 : Fin (N + 1)) spinHalfOpPlus * jwString N k +
      jwString N k * onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
    rw [hkeq]
    exact jwString_anticomm_onSite_zero_spinHalfOpPlus N (k.val - 1) hm
  calc A * (B * M) + B * M * A
      = A * B * M + B * M * A := by rw [← Matrix.mul_assoc]
    _ = A * B * M + B * (M * A) := by rw [Matrix.mul_assoc B]
    _ = A * B * M + B * (A * M) := by rw [← hcomm_AM]
    _ = A * B * M + B * A * M := by rw [← Matrix.mul_assoc B]
    _ = (A * B + B * A) * M := by rw [Matrix.add_mul]
    _ = 0 * M := by rw [hanticomm]
    _ = 0 := Matrix.zero_mul _

/-- Mixed cross-site CAR `{c_0†, c_k} = 0` for every `k : Fin (N + 1)`
with `0 < k.val`, via `conjTranspose` of
`fermionMultiAnnihilation_creation_anticomm_zero_pos`. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N k +
      fermionMultiAnnihilation N k *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_pos N k hk
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiAnnihilation N k +
        fermionMultiAnnihilation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiAnnihilation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) +
        fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiAnnihilation N k from add_comm _ _]
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
    change onSite i (spinHalfOpMinus * spinHalfOpPlus) * onSite j spinHalfOpPlus =
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
      change onSite k (spinHalfOpMinus * spinHalfOpPlus) * onSite k pauliZ =
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
  change fermionTotalNumber N *
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

/-- The general density-density interaction on `Fin (N + 1)` modes
with arbitrary complex coefficients `V : Fin (N+1) → Fin (N+1) → ℂ`:
`V_int = Σ_{i,j} V_{i,j} · n_i n_j`. Captures any density–density
potential (extended Hubbard, long-range Coulomb on a chain, etc.). -/
noncomputable def fermionDensityInteraction (N : ℕ)
    (V : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (N + 1)) :=
  ∑ i, ∑ j, V i j •
    (fermionMultiNumber N i * fermionMultiNumber N j)

/-- The general density-density interaction commutes with the total
particle-number operator `N̂`: every term `n_i n_j` commutes with `N̂`
(`fermionDensityDensity_commute_fermionTotalNumber`), the scalar
action `V_{ij} •` preserves the commute, and finite sums commute.
Together with `fermionHopping_commute_fermionTotalNumber` this gives
charge conservation for any Hubbard-type Hamiltonian
`H = H_hop + V_int`. -/
theorem fermionDensityInteraction_commute_fermionTotalNumber
    (N : ℕ) (V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionDensityInteraction N V) (fermionTotalNumber N) := by
  unfold fermionDensityInteraction
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact (fermionDensityDensity_commute_fermionTotalNumber N i j).smul_left
    (V i j)

/-- The canonical charge-conserving fermion Hamiltonian on
`Fin (N + 1)` modes, the sum of a single-particle hopping term and a
density–density interaction:
`H = H_hop + V_int = Σ_{i,j} t_{i,j} c_i† c_j + Σ_{i,j} V_{i,j} n_i n_j`.
Captures the algebraic skeleton of single-species Hubbard / extended
Hubbard models on a chain. -/
noncomputable def fermionGenericHamiltonian (N : ℕ)
    (t V : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (N + 1)) :=
  fermionHopping N t + fermionDensityInteraction N V

/-- The canonical Hamiltonian `H = H_hop + V_int` commutes with the
total particle-number operator `N̂`. Both summands separately commute
with `N̂` (`fermionHopping_commute_fermionTotalNumber` and
`fermionDensityInteraction_commute_fermionTotalNumber`), so by
`Commute.add_left` so does their sum. This is the unified statement
of charge conservation for any Hubbard-type Hamiltonian. -/
theorem fermionGenericHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionGenericHamiltonian N t V) (fermionTotalNumber N) := by
  unfold fermionGenericHamiltonian
  exact (fermionHopping_commute_fermionTotalNumber N t).add_left
    (fermionDensityInteraction_commute_fermionTotalNumber N V)

/-- The product `n_i * n_j` is Hermitian: each `n_i` is Hermitian
(`fermionMultiNumber_isHermitian`) and `n_i, n_j` commute pairwise
(`fermionMultiNumber_commute`), so the product of two commuting
Hermitian operators is Hermitian. -/
theorem fermionMultiNumber_mul_isHermitian (N : ℕ) (i j : Fin (N + 1)) :
    (fermionMultiNumber N i * fermionMultiNumber N j).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute (fermionMultiNumber_isHermitian N i)
    (fermionMultiNumber_isHermitian N j) (fermionMultiNumber_commute N i j)

/-- The density-density interaction
`V_int = Σ_{i,j} V_{i,j} n_i n_j` is Hermitian whenever every
coupling entry is real (`star V_{i,j} = V_{i,j}`). Each `n_i n_j` is
Hermitian (commuting Hermitian factors), and `(V_{i,j} • n_i n_j)†
= star V_{i,j} • n_i n_j = V_{i,j} • n_i n_j` under the realness
hypothesis; the sum of Hermitians is Hermitian. -/
theorem fermionDensityInteraction_isHermitian
    (N : ℕ) {V : Fin (N + 1) → Fin (N + 1) → ℂ}
    (hV : ∀ i j, star (V i j) = V i j) :
    (fermionDensityInteraction N V).IsHermitian := by
  unfold fermionDensityInteraction Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  congr 1; funext i
  rw [Matrix.conjTranspose_sum]
  congr 1; funext j
  rw [Matrix.conjTranspose_smul, (fermionMultiNumber_mul_isHermitian N i j).eq,
    hV]

/-- Auxiliary: the conjugate transpose of a single hopping term
`c_i† * c_j` equals `c_j† * c_i`. -/
theorem fermionHoppingTerm_conjTranspose (N : ℕ) (i j : Fin (N + 1)) :
    (fermionMultiCreation N i * fermionMultiAnnihilation N j)ᴴ =
      fermionMultiCreation N j * fermionMultiAnnihilation N i := by
  rw [Matrix.conjTranspose_mul, fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose]

/-- The single-particle hopping operator
`H_hop = Σ_{i,j} t_{i,j} c_i† c_j` is Hermitian when the coupling
matrix `t` is Hermitian, i.e. `star (t i j) = t j i` for all
`i, j`. The conjugate transpose flips creation/annihilation and
reverses the index order; an `i ↔ j` reindexing brings the sum back
to its original form under the Hermiticity hypothesis. -/
theorem fermionHopping_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i) :
    (fermionHopping N t).IsHermitian := by
  change (fermionHopping N t)ᴴ = fermionHopping N t
  unfold fermionHopping
  calc (∑ i, ∑ j, t i j •
          (fermionMultiCreation N i * fermionMultiAnnihilation N j))ᴴ
      = ∑ i, (∑ j, t i j •
            (fermionMultiCreation N i * fermionMultiAnnihilation N j))ᴴ := by
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, (t i j •
            (fermionMultiCreation N i * fermionMultiAnnihilation N j))ᴴ := by
        congr 1; funext i
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, t j i •
            (fermionMultiCreation N j * fermionMultiAnnihilation N i) := by
        congr 1; funext i; congr 1; funext j
        rw [Matrix.conjTranspose_smul, fermionHoppingTerm_conjTranspose, ht]
    _ = ∑ j, ∑ i, t j i •
            (fermionMultiCreation N j * fermionMultiAnnihilation N i) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, t i j •
            (fermionMultiCreation N i * fermionMultiAnnihilation N j) := rfl

/-- The canonical fermion Hamiltonian `H = H_hop + V_int` is
Hermitian whenever the hopping matrix `t` is Hermitian
(`star (t i j) = t j i`) and the density-density coupling `V` is
entry-wise real (`star (V i j) = V i j`). Direct sum of
`fermionHopping_isHermitian` and `fermionDensityInteraction_isHermitian`
via `Matrix.IsHermitian.add`. -/
theorem fermionGenericHamiltonian_isHermitian
    (N : ℕ) {t V : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i)
    (hV : ∀ i j, star (V i j) = V i j) :
    (fermionGenericHamiltonian N t V).IsHermitian := by
  unfold fermionGenericHamiltonian
  exact (fermionHopping_isHermitian N ht).add
    (fermionDensityInteraction_isHermitian N hV)

/-! ## Hubbard-skeleton Gibbs state

Combining the canonical fermion Hamiltonian with the generic
`gibbsState` framework gives the Gibbs state of the Hubbard
skeleton. -/

/-- The Gibbs state of the canonical Hubbard-skeleton Hamiltonian
`H = H_hop + V_int`. -/
noncomputable def fermionGenericGibbsState
    (N : ℕ) (β : ℝ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    ManyBodyOp (Fin (N + 1)) :=
  LatticeSystem.Quantum.gibbsState β (fermionGenericHamiltonian N t V)

/-- The Hubbard-skeleton Gibbs state is Hermitian when `t` is
Hermitian and `V` is entry-wise real. -/
theorem fermionGenericGibbsState_isHermitian
    (N : ℕ) (β : ℝ) {t V : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i)
    (hV : ∀ i j, star (V i j) = V i j) :
    (fermionGenericGibbsState N β t V).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (fermionGenericHamiltonian_isHermitian N ht hV) β

/-- The Hubbard-skeleton Gibbs state commutes with its
Hamiltonian (instance of the generic
`gibbsState_commute_hamiltonian`). -/
theorem fermionGenericGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionGenericGibbsState N β t V)
      (fermionGenericHamiltonian N t V) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-! ## Fermion vacuum state

The Jordan–Wigner vacuum is the all-up many-body basis vector
`|↑↑…↑⟩`, since `c_i = jwString N i · σ^+_i` and
`σ^+ |↑⟩ = 0` site-locally. -/

/-- The fermion vacuum state on `Fin (N + 1)` JW modes: the
many-body computational-basis vector `|↑↑…↑⟩`. -/
noncomputable def fermionMultiVacuum (N : ℕ) : (Fin (N + 1) → Fin 2) → ℂ :=
  LatticeSystem.Quantum.basisVec (fun _ : Fin (N + 1) => (0 : Fin 2))

/-- The vacuum is annihilated by every fermion annihilation
operator: `c_i · |vac⟩ = 0` for every site `i`. Proof:
`c_i = jwString N i · σ^+_i`; the inner factor `σ^+_i` acts on
`|↑↑…↑⟩` by sending its site-`i` entry through `σ^+`, but
`σ^+ k 0 = 0` for both `k = 0, 1` since `σ^+ = !![0,1;0,0]`,
so the result vanishes; the outer `jwString` factor then maps
zero to zero. -/
theorem fermionMultiAnnihilation_mulVec_vacuum
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionMultiAnnihilation fermionMultiVacuum
  rw [← Matrix.mulVec_mulVec]
  have hinner : (LatticeSystem.Quantum.onSite i spinHalfOpPlus).mulVec
      (LatticeSystem.Quantum.basisVec
        (fun _ : Fin (N + 1) => (0 : Fin 2))) = 0 := by
    rw [LatticeSystem.Quantum.onSite_mulVec_basisVec]
    funext τ
    apply Finset.sum_eq_zero
    intro k _
    change spinHalfOpPlus k 0 *
      LatticeSystem.Quantum.basisVec
        (Function.update (fun _ => (0 : Fin 2)) i k) τ = 0
    fin_cases k <;> simp [spinHalfOpPlus]
  rw [hinner, Matrix.mulVec_zero]

/-- Each site-occupation number annihilates the vacuum:
`n_i · |vac⟩ = c_i† (c_i |vac⟩) = c_i† 0 = 0`. -/
theorem fermionMultiNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiNumber N i).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionMultiNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_vacuum,
    Matrix.mulVec_zero]

/-- The vacuum is an `N̂`-eigenstate with eigenvalue 0:
`N̂ · |vac⟩ = (Σ_j n_j) · |vac⟩ = Σ_j (n_j · |vac⟩) = 0`. -/
theorem fermionTotalNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalNumber N).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionTotalNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionMultiNumber_mulVec_vacuum N i)

/-- The hopping operator annihilates the vacuum:
`H_hop · |vac⟩ = Σ t_{ij} c_i† (c_j |vac⟩) = 0`. -/
theorem fermionHopping_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (fermionHopping N t).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionHopping
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiAnnihilation_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The density-density interaction annihilates the vacuum:
`V_int · |vac⟩ = Σ V_{ij} n_i (n_j |vac⟩) = 0`. -/
theorem fermionDensityInteraction_mulVec_vacuum
    (N : ℕ) (V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (fermionDensityInteraction N V).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionDensityInteraction
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiNumber_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The full Hubbard-skeleton Hamiltonian annihilates the vacuum:
`H · |vac⟩ = (H_hop + V_int) · |vac⟩ = 0 + 0 = 0`. -/
theorem fermionGenericHamiltonian_mulVec_vacuum
    (N : ℕ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (fermionGenericHamiltonian N t V).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionGenericHamiltonian
  rw [Matrix.add_mulVec, fermionHopping_mulVec_vacuum,
    fermionDensityInteraction_mulVec_vacuum, add_zero]

/-- The single-particle state `c_i† |vac⟩` is an `N̂`-eigenstate
with eigenvalue 1. Uses `[N̂, c_i†] = c_i†` (so
`N̂ c_i† = c_i† N̂ + c_i†`) and `N̂ |vac⟩ = 0`. -/
theorem fermionTotalNumber_mulVec_singleParticle
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i).mulVec (fermionMultiVacuum N)) =
      (fermionMultiCreation N i).mulVec (fermionMultiVacuum N) := by
  rw [Matrix.mulVec_mulVec]
  have h_comm : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N i)).trans
      (add_comm _ _)
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalNumber_mulVec_vacuum, Matrix.mulVec_zero, zero_add]

/-- **Charge-eigenstate helper.** If `X` carries U(1) charge `α`
(`[N̂, X] = α • X`) and `v` is `N̂`-annihilated, then `X v` is an
`N̂`-eigenstate with eigenvalue `α`. Generalises
`fermionTotalNumber_mulVec_singleParticle` (α = 1, X = c_i†) and
`fermionTotalNumber_mulVec_twoParticle` (α = 2, X = c_i† c_j†). -/
theorem fermionTotalNumber_mulVec_eigenstate_of_commute
    {N : ℕ} {X : ManyBodyOp (Fin (N + 1))} {α : ℂ}
    (hX : fermionTotalNumber N * X - X * fermionTotalNumber N = α • X)
    {v : (Fin (N + 1) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber N).mulVec v = 0) :
    (fermionTotalNumber N).mulVec (X.mulVec v) = α • X.mulVec v := by
  rw [Matrix.mulVec_mulVec]
  have h_comm : fermionTotalNumber N * X = X * fermionTotalNumber N + α • X :=
    (eq_add_of_sub_eq hX).trans (add_comm _ _)
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, zero_add, Matrix.smul_mulVec]

/-! ## Spinful (two-species) fermion operator wrappers

To realise true Hubbard / spinful fermion models we re-index a
single-species chain of length `2 * (N + 1)` as a chain of
`N + 1` spinful sites, with each site carrying a spin label
`σ : Fin 2`. The bijection `(i, σ) ↦ 2 * i + σ` puts the two
species at site `i` in the consecutive JW positions
`2 i` (spin up) and `2 i + 1` (spin down).

All algebraic facts about the two-species operators (CARs,
charge conservation, Hermiticity) follow for free from the
single-species results applied to the underlying chain. -/

/-- The spinful site index: `(i, σ) ↦ 2 * i + σ`. -/
def spinfulIndex (N : ℕ) (i : Fin (N + 1)) (σ : Fin 2) :
    Fin (2 * N + 2) :=
  ⟨2 * i.val + σ.val, by
    have hi : i.val < N + 1 := i.isLt
    have hσ : σ.val < 2 := σ.isLt
    omega⟩

/-- Spin-up annihilation operator at spinful site `i`:
the JW annihilation at the underlying single-species position
`2 * i`. -/
noncomputable def fermionUpAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down annihilation operator at spinful site `i`:
the JW annihilation at the underlying single-species position
`2 * i + 1`. -/
noncomputable def fermionDownAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 1)

/-- Spin-up creation operator at spinful site `i`. -/
noncomputable def fermionUpCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down creation operator at spinful site `i`. -/
noncomputable def fermionDownCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1)

/-- Spin-up site occupation number at spinful site `i`:
`n_{i,↑} = c_{i,↑}† · c_{i,↑}`. -/
noncomputable def fermionUpNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down site occupation number at spinful site `i`:
`n_{i,↓} = c_{i,↓}† · c_{i,↓}`. -/
noncomputable def fermionDownNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1)

/-- The on-site Hubbard interaction
`H_int = U Σ_i n_{i,↑} · n_{i,↓}` on the spinful chain. -/
noncomputable def hubbardOnSiteInteraction (N : ℕ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), U • (fermionUpNumber N i * fermionDownNumber N i)

/-- The Hubbard on-site interaction commutes with the total
particle-number operator `N̂` on the underlying chain (charge
conservation). -/
theorem hubbardOnSiteInteraction_commute_fermionTotalNumber
    (N : ℕ) (U : ℂ) :
    Commute (hubbardOnSiteInteraction N U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact (fermionDensityDensity_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).smul_left U

/-- The Hubbard on-site interaction is Hermitian when the coupling
`U` is real (`star U = U`). Each summand `n_{i,↑} · n_{i,↓}` is
Hermitian (commuting Hermitian factors), and the scalar `U`
preserves Hermiticity under the realness assumption. -/
theorem hubbardOnSiteInteraction_isHermitian
    (N : ℕ) {U : ℂ} (hU : star U = U) :
    (hubbardOnSiteInteraction N U).IsHermitian := by
  change (hubbardOnSiteInteraction N U)ᴴ = hubbardOnSiteInteraction N U
  unfold hubbardOnSiteInteraction
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_smul]
  unfold fermionUpNumber fermionDownNumber
  rw [(fermionMultiNumber_mul_isHermitian (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).eq, hU]

/-- The spin-symmetric tight-binding kinetic operator on the spinful
chain: `T = Σ_{σ} Σ_{i,j} t_{i,j} c_{i,σ}† c_{j,σ}`. Each spin
sector hops independently with the same coupling matrix `t`. -/
noncomputable def hubbardKinetic (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ σ : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    t i j • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))

/-- The spinful kinetic operator commutes with the total particle
number `N̂` on the underlying chain. Each summand
`t_{ij} • c_{iσ}† c_{jσ}` commutes with `N̂` via
`fermionTotalNumber_commute_hopping`, and finite sums preserve
this. -/
theorem hubbardKinetic_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (hubbardKinetic N t) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardKinetic
  refine Commute.sum_left _ _ _ (fun σ _ => ?_)
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact ((fermionTotalNumber_commute_hopping (2 * N + 1)
    (spinfulIndex N i σ) (spinfulIndex N j σ)).symm).smul_left (t i j)

/-- The spinful kinetic operator is Hermitian when the hopping
matrix `t` is Hermitian (`star (t i j) = t j i`). For each fixed
spin `σ`, the inner double sum is the single-species
`fermionHopping (2N+1) t̃` for the lifted coupling
`t̃ (spinfulIndex N i σ) (spinfulIndex N j σ) = t i j`; we prove
Hermiticity term-by-term using the conjTranspose flip and a
`Finset.sum_comm` index swap. -/
theorem hubbardKinetic_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i) :
    (hubbardKinetic N t).IsHermitian := by
  change (hubbardKinetic N t)ᴴ = hubbardKinetic N t
  unfold hubbardKinetic
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  calc (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), t i j •
          (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)))ᴴ
      = ∑ i, (∑ j, t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)))ᴴ := by
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, (t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)))ᴴ := by
        congr 1; funext i
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, t j i •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N j σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N i σ)) := by
        congr 1; funext i; congr 1; funext j
        rw [Matrix.conjTranspose_smul,
          fermionHoppingTerm_conjTranspose, ht]
    _ = ∑ j, ∑ i, t j i •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N j σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N i σ)) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)) := rfl

/-- The canonical (single-band) Hubbard Hamiltonian:
`H = Σ_{σ} Σ_{i,j} t_{i,j} c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}`. -/
noncomputable def hubbardHamiltonian (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N t + hubbardOnSiteInteraction N U

/-- The Hubbard Hamiltonian commutes with the total particle
number `N̂`: charge conservation. Direct from
`hubbardKinetic_commute_fermionTotalNumber` and
`hubbardOnSiteInteraction_commute_fermionTotalNumber` via
`Commute.add_left`. -/
theorem hubbardHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardHamiltonian N t U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHamiltonian
  exact (hubbardKinetic_commute_fermionTotalNumber N t).add_left
    (hubbardOnSiteInteraction_commute_fermionTotalNumber N U)

/-- The Hubbard Hamiltonian is Hermitian when the hopping matrix
`t` is Hermitian and the on-site coupling `U` is real. -/
theorem hubbardHamiltonian_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardHamiltonian N t U).IsHermitian := by
  unfold hubbardHamiltonian
  exact (hubbardKinetic_isHermitian N ht).add
    (hubbardOnSiteInteraction_isHermitian N hU)

/-- The Gibbs state of the canonical Hubbard Hamiltonian. -/
noncomputable def hubbardGibbsState
    (N : ℕ) (β : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardHamiltonian N t U)

/-- The Hubbard Gibbs state is Hermitian when `t` is Hermitian and
`U` is real. -/
theorem hubbardGibbsState_isHermitian
    (N : ℕ) (β : ℝ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardGibbsState N β t U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardHamiltonian_isHermitian N ht hU) β

/-- The Hubbard Gibbs state commutes with the Hubbard Hamiltonian
(generic instance of `gibbsState_commute_hamiltonian`). -/
theorem hubbardGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardGibbsState N β t U) (hubbardHamiltonian N t U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-! ## Spinful conserved charges N_↑, N_↓, and S^z_tot

The spinful Hilbert space carries two natural U(1) charges
(particle numbers per spin) and one diagonal SU(2) charge
(z-component of total spin). They all commute pairwise (and with
the total particle number `N̂`); commute with the full Hubbard
Hamiltonian is deferred to a later PR. -/

/-- Total spin-up particle number `N_↑ = Σ_i n_{i,↑}`. -/
noncomputable def fermionTotalUpNumber (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionUpNumber N i

/-- Total spin-down particle number `N_↓ = Σ_i n_{i,↓}`. -/
noncomputable def fermionTotalDownNumber (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionDownNumber N i

/-- Total z-component of spin `S^z_tot = (1/2)(N_↑ − N_↓)`. -/
noncomputable def fermionTotalSpinZ (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) • (fermionTotalUpNumber N - fermionTotalDownNumber N)

/-- `N_↑` and `N_↓` commute (sums of pairwise commuting number
operators). -/
theorem fermionTotalUpNumber_commute_fermionTotalDownNumber (N : ℕ) :
    Commute (fermionTotalUpNumber N) (fermionTotalDownNumber N) := by
  unfold fermionTotalUpNumber fermionTotalDownNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_right _ _ _ (fun j _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 1)

/-- `N_↑` commutes with the total particle number `N̂` on the
underlying chain. -/
theorem fermionTotalUpNumber_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalUpNumber N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalUpNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0)

/-- `N_↓` commutes with the total particle number `N̂` on the
underlying chain. -/
theorem fermionTotalDownNumber_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalDownNumber N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalDownNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 1)

/-- The total z-spin `S^z_tot` commutes with the total particle
number `N̂`: free corollary of the up/down individual commutes. -/
theorem fermionTotalSpinZ_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinZ N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinZ
  refine Commute.smul_left ?_ _
  exact (fermionTotalUpNumber_commute_fermionTotalNumber N).sub_left
    (fermionTotalDownNumber_commute_fermionTotalNumber N)

/-- `N_↑` commutes with the Hubbard on-site interaction
`U Σ_i n_{i↑} n_{i↓}`. All summands are products of pairwise
commuting number operators. -/
theorem fermionTotalUpNumber_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalUpNumber hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ U
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the Hubbard on-site interaction. -/
theorem fermionTotalDownNumber_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalDownNumber hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ U
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 1)

/-- `S^z_tot` commutes with the Hubbard on-site interaction. Free
corollary. -/
theorem fermionTotalSpinZ_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalSpinZ N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalSpinZ
  refine Commute.smul_left ?_ _
  exact (fermionTotalUpNumber_commute_hubbardOnSiteInteraction N U).sub_left
    (fermionTotalDownNumber_commute_hubbardOnSiteInteraction N U)

/-! ## Spinful vacuum eigenstate corollaries

The JW vacuum on the underlying chain `Fin (2N+2)` is the
canonical spinful vacuum. All single-species vacuum results lift
mechanically. -/

/-- The spin-up annihilation operator at any site kills the
vacuum. -/
theorem fermionUpAnnihilation_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpAnnihilation N i).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 0)

/-- The spin-down annihilation operator at any site kills the
vacuum. -/
theorem fermionDownAnnihilation_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownAnnihilation N i).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 1)

/-- `n_{i,↑} · |vac⟩ = 0`. -/
theorem fermionUpNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiNumber_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 0)

/-- `n_{i,↓} · |vac⟩ = 0`. -/
theorem fermionDownNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownNumber N i).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiNumber_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 1)

/-- `N_↑ · |vac⟩ = 0`. -/
theorem fermionTotalUpNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalUpNumber N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionUpNumber_mulVec_vacuum N i)

/-- `N_↓ · |vac⟩ = 0`. -/
theorem fermionTotalDownNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalDownNumber N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionDownNumber_mulVec_vacuum N i)

/-- The vacuum is unpolarised: `S^z_tot · |vac⟩ = 0`. -/
theorem fermionTotalSpinZ_mulVec_vacuum (N : ℕ) :
    (fermionTotalSpinZ N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    fermionTotalUpNumber_mulVec_vacuum,
    fermionTotalDownNumber_mulVec_vacuum, sub_zero, smul_zero]

/-- The Hubbard kinetic operator annihilates the vacuum. -/
theorem hubbardKinetic_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (hubbardKinetic N t).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardKinetic
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiAnnihilation_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The Hubbard on-site interaction annihilates the vacuum. -/
theorem hubbardOnSiteInteraction_mulVec_vacuum (N : ℕ) (U : ℂ) :
    (hubbardOnSiteInteraction N U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.smul_mulVec]
  unfold fermionUpNumber fermionDownNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiNumber_mulVec_vacuum,
    Matrix.mulVec_zero, smul_zero]

/-- The full Hubbard Hamiltonian annihilates the vacuum. -/
theorem hubbardHamiltonian_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    (hubbardHamiltonian N t U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardHamiltonian
  rw [Matrix.add_mulVec, hubbardKinetic_mulVec_vacuum,
    hubbardOnSiteInteraction_mulVec_vacuum, add_zero]

/-! ## Cross-spin commutes (different species commute) -/

/-- Even and odd JW positions are distinct: `spinfulIndex N i 0 ≠
spinfulIndex N j 1` (the up-channel position `2 i` is never the
down-channel position `2 j + 1`). -/
theorem spinfulIndex_up_ne_down (N : ℕ) (i j : Fin (N + 1)) :
    spinfulIndex N i 0 ≠ spinfulIndex N j 1 := by
  intro heq
  have h := congrArg Fin.val heq
  change False
  simp [spinfulIndex] at h
  omega

/-- `N_↓` commutes with every `c_{i,↑}†`: each summand
`n_{2k+1}` and `c_{2i}†` are at distinct JW positions. -/
theorem fermionTotalDownNumber_commute_fermionUpCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpCreation N i) := by
  unfold fermionTotalDownNumber fermionUpCreation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiCreation_of_ne
    ((spinfulIndex_up_ne_down N i k).symm).symm.symm

/-- `N_↓` commutes with every `c_{i,↑}`. -/
theorem fermionTotalDownNumber_commute_fermionUpAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpAnnihilation N i) := by
  unfold fermionTotalDownNumber fermionUpAnnihilation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    ((spinfulIndex_up_ne_down N i k).symm).symm.symm

/-- `N_↓` commutes with every `n_{i,↑}` (number operators always
commute, but here we record the cross-spin special case
explicitly). -/
theorem fermionTotalDownNumber_commute_fermionUpNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpNumber N i) := by
  unfold fermionTotalDownNumber fermionUpNumber
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N k 1) (spinfulIndex N i 0)

/-- `N_↑` commutes with every `c_{i,↓}†`. -/
theorem fermionTotalUpNumber_commute_fermionDownCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownCreation N i) := by
  unfold fermionTotalUpNumber fermionDownCreation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiCreation_of_ne
    (spinfulIndex_up_ne_down N k i)

/-- `N_↑` commutes with every `c_{i,↓}`. -/
theorem fermionTotalUpNumber_commute_fermionDownAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownAnnihilation N i) := by
  unfold fermionTotalUpNumber fermionDownAnnihilation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    (spinfulIndex_up_ne_down N k i)

/-- `N_↑` commutes with every `n_{i,↓}`. -/
theorem fermionTotalUpNumber_commute_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownNumber N i) := by
  unfold fermionTotalUpNumber fermionDownNumber
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the up-sector hopping term
`c_{i,↑}† · c_{j,↑}` (cross-spin). -/
theorem fermionTotalDownNumber_commute_upHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N)
      (fermionUpCreation N i * fermionUpAnnihilation N j) :=
  (fermionTotalDownNumber_commute_fermionUpCreation N i).mul_right
    (fermionTotalDownNumber_commute_fermionUpAnnihilation N j)

/-- `N_↑` commutes with the down-sector hopping term
`c_{i,↓}† · c_{j,↓}` (cross-spin). -/
theorem fermionTotalUpNumber_commute_downHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N)
      (fermionDownCreation N i * fermionDownAnnihilation N j) :=
  (fermionTotalUpNumber_commute_fermionDownCreation N i).mul_right
    (fermionTotalUpNumber_commute_fermionDownAnnihilation N j)

/-! ## Hubbard-on-graph wrappers (graph-centric Hubbard) -/

/-- Hubbard kinetic operator with hopping matrix derived from a
`SimpleGraph G` and uniform edge weight `J : ℂ`. -/
noncomputable def hubbardKineticOnGraph (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (LatticeSystem.Lattice.couplingOf G J)

/-- The graph-built Hubbard kinetic operator commutes with `N̂`. -/
theorem hubbardKineticOnGraph_commute_fermionTotalNumber
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J : ℂ) :
    Commute (hubbardKineticOnGraph N G J)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardKinetic_commute_fermionTotalNumber N _

/-- The graph-built Hubbard kinetic operator is Hermitian when
`J` is real: the coupling `couplingOf G J` is then a Hermitian
matrix on the (symmetric, decidable) graph. -/
theorem hubbardKineticOnGraph_isHermitian
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) :
    (hubbardKineticOnGraph N G J).IsHermitian := by
  unfold hubbardKineticOnGraph
  refine hubbardKinetic_isHermitian N (fun i j => ?_)
  rw [LatticeSystem.Lattice.couplingOf_real G hJ,
    LatticeSystem.Lattice.couplingOf_symm]

/-- The full Hubbard Hamiltonian with hopping derived from a
`SimpleGraph G` plus on-site interaction `U`. -/
noncomputable def hubbardHamiltonianOnGraph (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKineticOnGraph N G J + hubbardOnSiteInteraction N U

/-- The graph-built Hubbard Hamiltonian commutes with `N̂`. -/
theorem hubbardHamiltonianOnGraph_commute_fermionTotalNumber
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    Commute (hubbardHamiltonianOnGraph N G J U)
      (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHamiltonianOnGraph
  exact (hubbardKineticOnGraph_commute_fermionTotalNumber N G J).add_left
    (hubbardOnSiteInteraction_commute_fermionTotalNumber N U)

/-- The graph-built Hubbard Hamiltonian is Hermitian when both
`J` and `U` are real. -/
theorem hubbardHamiltonianOnGraph_isHermitian
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J U : ℂ} (hJ : star J = J) (hU : star U = U) :
    (hubbardHamiltonianOnGraph N G J U).IsHermitian := by
  unfold hubbardHamiltonianOnGraph
  exact (hubbardKineticOnGraph_isHermitian N G hJ).add
    (hubbardOnSiteInteraction_isHermitian N hU)

/-! ## 1D Hubbard chain instance -/

/-- The canonical 1D nearest-neighbour Hubbard Hamiltonian on a
chain of `N + 1` spinful sites, with hopping amplitude `J : ℝ`
(ferromagnetic sign convention `−J`) and on-site Coulomb
repulsion `U : ℝ`. -/
noncomputable def hubbardChainHamiltonian (N : ℕ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N (SimpleGraph.pathGraph (N + 1))
    (-(J : ℂ)) (U : ℂ)

/-- The 1D Hubbard chain Hamiltonian is Hermitian. -/
theorem hubbardChainHamiltonian_isHermitian (N : ℕ) (J U : ℝ) :
    (hubbardChainHamiltonian N J U).IsHermitian :=
  hubbardHamiltonianOnGraph_isHermitian N _ (by simp) (by simp)

/-- The 1D Hubbard chain Hamiltonian commutes with `N̂` (charge
conservation). -/
theorem hubbardChainHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (J U : ℝ) :
    Commute (hubbardChainHamiltonian N J U)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardHamiltonianOnGraph_commute_fermionTotalNumber N _ _ _

/-- `hubbardHamiltonianOnGraph` annihilates the vacuum. Both
`hubbardKinetic` and `hubbardOnSiteInteraction` do, by PR #166. -/
theorem hubbardHamiltonianOnGraph_mulVec_vacuum
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    (hubbardHamiltonianOnGraph N G J U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardHamiltonianOnGraph hubbardKineticOnGraph
  rw [Matrix.add_mulVec, hubbardKinetic_mulVec_vacuum,
    hubbardOnSiteInteraction_mulVec_vacuum, add_zero]

/-- The 1D Hubbard chain Hamiltonian annihilates the vacuum. Free
corollary of `hubbardHamiltonianOnGraph_mulVec_vacuum`. -/
theorem hubbardChainHamiltonian_mulVec_vacuum
    (N : ℕ) (J U : ℝ) :
    (hubbardChainHamiltonian N J U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  hubbardHamiltonianOnGraph_mulVec_vacuum N _ _ _

/-- The Gibbs state of the 1D Hubbard chain Hamiltonian. -/
noncomputable def hubbardChainGibbsState (N : ℕ) (β : ℝ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardChainHamiltonian N J U)

/-- The 1D Hubbard chain Gibbs state is Hermitian. -/
theorem hubbardChainGibbsState_isHermitian (N : ℕ) (β : ℝ) (J U : ℝ) :
    (hubbardChainGibbsState N β J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- The 1D Hubbard chain Gibbs state commutes with its
Hamiltonian. -/
theorem hubbardChainGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (J U : ℝ) :
    Commute (hubbardChainGibbsState N β J U)
      (hubbardChainHamiltonian N J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-- The two-particle state `c_i† c_j† |vac⟩` is an `N̂`-eigenstate
with eigenvalue 2. The Leibniz rule
`[N̂, AB] = [N̂,A]B + A[N̂,B]` together with `[N̂, c_†] = c_†`
yields `[N̂, c_i† c_j†] = 2 c_i† c_j†`; applied to the vacuum and
combined with `N̂ |vac⟩ = 0` this gives the eigenvalue 2. -/
theorem fermionTotalNumber_mulVec_twoParticle
    (N : ℕ) (i j : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N)) =
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N) := by
  rw [Matrix.mulVec_mulVec]
  have h₁ : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N i)).trans
      (add_comm _ _)
  have h₂ : fermionTotalNumber N * fermionMultiCreation N j =
      fermionMultiCreation N j * fermionTotalNumber N +
        fermionMultiCreation N j :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N j)).trans
      (add_comm _ _)
  have h_comm : fermionTotalNumber N *
      (fermionMultiCreation N i * fermionMultiCreation N j) =
      (fermionMultiCreation N i * fermionMultiCreation N j) *
        fermionTotalNumber N +
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j) := by
    calc fermionTotalNumber N *
          (fermionMultiCreation N i * fermionMultiCreation N j)
        = (fermionTotalNumber N * fermionMultiCreation N i) *
            fermionMultiCreation N j := by rw [← Matrix.mul_assoc]
      _ = (fermionMultiCreation N i * fermionTotalNumber N +
            fermionMultiCreation N i) * fermionMultiCreation N j := by
            rw [h₁]
      _ = fermionMultiCreation N i * fermionTotalNumber N *
            fermionMultiCreation N j +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.add_mul]
      _ = fermionMultiCreation N i *
            (fermionTotalNumber N * fermionMultiCreation N j) +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.mul_assoc]
      _ = fermionMultiCreation N i *
            (fermionMultiCreation N j * fermionTotalNumber N +
              fermionMultiCreation N j) +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [h₂]
      _ = fermionMultiCreation N i *
            (fermionMultiCreation N j * fermionTotalNumber N) +
          fermionMultiCreation N i * fermionMultiCreation N j +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.mul_add]
      _ = fermionMultiCreation N i * fermionMultiCreation N j *
            fermionTotalNumber N +
          (fermionMultiCreation N i * fermionMultiCreation N j +
            fermionMultiCreation N i * fermionMultiCreation N j) := by
            rw [← Matrix.mul_assoc]; abel
      _ = fermionMultiCreation N i * fermionMultiCreation N j *
            fermionTotalNumber N +
          (2 : ℂ) •
            (fermionMultiCreation N i * fermionMultiCreation N j) := by
            rw [two_smul]
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalNumber_mulVec_vacuum, Matrix.mulVec_zero, zero_add,
    Matrix.smul_mulVec]

/-! ## Hubbard Gibbs state on a graph -/

/-- Gibbs state of the graph-built Hubbard Hamiltonian. -/
noncomputable def hubbardGibbsStateOnGraph (N : ℕ) (β : ℝ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardHamiltonianOnGraph N G J U)

/-- Hermiticity of the graph-built Hubbard Gibbs state. -/
theorem hubbardGibbsStateOnGraph_isHermitian
    (N : ℕ) (β : ℝ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J U : ℂ} (hJ : star J = J) (hU : star U = U) :
    (hubbardGibbsStateOnGraph N β G J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardHamiltonianOnGraph_isHermitian N G hJ hU) β

/-- The graph-built Hubbard Gibbs state commutes with its Hamiltonian. -/
theorem hubbardGibbsStateOnGraph_commute_hamiltonian
    (N : ℕ) (β : ℝ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    Commute (hubbardGibbsStateOnGraph N β G J U)
      (hubbardHamiltonianOnGraph N G J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-- Bridge: `hubbardChainGibbsState` = `hubbardGibbsStateOnGraph`
on `pathGraph (N+1)` with weight `-J`. -/
theorem hubbardChainGibbsState_eq_onGraph (N : ℕ) (β : ℝ) (J U : ℝ) :
    hubbardChainGibbsState N β J U
      = hubbardGibbsStateOnGraph N β (SimpleGraph.pathGraph (N + 1))
          (-(J : ℂ)) (U : ℂ) :=
  rfl

/-! ## Periodic 1D Hubbard chain (cycleGraph instance) -/

/-- The canonical 1D periodic Hubbard ring on `N + 1` spinful sites,
defined via `hubbardHamiltonianOnGraph` with the cycle graph on
`N + 1` vertices. -/
noncomputable def hubbardCycleHamiltonian (N : ℕ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N (SimpleGraph.cycleGraph (N + 1))
    (-(J : ℂ)) (U : ℂ)

/-- Hermiticity of the periodic Hubbard chain. -/
theorem hubbardCycleHamiltonian_isHermitian (N : ℕ) (J U : ℝ) :
    (hubbardCycleHamiltonian N J U).IsHermitian :=
  hubbardHamiltonianOnGraph_isHermitian N _ (by simp) (by simp)

/-- Charge conservation for the periodic Hubbard chain. -/
theorem hubbardCycleHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (J U : ℝ) :
    Commute (hubbardCycleHamiltonian N J U)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardHamiltonianOnGraph_commute_fermionTotalNumber N _ _ _

/-- Gibbs state of the periodic Hubbard chain. -/
noncomputable def hubbardCycleGibbsState (N : ℕ) (β : ℝ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardCycleHamiltonian N J U)

/-- Hermiticity of the periodic Hubbard Gibbs state. -/
theorem hubbardCycleGibbsState_isHermitian (N : ℕ) (β : ℝ) (J U : ℝ) :
    (hubbardCycleGibbsState N β J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) β

end LatticeSystem.Fermion
