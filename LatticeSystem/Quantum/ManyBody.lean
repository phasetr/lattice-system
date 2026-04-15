/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Multi-body operator space and site-embedded operators

This module introduces the operator space on the many-body spin-1/2 Hilbert
space of an arbitrary finite lattice `Λ`, represented as matrices indexed
by configurations `Λ → Fin 2`. Following Tasaki *Physics and Mathematics
of Quantum Many-Body Systems*, §2.2, p. 21, the lattice is any finite set
`Λ` with decidable equality; specializing to `Λ = Fin N` recovers an
`N`-site chain.

The principal construction is the site-embedded operator

```
onSite i A : ManyBodyOp Λ
```

which acts as a single-site operator `A : Matrix (Fin 2) (Fin 2) ℂ` on site
`i` and as the identity on every other site. We prove:

* `onSite_isHermitian` — Hermiticity lifts from the single-site operator to
  its site embedding.
* `onSite_mul_onSite_of_ne` — operators embedded at distinct sites commute.
* `IsHermitian.mul_of_commute` — a small helper showing that the product
  of two commuting Hermitian matrices is Hermitian.

Together these are the ingredients needed to state and prove self-adjointness
of genuine many-body Hamiltonians such as the quantum Ising chain.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The operator space on the spin-1/2 many-body Hilbert space indexed by
the lattice `Λ`, represented as matrices indexed by computational-basis
configurations `σ : Λ → Fin 2`. -/
abbrev ManyBodyOp (Λ : Type*) : Type _ :=
  Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ

/-- The site-embedded operator `onSite i A` acts as `A` on site `i` and as
the identity on every other site. Its matrix element is `A (σ' i) (σ i)`
when `σ'` and `σ` agree at every site other than `i`, and `0` otherwise. -/
def onSite (i : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ManyBodyOp Λ :=
  fun σ' σ => if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0

/-- Unfolding the matrix element of `onSite i A`. -/
theorem onSite_apply (i : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (σ' σ : Λ → Fin 2) :
    onSite i A σ' σ =
      if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0 := rfl

/-! ## Hermiticity preservation -/

/-- If `A` is Hermitian, so is its site embedding `onSite i A`. -/
theorem onSite_isHermitian (i : Λ) {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) : (onSite i A).IsHermitian := by
  ext σ σ'
  simp only [Matrix.conjTranspose_apply, onSite_apply]
  by_cases h : ∀ k, k ≠ i → σ k = σ' k
  · have h' : ∀ k, k ≠ i → σ' k = σ k := fun k hki => (h k hki).symm
    rw [if_pos h', if_pos h]
    exact hA.apply (σ i) (σ' i)
  · have h' : ¬ (∀ k, k ≠ i → σ' k = σ k) := by
      intro hp
      exact h (fun k hki => (hp k hki).symm)
    rw [if_neg h', if_neg h, star_zero]

/-! ## Commutativity at distinct sites -/

/-- The unique configuration `τ` that contributes to
`(onSite i A * onSite j B) σ' σ` as a function of `σ'`, `σ`, `j`: on site
`j` it takes the value `σ' j`, and elsewhere it equals `σ`. -/
private def pivotLeft (σ' σ : Λ → Fin 2) (j : Λ) : Λ → Fin 2 :=
  Function.update σ j (σ' j)

omit [Fintype Λ] in
private lemma pivotLeft_at_i_of_ne {i j : Λ} (hij : i ≠ j)
    (σ' σ : Λ → Fin 2) : pivotLeft σ' σ j i = σ i := by
  rw [pivotLeft, Function.update_of_ne hij]

omit [Fintype Λ] in
private lemma pivotLeft_at_j (σ' σ : Λ → Fin 2) (j : Λ) :
    pivotLeft σ' σ j j = σ' j := by
  rw [pivotLeft, Function.update_self]

omit [Fintype Λ] in
private lemma pivotLeft_off_j {j k : Λ} (hk : k ≠ j)
    (σ' σ : Λ → Fin 2) :
    pivotLeft σ' σ j k = σ k := by
  rw [pivotLeft, Function.update_of_ne hk]

private lemma onSite_mul_onSite_apply_of_ne_aux {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (σ' σ : Λ → Fin 2) :
    (onSite i A * onSite j B) σ' σ =
      onSite i A σ' (pivotLeft σ' σ j) * onSite j B (pivotLeft σ' σ j) σ := by
  rw [Matrix.mul_apply]
  apply Fintype.sum_eq_single
  intro τ hτ
  simp only [onSite_apply]
  by_cases hτj : τ j = σ' j
  · -- τ agrees with the pivot at site j, so the disagreement sits somewhere
    -- off j; hence the second factor's agreement condition fails.
    have : ¬ (∀ k, k ≠ j → τ k = σ k) := by
      intro hall
      apply hτ
      funext k
      by_cases hkj : k = j
      · subst hkj
        rw [pivotLeft_at_j]
        exact hτj
      · rw [pivotLeft_off_j hkj]
        exact hall k hkj
    rw [if_neg this, mul_zero]
  · -- τ disagrees with σ' at site j, and since j ≠ i the first factor's
    -- agreement condition fails at k = j.
    have hnotall : ¬ (∀ k, k ≠ i → σ' k = τ k) := by
      intro hall
      exact hτj (hall j hij.symm).symm
    rw [if_neg hnotall, zero_mul]

private lemma onSite_mul_onSite_value_of_agree {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) {σ' σ : Λ → Fin 2}
    (hagree : ∀ k, k ≠ i → k ≠ j → σ' k = σ k) :
    onSite i A σ' (pivotLeft σ' σ j) * onSite j B (pivotLeft σ' σ j) σ =
      A (σ' i) (σ i) * B (σ' j) (σ j) := by
  simp only [onSite_apply]
  rw [if_pos, if_pos]
  · rw [pivotLeft_at_i_of_ne hij, pivotLeft_at_j]
  · intro k hkj
    exact pivotLeft_off_j hkj σ' σ
  · intro k hki
    by_cases hkj : k = j
    · rw [hkj, pivotLeft_at_j]
    · rw [pivotLeft_off_j hkj]
      exact hagree k hki hkj

private lemma onSite_mul_onSite_value_of_disagree {i j : Λ}
    (A B : Matrix (Fin 2) (Fin 2) ℂ) {σ' σ : Λ → Fin 2}
    (hdis : ¬ ∀ k, k ≠ i → k ≠ j → σ' k = σ k) :
    onSite i A σ' (pivotLeft σ' σ j) * onSite j B (pivotLeft σ' σ j) σ = 0 := by
  simp only [onSite_apply]
  rw [if_neg]
  · exact zero_mul _
  · intro hall
    apply hdis
    intro k hki hkj
    have := hall k hki
    rwa [pivotLeft_off_j hkj] at this

/-- The matrix element `(onSite i A * onSite j B) σ' σ` when `i ≠ j`. -/
private lemma onSite_mul_onSite_apply_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (σ' σ : Λ → Fin 2) :
    (onSite i A * onSite j B) σ' σ =
      if ∀ k, k ≠ i → k ≠ j → σ' k = σ k then
        A (σ' i) (σ i) * B (σ' j) (σ j)
      else 0 := by
  rw [onSite_mul_onSite_apply_of_ne_aux hij]
  by_cases h : ∀ k, k ≠ i → k ≠ j → σ' k = σ k
  · rw [if_pos h]
    exact onSite_mul_onSite_value_of_agree hij A B h
  · rw [if_neg h]
    exact onSite_mul_onSite_value_of_disagree A B h

/-- Operators embedded at distinct sites commute. -/
theorem onSite_mul_onSite_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i A * onSite j B : ManyBodyOp Λ) = onSite j B * onSite i A := by
  ext σ' σ
  rw [onSite_mul_onSite_apply_of_ne hij, onSite_mul_onSite_apply_of_ne hij.symm]
  have hcond :
      (∀ k, k ≠ i → k ≠ j → σ' k = σ k) ↔
        (∀ k, k ≠ j → k ≠ i → σ' k = σ k) := by
    constructor <;> intro h k hki hkj <;> exact h k hkj hki
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rfl

/-! ## Products of commuting Hermitian matrices -/

/-- The product of two commuting Hermitian matrices is Hermitian. -/
theorem Matrix.IsHermitian.mul_of_commute {n : Type*} [Fintype n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hcomm : A * B = B * A) : (A * B).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, hA, hB, hcomm]

/-! ## Linearity of the site embedding -/

/-- `onSite` is additive in the operator argument. -/
theorem onSite_add (i : Λ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i (A + B) : ManyBodyOp Λ) = onSite i A + onSite i B := by
  ext σ' σ
  simp only [onSite_apply, Matrix.add_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · simp [if_pos h]
  · simp [if_neg h]

/-- `onSite` takes subtraction of operators to subtraction of embeddings. -/
theorem onSite_sub (i : Λ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i (A - B) : ManyBodyOp Λ) = onSite i A - onSite i B := by
  ext σ' σ
  simp only [onSite_apply, Matrix.sub_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · simp [if_pos h]
  · simp [if_neg h]

/-- `onSite i 0 = 0`. -/
theorem onSite_zero (i : Λ) :
    (onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ) : ManyBodyOp Λ) = 0 := by
  ext σ' σ
  simp only [onSite_apply, Matrix.zero_apply]
  split_ifs <;> rfl

/-- `onSite i 1 = 1`: the site embedding of the 2×2 identity is the
many-body identity. -/
theorem onSite_one (i : Λ) :
    (onSite i (1 : Matrix (Fin 2) (Fin 2) ℂ) : ManyBodyOp Λ) = 1 := by
  ext σ' σ
  simp only [onSite_apply, Matrix.one_apply]
  by_cases heq : σ' = σ
  · subst heq
    simp
  · have : ¬ (∀ k, k ≠ i → σ' k = σ k) ∨ σ' i ≠ σ i := by
      by_contra hall
      push Not at hall
      obtain ⟨hoff, hi⟩ := hall
      apply heq
      funext k
      by_cases hki : k = i
      · subst hki; exact hi
      · exact hoff k hki
    rcases this with h | h
    · rw [if_neg h, if_neg heq]
    · by_cases hagree : ∀ k, k ≠ i → σ' k = σ k
      · rw [if_pos hagree, if_neg h, if_neg heq]
      · rw [if_neg hagree, if_neg heq]

/-- `onSite` commutes with scalar multiplication. -/
theorem onSite_smul (i : Λ) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i (c • A) : ManyBodyOp Λ) = c • onSite i A := by
  ext σ' σ
  simp only [onSite_apply, Matrix.smul_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · simp [if_pos h]
  · simp [if_neg h]

/-! ## Same-site multiplication (Tasaki eq (2.2.6), `x = y` case)

For `onSite i A * onSite i B` (two operators embedded at the *same* site),
the product is the site embedding of the Fin 2 matrix product `A * B`.
This is the diagonal (`x = y`) case of Tasaki eq. (2.2.6), whose
off-diagonal (`x ≠ y`) case is `onSite_mul_onSite_of_ne`.
-/

/-- The pivot used in the same-site product: the unique `τ` (as a function
of `τi ∈ Fin 2`) that agrees with `σ` off site `i` and takes value `τi`
at site `i`. -/
private def fiberUpdate (σ : Λ → Fin 2) (i : Λ) (t : Fin 2) : Λ → Fin 2 :=
  Function.update σ i t

omit [Fintype Λ] in
private lemma fiberUpdate_at (σ : Λ → Fin 2) (i : Λ) (t : Fin 2) :
    fiberUpdate σ i t i = t := by
  rw [fiberUpdate, Function.update_self]

omit [Fintype Λ] in
private lemma fiberUpdate_off {σ : Λ → Fin 2} {i k : Λ} (hk : k ≠ i) (t : Fin 2) :
    fiberUpdate σ i t k = σ k := by
  rw [fiberUpdate, Function.update_of_ne hk]

/-- Same-site product reduces to the site embedding of the 2×2 product. -/
theorem onSite_mul_onSite_same (i : Λ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i A * onSite i B : ManyBodyOp Λ) = onSite i (A * B) := by
  ext σ' σ
  rw [Matrix.mul_apply]
  simp only [onSite_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · rw [if_pos h, Matrix.mul_apply]
    -- First, rewrite each τ-term to be nonzero only when τ = fiberUpdate σ i (τ i).
    have hterm : ∀ τ : Λ → Fin 2,
        (if ∀ k, k ≠ i → σ' k = τ k then A (σ' i) (τ i) else 0) *
            (if ∀ k, k ≠ i → τ k = σ k then B (τ i) (σ i) else 0) =
          if τ = fiberUpdate σ i (τ i) then
            A (σ' i) (τ i) * B (τ i) (σ i)
          else 0 := by
      intro τ
      by_cases hτ : τ = fiberUpdate σ i (τ i)
      · have hoff_σ : ∀ k, k ≠ i → τ k = σ k := by
          intro k hk
          have hstep : τ k = fiberUpdate σ i (τ i) k := congrFun hτ k
          rw [hstep, fiberUpdate_off hk]
        have hoff_σ' : ∀ k, k ≠ i → σ' k = τ k := fun k hk =>
          (h k hk).trans (hoff_σ k hk).symm
        rw [if_pos hoff_σ', if_pos hoff_σ, if_pos hτ]
      · have hnot : ¬ ∀ k, k ≠ i → τ k = σ k := by
          intro hall
          apply hτ
          funext k
          by_cases hki : k = i
          · subst hki; rw [fiberUpdate_at]
          · rw [fiberUpdate_off hki]; exact hall k hki
        rw [if_neg hnot, mul_zero, if_neg hτ]
    rw [Finset.sum_congr rfl (fun τ _ => hterm τ)]
    -- Convert the ite-sum to a filter-sum.
    rw [← Finset.sum_filter]
    -- Reindex the filter-sum over Fin 2 via t ↦ fiberUpdate σ i t.
    symm
    refine Finset.sum_bij (fun (t : Fin 2) _ => fiberUpdate σ i t)
      ?memImage ?inj ?surj ?eq
    case memImage =>
      intro t _
      simp only
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      funext k
      by_cases hki : k = i
      · subst hki
        rw [fiberUpdate_at, fiberUpdate_at]
      · rw [fiberUpdate_off hki, fiberUpdate_off hki]
    case inj =>
      intros s _ u _ hsu
      simp only at hsu
      have := congrFun hsu i
      simpa [fiberUpdate_at] using this
    case surj =>
      intros τ hτ
      rw [Finset.mem_filter] at hτ
      refine ⟨τ i, Finset.mem_univ _, ?_⟩
      simp only
      exact hτ.2.symm
    case eq =>
      intro t _
      simp only
      rw [fiberUpdate_at]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases h1 : ∀ k, k ≠ i → σ' k = τ k
    · have h2 : ¬ ∀ k, k ≠ i → τ k = σ k := by
        intro hh
        exact h (fun k hk => (h1 k hk).trans (hh k hk))
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- Same-site commutator: `[onSite i A, onSite i B] = onSite i [A, B]`.
Specialized to Pauli-basis spin operators, this is the diagonal (`x = y`)
case of Tasaki eq. (2.2.6). -/
theorem onSite_commutator_same (i : Λ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i A * onSite i B - onSite i B * onSite i A : ManyBodyOp Λ) =
      onSite i (A * B - B * A) := by
  rw [onSite_mul_onSite_same, onSite_mul_onSite_same, ← onSite_sub]

end LatticeSystem.Quantum
