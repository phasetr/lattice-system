/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Multi-body operator space and site-embedded operators

This module introduces the operator space on the many-body spin-1/2 Hilbert
space of an `N`-site lattice, represented as matrices indexed by
configurations `Fin N → Fin 2`.

The principal construction is the site-embedded operator

```
onSite i A : ManyBodyOp N
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

variable {N : ℕ}

/-- The operator space on the `N`-site spin-1/2 many-body Hilbert space,
represented as matrices indexed by computational-basis configurations
`σ : Fin N → Fin 2`. -/
abbrev ManyBodyOp (N : ℕ) : Type :=
  Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ

/-- The site-embedded operator `onSite i A` acts as `A` on site `i` and as
the identity on every other site. Its matrix element is `A (σ' i) (σ i)`
when `σ'` and `σ` agree at every site other than `i`, and `0` otherwise. -/
def onSite (i : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ) : ManyBodyOp N :=
  fun σ' σ => if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0

/-- Unfolding the matrix element of `onSite i A`. -/
theorem onSite_apply (i : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (σ' σ : Fin N → Fin 2) :
    onSite i A σ' σ =
      if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0 := rfl

/-! ## Hermiticity preservation -/

/-- If `A` is Hermitian, so is its site embedding `onSite i A`. -/
theorem onSite_isHermitian (i : Fin N) {A : Matrix (Fin 2) (Fin 2) ℂ}
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
private def pivotLeft (σ' σ : Fin N → Fin 2) (j : Fin N) : Fin N → Fin 2 :=
  Function.update σ j (σ' j)

private lemma pivotLeft_at_i_of_ne {i j : Fin N} (hij : i ≠ j)
    (σ' σ : Fin N → Fin 2) : pivotLeft σ' σ j i = σ i := by
  rw [pivotLeft, Function.update_of_ne hij]

private lemma pivotLeft_at_j (σ' σ : Fin N → Fin 2) (j : Fin N) :
    pivotLeft σ' σ j j = σ' j := by
  rw [pivotLeft, Function.update_self]

private lemma pivotLeft_off_j {j k : Fin N} (hk : k ≠ j)
    (σ' σ : Fin N → Fin 2) :
    pivotLeft σ' σ j k = σ k := by
  rw [pivotLeft, Function.update_of_ne hk]

private lemma onSite_mul_onSite_apply_of_ne_aux {i j : Fin N} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (σ' σ : Fin N → Fin 2) :
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

private lemma onSite_mul_onSite_value_of_agree {i j : Fin N} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) {σ' σ : Fin N → Fin 2}
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

private lemma onSite_mul_onSite_value_of_disagree {i j : Fin N}
    (A B : Matrix (Fin 2) (Fin 2) ℂ) {σ' σ : Fin N → Fin 2}
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
private lemma onSite_mul_onSite_apply_of_ne {i j : Fin N} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (σ' σ : Fin N → Fin 2) :
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
theorem onSite_mul_onSite_of_ne {i j : Fin N} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite i A * onSite j B = onSite j B * onSite i A := by
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

end LatticeSystem.Quantum
