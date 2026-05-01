/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin

/-!
# Sublattice spin operators for the MLM toy Hamiltonian

To establish the Casimir identity for the toy Hamiltonian
(Tasaki §2.5 eq. (2.5.11)),

  `Ĥ_toy = (1/(2|Λ|)) ((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)`,

we need the **sublattice spin operators** for `α ∈ {1, 2, 3}`:

  `Ŝ_A^(α) := Σ_{x ∈ A} Ŝ_x^(α)`,
  `Ŝ_B^(α) := Σ_{x ∈ ¬A} Ŝ_x^(α)`,

where the sums are over the sublattice indicators `A : Λ → Bool`.
The total spin then decomposes as
`Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_B^(α)`.

This module defines the sublattice operators and proves the basic
decomposition `Ŝ_tot = Ŝ_A + Ŝ_B`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Sublattice spin operators -/

/-- The sublattice-`A` total spin (axis 1):
`Ŝ_A^(1) := Σ_{x ∈ A} onSite x Ŝ^(1)`. -/
noncomputable def sublatticeSpinHalfOp1 (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOp1 else 0

/-- The sublattice-`A` total spin (axis 2):
`Ŝ_A^(2) := Σ_{x ∈ A} onSite x Ŝ^(2)`. -/
noncomputable def sublatticeSpinHalfOp2 (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOp2 else 0

/-- The sublattice-`A` total spin (axis 3):
`Ŝ_A^(3) := Σ_{x ∈ A} onSite x Ŝ^(3)`. -/
noncomputable def sublatticeSpinHalfOp3 (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOp3 else 0

/-! ## Decomposition of the total spin into sublattices -/

/-- The total spin (axis 1) decomposes as a sum over the two
sublattices: `Ŝ_tot^(1) = Ŝ_A^(1) + Ŝ_¬A^(1)`. -/
theorem totalSpinHalfOp1_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOp1 Λ =
      sublatticeSpinHalfOp1 A + sublatticeSpinHalfOp1 (fun x => ! A x) := by
  unfold totalSpinHalfOp1 sublatticeSpinHalfOp1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin (axis 2) decomposes as a sum over the two
sublattices. -/
theorem totalSpinHalfOp2_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOp2 Λ =
      sublatticeSpinHalfOp2 A + sublatticeSpinHalfOp2 (fun x => ! A x) := by
  unfold totalSpinHalfOp2 sublatticeSpinHalfOp2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin (axis 3) decomposes as a sum over the two
sublattices. -/
theorem totalSpinHalfOp3_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOp3 Λ =
      sublatticeSpinHalfOp3 A + sublatticeSpinHalfOp3 (fun x => ! A x) := by
  unfold totalSpinHalfOp3 sublatticeSpinHalfOp3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-! ## Hermiticity -/

/-- Each sublattice spin operator is Hermitian.
Sum of Hermitian operators is Hermitian. -/
theorem sublatticeSpinHalfOp1_isHermitian (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 A).IsHermitian := by
  unfold sublatticeSpinHalfOp1
  refine Finset.sum_induction _ _ (fun a b => Matrix.IsHermitian.add) Matrix.isHermitian_zero ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_isHermitian x spinHalfOp1_isHermitian
  · cases h : A x
    · rw [if_neg]
      · simp [Matrix.IsHermitian]
      · simp [h]
    · exact absurd h hA

/-- `Ŝ_A^(2)` is Hermitian. -/
theorem sublatticeSpinHalfOp2_isHermitian (A : Λ → Bool) :
    (sublatticeSpinHalfOp2 A).IsHermitian := by
  unfold sublatticeSpinHalfOp2
  refine Finset.sum_induction _ _ (fun a b => Matrix.IsHermitian.add) Matrix.isHermitian_zero ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_isHermitian x spinHalfOp2_isHermitian
  · cases h : A x
    · rw [if_neg]
      · simp [Matrix.IsHermitian]
      · simp [h]
    · exact absurd h hA

/-- `Ŝ_A^(3)` is Hermitian. -/
theorem sublatticeSpinHalfOp3_isHermitian (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A).IsHermitian := by
  unfold sublatticeSpinHalfOp3
  refine Finset.sum_induction _ _ (fun a b => Matrix.IsHermitian.add) Matrix.isHermitian_zero ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_isHermitian x spinHalfOp3_isHermitian
  · cases h : A x
    · rw [if_neg]
      · simp [Matrix.IsHermitian]
      · simp [h]
    · exact absurd h hA

/-! ## Cross-sublattice commutativity (axis 1)

The sublattice-`A` and sublattice-`¬A` operators commute pairwise:
each pair `(onSite x σ_α)`, `(onSite y σ_α)` for `x ∈ A`, `y ∉ A`
has `x ≠ y` (since `A x = true ≠ false = A y`), so the site-embedded
operators commute (`onSite_mul_onSite_of_ne`).

This is the key combinatorial fact for the Casimir identity
`(Ŝ_tot^(α))² = (Ŝ_A^(α))² + 2 Ŝ_A^(α) Ŝ_¬A^(α) + (Ŝ_¬A^(α))²`. -/

/-- Cross-sublattice commutativity (axis 1):
`Ŝ_A^(1)` and `Ŝ_¬A^(1)` commute. -/
theorem sublatticeSpinHalfOp1_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp1 A) (sublatticeSpinHalfOp1 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp1
  refine Commute.sum_left _ _ _ fun x _ => ?_
  refine Commute.sum_right _ _ _ fun y _ => ?_
  -- Case-split on `A x` and `A y` (not `!A y`).
  by_cases hAx : A x = true
  · by_cases hAy : A y = true
    · -- A x = true, A y = true.  `(fun z => !A z) y = !true = false`, so the y term is 0.
      rw [show (fun z : Λ => ! A z) y = false from by simp [hAy]]
      simp
    · -- A x = true, A y = false. y term: `onSite y σ1`.
      have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      rw [show (fun z : Λ => ! A z) y = true from by simp [hAy']]
      have hxy : x ≠ y := fun heq => by
        subst heq; rw [hAx] at hAy'; exact Bool.noConfusion hAy'
      rw [if_pos hAx, if_pos rfl]
      exact onSite_mul_onSite_of_ne hxy spinHalfOp1 spinHalfOp1
  · rw [if_neg hAx]; exact Commute.zero_left _

end LatticeSystem.Quantum
