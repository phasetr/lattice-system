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

/-! ## Vector spin squared `(Ŝ_A)²` -/

/-- The sublattice-`A` total spin squared (Casimir):
`(Ŝ_A)² := Σ_{α=1,2,3} (Ŝ_A^(α))²`. -/
noncomputable def sublatticeSpinHalfSquared (A : Λ → Bool) : ManyBodyOp Λ :=
  sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
    sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A +
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 A

/-- `(Ŝ_A)² = Σ_α (Ŝ_A^(α))²` is the explicit definition. -/
@[simp] theorem sublatticeSpinHalfSquared_def (A : Λ → Bool) :
    sublatticeSpinHalfSquared A =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A +
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 A := rfl

/-- `(Ŝ_A)²` is Hermitian.  Each `(Ŝ_A^(α))²` is Hermitian as the
product of a self-commuting Hermitian operator with itself; the sum
of Hermitian operators is Hermitian. -/
theorem sublatticeSpinHalfSquared_isHermitian (A : Λ → Bool) :
    (sublatticeSpinHalfSquared A).IsHermitian := by
  unfold sublatticeSpinHalfSquared
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinHalfOp1_isHermitian A) (sublatticeSpinHalfOp1_isHermitian A) rfl
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinHalfOp2_isHermitian A) (sublatticeSpinHalfOp2_isHermitian A) rfl
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinHalfOp3_isHermitian A) (sublatticeSpinHalfOp3_isHermitian A) rfl

/-! ## Cross-sublattice commutativity

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

/-- Cross-sublattice commutativity (axis 2):
`Ŝ_A^(2)` and `Ŝ_¬A^(2)` commute. -/
theorem sublatticeSpinHalfOp2_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp2 A) (sublatticeSpinHalfOp2 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp2
  refine Commute.sum_left _ _ _ fun x _ => ?_
  refine Commute.sum_right _ _ _ fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hAy : A y = true
    · rw [show (fun z : Λ => ! A z) y = false from by simp [hAy]]
      simp
    · -- A x = true, A y = false. y term: `onSite y σ2`.
      have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      rw [show (fun z : Λ => ! A z) y = true from by simp [hAy']]
      have hxy : x ≠ y := fun heq => by
        subst heq; rw [hAx] at hAy'; exact Bool.noConfusion hAy'
      rw [if_pos hAx, if_pos rfl]
      exact onSite_mul_onSite_of_ne hxy spinHalfOp2 spinHalfOp2
  · rw [if_neg hAx]; exact Commute.zero_left _

/-- Cross-sublattice commutativity (axis 3):
`Ŝ_A^(3)` and `Ŝ_¬A^(3)` commute. -/
theorem sublatticeSpinHalfOp3_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp3 A) (sublatticeSpinHalfOp3 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp3
  refine Commute.sum_left _ _ _ fun x _ => ?_
  refine Commute.sum_right _ _ _ fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hAy : A y = true
    · rw [show (fun z : Λ => ! A z) y = false from by simp [hAy]]
      simp
    · have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      rw [show (fun z : Λ => ! A z) y = true from by simp [hAy']]
      have hxy : x ≠ y := fun heq => by
        subst heq; rw [hAx] at hAy'; exact Bool.noConfusion hAy'
      rw [if_pos hAx, if_pos rfl]
      exact onSite_mul_onSite_of_ne hxy spinHalfOp3 spinHalfOp3
  · rw [if_neg hAx]; exact Commute.zero_left _

/-! ## Generic mixed-axes cross-sublattice commutativity

Sites in `A` and sites in `¬A` are necessarily distinct, so any
single-site operators embedded at those sites commute via
`onSite_mul_onSite_of_ne`. Lifted to the sublattice sums, this gives
that `Ŝ_A^(α)` and `Ŝ_¬A^(β)` commute for **any** axes `α, β`
— the existing `_cross_commute` lemmas are the diagonal case `α = β`.

This generic form is needed when expanding `(Ŝ_A)² · Ŝ_¬A^(α)` etc.,
which mix axes `1, 2, 3` in the Casimir-eigenvalue analysis. -/

/-- Generic helper: the `A`-sublattice sum of `onSite x S` commutes
with the `¬A`-sublattice sum of `onSite y T` for **any** single-site
operators `S, T`. Each cross-pair has `x ∈ A`, `y ∉ A`, so `x ≠ y`. -/
theorem sublatticeSpinHalfOpGeneric_cross_commute
    (A : Λ → Bool) (S T : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute
      (∑ x : Λ, if A x then onSite x S else 0)
      (∑ y : Λ, if (! A y) then onSite y T else 0) := by
  refine Commute.sum_left _ _ _ fun x _ => ?_
  refine Commute.sum_right _ _ _ fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hAy : A y = true
    · rw [show (! A y) = false from by simp [hAy]]
      simp
    · have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      rw [show (! A y) = true from by simp [hAy']]
      have hxy : x ≠ y := fun heq => by
        subst heq; rw [hAx] at hAy'; exact Bool.noConfusion hAy'
      rw [if_pos hAx, if_pos rfl]
      exact onSite_mul_onSite_of_ne hxy S T
  · rw [if_neg hAx]; exact Commute.zero_left _

/-- Mixed-axes cross-sublattice commutativity:
`Ŝ_A^(1)` commutes with `Ŝ_¬A^(2)`. -/
theorem sublatticeSpinHalfOp1_cross_commute_op2 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp1 A) (sublatticeSpinHalfOp2 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp1 sublatticeSpinHalfOp2
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOp1 spinHalfOp2

/-- Mixed-axes cross-sublattice commutativity:
`Ŝ_A^(1)` commutes with `Ŝ_¬A^(3)`. -/
theorem sublatticeSpinHalfOp1_cross_commute_op3 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp1 A) (sublatticeSpinHalfOp3 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp1 sublatticeSpinHalfOp3
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOp1 spinHalfOp3

/-- Mixed-axes cross-sublattice commutativity:
`Ŝ_A^(2)` commutes with `Ŝ_¬A^(1)`. -/
theorem sublatticeSpinHalfOp2_cross_commute_op1 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp2 A) (sublatticeSpinHalfOp1 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp2 sublatticeSpinHalfOp1
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOp2 spinHalfOp1

/-- Mixed-axes cross-sublattice commutativity:
`Ŝ_A^(2)` commutes with `Ŝ_¬A^(3)`. -/
theorem sublatticeSpinHalfOp2_cross_commute_op3 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp2 A) (sublatticeSpinHalfOp3 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp2 sublatticeSpinHalfOp3
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOp2 spinHalfOp3

/-- Mixed-axes cross-sublattice commutativity:
`Ŝ_A^(3)` commutes with `Ŝ_¬A^(1)`. -/
theorem sublatticeSpinHalfOp3_cross_commute_op1 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp3 A) (sublatticeSpinHalfOp1 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp3 sublatticeSpinHalfOp1
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOp3 spinHalfOp1

/-- Mixed-axes cross-sublattice commutativity:
`Ŝ_A^(3)` commutes with `Ŝ_¬A^(2)`. -/
theorem sublatticeSpinHalfOp3_cross_commute_op2 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOp3 A) (sublatticeSpinHalfOp2 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOp3 sublatticeSpinHalfOp2
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOp3 spinHalfOp2

/-! ## Inter-Casimir cross-sublattice commutativity -/

/-- The two sublattice Casimirs commute:
`Commute (Ŝ_A)² (Ŝ_¬A)²`. Each pairwise component
`Commute ((Ŝ_A^(α))²) ((Ŝ_¬A^(β))²)` follows from the mixed-axes
cross-commute by chaining `Commute.mul_left` / `Commute.mul_right`.

Used to set up the joint eigenbasis of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²`
for the toy-Hamiltonian eigenvalue analysis. -/
theorem sublatticeSpinHalfSquared_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A)
            (sublatticeSpinHalfSquared (fun x => ! A x)) := by
  unfold sublatticeSpinHalfSquared
  -- Each axis-α square commutes with each axis-β square.
  have hα1β1 := sublatticeSpinHalfOp1_cross_commute A
  have hα1β2 := sublatticeSpinHalfOp1_cross_commute_op2 A
  have hα1β3 := sublatticeSpinHalfOp1_cross_commute_op3 A
  have hα2β1 := sublatticeSpinHalfOp2_cross_commute_op1 A
  have hα2β2 := sublatticeSpinHalfOp2_cross_commute A
  have hα2β3 := sublatticeSpinHalfOp2_cross_commute_op3 A
  have hα3β1 := sublatticeSpinHalfOp3_cross_commute_op1 A
  have hα3β2 := sublatticeSpinHalfOp3_cross_commute_op2 A
  have hα3β3 := sublatticeSpinHalfOp3_cross_commute A
  -- Sum-left: each (Ŝ_A^α)² (= sum) commutes with the product (Ŝ_¬A^β)²
  -- for each β. Then add over α; then add over β.
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · refine Commute.add_right (Commute.add_right ?_ ?_) ?_
    · exact (hα1β1.mul_left hα1β1).mul_right (hα1β1.mul_left hα1β1)
    · exact (hα1β2.mul_left hα1β2).mul_right (hα1β2.mul_left hα1β2)
    · exact (hα1β3.mul_left hα1β3).mul_right (hα1β3.mul_left hα1β3)
  · refine Commute.add_right (Commute.add_right ?_ ?_) ?_
    · exact (hα2β1.mul_left hα2β1).mul_right (hα2β1.mul_left hα2β1)
    · exact (hα2β2.mul_left hα2β2).mul_right (hα2β2.mul_left hα2β2)
    · exact (hα2β3.mul_left hα2β3).mul_right (hα2β3.mul_left hα2β3)
  · refine Commute.add_right (Commute.add_right ?_ ?_) ?_
    · exact (hα3β1.mul_left hα3β1).mul_right (hα3β1.mul_left hα3β1)
    · exact (hα3β2.mul_left hα3β2).mul_right (hα3β2.mul_left hα3β2)
    · exact (hα3β3.mul_left hα3β3).mul_right (hα3β3.mul_left hα3β3)

end LatticeSystem.Quantum
