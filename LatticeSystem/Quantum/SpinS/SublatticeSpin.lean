import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.ManyBody

/-!
# Sublattice spin-`S` operators (Tasaki §2.5 Theorem 2.3 prep)

To establish the Casimir identity used in Tasaki Theorem 2.3
(`|A| ≠ |B|` case),

  `Ĥ_toy = (1/(2|Λ|)) ((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)`,

we need spin-`S` analogues of the **sublattice spin operators**
already defined for spin-`1/2`
(`Quantum/MarshallLiebMattis/SublatticeSpin.lean`):

  `Ŝ_A^(α) := Σ_{x : A x = true} onSiteS x (spinSOp_α N)`,
  `Ŝ_¬A^(α) := Σ_{x : A x = false} onSiteS x (spinSOp_α N)`.

The total spin-`S` then decomposes as
`Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_¬A^(α)`.

This module defines the spin-`S` sublattice operators and the
decomposition. First step in the γ-4 multi-PR effort tracked
under Issue #412.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.3 (p. 42), eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## Sublattice spin-`S` operators -/

/-- The sublattice-`A` total spin-`S` (axis 1):
`Ŝ_A^(1) := Σ_{x : A x} onSiteS x (spinSOp1 N)`. -/
noncomputable def sublatticeSpinSOp1 (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOp1 N) else 0

/-- The sublattice-`A` total spin-`S` (axis 2):
`Ŝ_A^(2) := Σ_{x : A x} onSiteS x (spinSOp2 N)`. -/
noncomputable def sublatticeSpinSOp2 (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOp2 N) else 0

/-- The sublattice-`A` total spin-`S` (axis 3):
`Ŝ_A^(3) := Σ_{x : A x} onSiteS x (spinSOp3 N)`. -/
noncomputable def sublatticeSpinSOp3 (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOp3 N) else 0

/-! ## Decomposition of the total spin into sublattices -/

/-- The total spin-`S` (axis 1) decomposes as a sum over the two
sublattices: `Ŝ_tot^(1) = Ŝ_A^(1) + Ŝ_¬A^(1)`. -/
theorem totalSpinSOp1_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOp1 Λ N =
      sublatticeSpinSOp1 N A + sublatticeSpinSOp1 N (fun x => ! A x) := by
  unfold totalSpinSOp1 sublatticeSpinSOp1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin-`S` (axis 2) decomposes as a sum over the two
sublattices. -/
theorem totalSpinSOp2_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOp2 Λ N =
      sublatticeSpinSOp2 N A + sublatticeSpinSOp2 N (fun x => ! A x) := by
  unfold totalSpinSOp2 sublatticeSpinSOp2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin-`S` (axis 3) decomposes as a sum over the two
sublattices. -/
theorem totalSpinSOp3_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOp3 Λ N =
      sublatticeSpinSOp3 N A + sublatticeSpinSOp3 N (fun x => ! A x) := by
  unfold totalSpinSOp3 sublatticeSpinSOp3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-! ## Hermiticity -/

/-- Each sublattice spin-`S` operator is Hermitian.
Sum of Hermitian operators is Hermitian. -/
theorem sublatticeSpinSOp1_isHermitian (A : Λ → Bool) :
    (sublatticeSpinSOp1 N A).IsHermitian := by
  unfold sublatticeSpinSOp1
  refine Finset.sum_induction _ _ (fun a b => Matrix.IsHermitian.add)
    Matrix.isHermitian_zero ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_isHermitian x (spinSOp1_isHermitian N)
  · cases h : A x
    · rw [if_neg]
      · simp [Matrix.IsHermitian]
      · simp
    · exact absurd h hA

/-- `Ŝ_A^(2)` is Hermitian. -/
theorem sublatticeSpinSOp2_isHermitian (A : Λ → Bool) :
    (sublatticeSpinSOp2 N A).IsHermitian := by
  unfold sublatticeSpinSOp2
  refine Finset.sum_induction _ _ (fun a b => Matrix.IsHermitian.add)
    Matrix.isHermitian_zero ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_isHermitian x (spinSOp2_isHermitian N)
  · cases h : A x
    · rw [if_neg]
      · simp [Matrix.IsHermitian]
      · simp
    · exact absurd h hA

/-- `Ŝ_A^(3)` is Hermitian. -/
theorem sublatticeSpinSOp3_isHermitian (A : Λ → Bool) :
    (sublatticeSpinSOp3 N A).IsHermitian := by
  unfold sublatticeSpinSOp3
  refine Finset.sum_induction _ _ (fun a b => Matrix.IsHermitian.add)
    Matrix.isHermitian_zero ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_isHermitian x (spinSOp3_isHermitian N)
  · cases h : A x
    · rw [if_neg]
      · simp [Matrix.IsHermitian]
      · simp
    · exact absurd h hA

/-! ## Vector spin squared `(Ŝ_A)²` -/

/-- The sublattice-`A` total spin squared (Casimir) for spin-`S`:
`(Ŝ_A)² := Σ_{α=1,2,3} (Ŝ_A^(α))²`. -/
noncomputable def sublatticeSpinSquaredS (A : Λ → Bool) : ManyBodyOpS Λ N :=
  sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A +
    sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A +
    sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A

/-- `(Ŝ_A)² = Σ_α (Ŝ_A^(α))²` is the explicit definition. -/
@[simp] theorem sublatticeSpinSquaredS_def (A : Λ → Bool) :
    sublatticeSpinSquaredS N A =
      sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A +
        sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A := rfl

/-- `(Ŝ_A)²` is Hermitian. Each `(Ŝ_A^(α))²` is Hermitian as the
product of a self-commuting Hermitian operator with itself; the
sum of Hermitian operators is Hermitian. -/
theorem sublatticeSpinSquaredS_isHermitian (A : Λ → Bool) :
    (sublatticeSpinSquaredS N A).IsHermitian := by
  unfold sublatticeSpinSquaredS
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinSOp1_isHermitian N A)
      (sublatticeSpinSOp1_isHermitian N A) rfl
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinSOp2_isHermitian N A)
      (sublatticeSpinSOp2_isHermitian N A) rfl
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinSOp3_isHermitian N A)
      (sublatticeSpinSOp3_isHermitian N A) rfl

/-! ## Cross-sublattice commutativity (same axis)

The sublattice-`A` and sublattice-`¬A` operators commute pairwise:
each pair `(onSiteS x (spinSOp_α N))`, `(onSiteS y (spinSOp_α N))`
for `x ∈ A`, `y ∉ A` has `x ≠ y`, so the site-embedded operators
commute (`onSiteS_commute_of_ne`).
-/

/-- Cross-sublattice commutativity for spin-`S` (axis 1):
`Ŝ_A^(1)` and `Ŝ_¬A^(1)` commute. -/
theorem sublatticeSpinSOp1_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinSOp1 N A)
      (sublatticeSpinSOp1 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp1
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
      exact onSiteS_commute_of_ne hxy (spinSOp1 N) (spinSOp1 N)
  · rw [if_neg hAx]; exact Commute.zero_left _

/-- Cross-sublattice commutativity for spin-`S` (axis 2):
`Ŝ_A^(2)` and `Ŝ_¬A^(2)` commute. -/
theorem sublatticeSpinSOp2_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinSOp2 N A)
      (sublatticeSpinSOp2 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp2
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
      exact onSiteS_commute_of_ne hxy (spinSOp2 N) (spinSOp2 N)
  · rw [if_neg hAx]; exact Commute.zero_left _

/-- Cross-sublattice commutativity for spin-`S` (axis 3):
`Ŝ_A^(3)` and `Ŝ_¬A^(3)` commute. -/
theorem sublatticeSpinSOp3_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinSOp3 N A)
      (sublatticeSpinSOp3 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp3
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
      exact onSiteS_commute_of_ne hxy (spinSOp3 N) (spinSOp3 N)
  · rw [if_neg hAx]; exact Commute.zero_left _

/-! ## Generic mixed-axes cross-sublattice commutativity for spin-`S`

Sites in `A` and `¬A` are distinct, so any single-site operators
embedded at those sites commute via `onSiteS_mul_onSiteS_of_ne`.
Lifted to the sublattice sums, this gives that `Ŝ_A^(α)` and
`Ŝ_¬A^(β)` commute for **any** axes `α, β`. -/

/-- Generic helper: the `A`-sublattice sum of `onSiteS x S`
commutes with the `¬A`-sublattice sum of `onSiteS y T` for
**any** single-site operators `S, T`. -/
theorem sublatticeSpinSOpGeneric_cross_commute
    (A : Λ → Bool) (S T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute
      (∑ x : Λ, if A x then onSiteS x S else 0)
      (∑ y : Λ, if (! A y) then onSiteS y T else 0) := by
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
      exact onSiteS_commute_of_ne hxy S T
  · rw [if_neg hAx]; exact Commute.zero_left _

/-- Mixed-axes cross-sublattice commutativity for spin-`S`:
`Ŝ_A^(1)` commutes with `Ŝ_¬A^(2)`. -/
theorem sublatticeSpinSOp1_cross_commute_op2 (A : Λ → Bool) :
    Commute (sublatticeSpinSOp1 N A) (sublatticeSpinSOp2 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp1 sublatticeSpinSOp2
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOp1 N) (spinSOp2 N)

/-- `Ŝ_A^(1)` commutes with `Ŝ_¬A^(3)`. -/
theorem sublatticeSpinSOp1_cross_commute_op3 (A : Λ → Bool) :
    Commute (sublatticeSpinSOp1 N A) (sublatticeSpinSOp3 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp1 sublatticeSpinSOp3
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOp1 N) (spinSOp3 N)

/-- `Ŝ_A^(2)` commutes with `Ŝ_¬A^(1)`. -/
theorem sublatticeSpinSOp2_cross_commute_op1 (A : Λ → Bool) :
    Commute (sublatticeSpinSOp2 N A) (sublatticeSpinSOp1 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp2 sublatticeSpinSOp1
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOp2 N) (spinSOp1 N)

/-- `Ŝ_A^(2)` commutes with `Ŝ_¬A^(3)`. -/
theorem sublatticeSpinSOp2_cross_commute_op3 (A : Λ → Bool) :
    Commute (sublatticeSpinSOp2 N A) (sublatticeSpinSOp3 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp2 sublatticeSpinSOp3
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOp2 N) (spinSOp3 N)

/-- `Ŝ_A^(3)` commutes with `Ŝ_¬A^(1)`. -/
theorem sublatticeSpinSOp3_cross_commute_op1 (A : Λ → Bool) :
    Commute (sublatticeSpinSOp3 N A) (sublatticeSpinSOp1 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp3 sublatticeSpinSOp1
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOp3 N) (spinSOp1 N)

/-- `Ŝ_A^(3)` commutes with `Ŝ_¬A^(2)`. -/
theorem sublatticeSpinSOp3_cross_commute_op2 (A : Λ → Bool) :
    Commute (sublatticeSpinSOp3 N A) (sublatticeSpinSOp2 N (fun x => ! A x)) := by
  unfold sublatticeSpinSOp3 sublatticeSpinSOp2
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOp3 N) (spinSOp2 N)

end LatticeSystem.Quantum
