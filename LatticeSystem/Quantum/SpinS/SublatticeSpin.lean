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

end LatticeSystem.Quantum
