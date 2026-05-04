import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Quantum.SpinS.MultiSiteCommutator
import LatticeSystem.Quantum.SpinS.CyclicCommutator
import LatticeSystem.Quantum.SpinS.CyclicCommutator23
import LatticeSystem.Quantum.SpinS.CyclicCommutator31
import LatticeSystem.Quantum.SpinS.AllAlignedState
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

/-! ## Sublattice Casimir cross-commute -/

/-! ## Sublattice SU(2) algebra `[Ŝ_A^α, Ŝ_A^β] = i ε^αβγ Ŝ_A^γ`
(spin-`S`)

For `x ≠ y`, the cross-pair vanishes (`onSiteS_mul_onSiteS_of_ne`);
for `x = y` and `A x = true`, the diagonal contribution gives
`onSiteS x [Sα, Sβ] = i • onSiteS x Sγ`. -/

/-- Generic sublattice-spin commutator (spin-`S`): if
`Sα * Sβ - Sβ * Sα = Complex.I • Sγ` then
`[Σ_x∈A onSiteS x Sα, Σ_x∈A onSiteS x Sβ] =
 i • Σ_x∈A onSiteS x Sγ`. -/
private lemma sublatticeSpinS_commutator_general
    (A : Λ → Bool)
    {Sα Sβ Sγ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hab : Sα * Sβ - Sβ * Sα = Complex.I • Sγ) :
    ((∑ x : Λ, if A x then onSiteS x Sα else 0) *
        (∑ x : Λ, if A x then onSiteS x Sβ else 0) -
      (∑ x : Λ, if A x then onSiteS x Sβ else 0) *
        (∑ x : Λ, if A x then onSiteS x Sα else 0) : ManyBodyOpS Λ N) =
      Complex.I • ∑ x : Λ, if A x then onSiteS x Sγ else 0 := by
  calc (∑ x : Λ, if A x then onSiteS x Sα else 0) *
            (∑ x : Λ, if A x then onSiteS x Sβ else 0) -
          (∑ x : Λ, if A x then onSiteS x Sβ else 0) *
            (∑ x : Λ, if A x then onSiteS x Sα else 0)
      = ∑ x : Λ, ∑ y : Λ,
          ((if A x then onSiteS x Sα else 0) *
              (if A y then onSiteS y Sβ else 0) -
            (if A y then onSiteS y Sβ else 0) *
              (if A x then onSiteS x Sα else 0)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm
          (f := fun y x => (if A y then onSiteS y Sβ else 0) *
              (if A x then onSiteS x Sα else 0))
          (s := Finset.univ) (t := Finset.univ)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Λ, (if A x then Complex.I • onSiteS x Sγ else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · -- diagonal: y = x.
          by_cases hAx : A x = true
          · simp only [if_pos hAx]
            rw [onSiteS_commutator_same, hab, onSiteS_smul]
          · simp only [if_neg hAx, mul_zero, sub_zero]
        · -- off-diagonal: y ≠ x, vanishes.
          intros y _ hyx
          by_cases hAx : A x = true
          · by_cases hAy : A y = true
            · simp only [if_pos hAx, if_pos hAy]
              rw [onSiteS_mul_onSiteS_of_ne hyx.symm]; simp
            · simp only [if_pos hAx, if_neg hAy, mul_zero, zero_mul, sub_zero]
          · simp only [if_neg hAx, mul_zero, zero_mul, sub_zero]
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = Complex.I • ∑ x : Λ, if A x then onSiteS x Sγ else 0 := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hAx : A x = true
        · rw [if_pos hAx, if_pos hAx]
        · rw [if_neg hAx, if_neg hAx, smul_zero]

/-- Sublattice spin-`S` commutator: `[Ŝ_A^(1), Ŝ_A^(2)] = i · Ŝ_A^(3)`. -/
theorem sublatticeSpinSOp1_commutator_sublatticeSpinSOp2 (A : Λ → Bool) :
    (sublatticeSpinSOp1 N A * sublatticeSpinSOp2 N A
        - sublatticeSpinSOp2 N A * sublatticeSpinSOp1 N A : ManyBodyOpS Λ N) =
      Complex.I • sublatticeSpinSOp3 N A := by
  unfold sublatticeSpinSOp1 sublatticeSpinSOp2 sublatticeSpinSOp3
  exact sublatticeSpinS_commutator_general N A (spinSOp1_commutator_spinSOp2 N)

/-- Sublattice spin-`S` commutator: `[Ŝ_A^(2), Ŝ_A^(3)] = i · Ŝ_A^(1)`. -/
theorem sublatticeSpinSOp2_commutator_sublatticeSpinSOp3 (A : Λ → Bool) :
    (sublatticeSpinSOp2 N A * sublatticeSpinSOp3 N A
        - sublatticeSpinSOp3 N A * sublatticeSpinSOp2 N A : ManyBodyOpS Λ N) =
      Complex.I • sublatticeSpinSOp1 N A := by
  unfold sublatticeSpinSOp1 sublatticeSpinSOp2 sublatticeSpinSOp3
  exact sublatticeSpinS_commutator_general N A (spinSOp2_commutator_spinSOp3 N)

/-- Sublattice spin-`S` commutator: `[Ŝ_A^(3), Ŝ_A^(1)] = i · Ŝ_A^(2)`. -/
theorem sublatticeSpinSOp3_commutator_sublatticeSpinSOp1 (A : Λ → Bool) :
    (sublatticeSpinSOp3 N A * sublatticeSpinSOp1 N A
        - sublatticeSpinSOp1 N A * sublatticeSpinSOp3 N A : ManyBodyOpS Λ N) =
      Complex.I • sublatticeSpinSOp2 N A := by
  unfold sublatticeSpinSOp1 sublatticeSpinSOp2 sublatticeSpinSOp3
  exact sublatticeSpinS_commutator_general N A (spinSOp3_commutator_spinSOp1 N)

/-! ## Sublattice Casimir self-invariance `[(Ŝ_A)², Ŝ_A^(α)] = 0`
(spin-`S`) -/

/-- Internal Leibniz: `[X·X, C] = X·[X,C] + [X,C]·X`. -/
private lemma square_commutator_sublatticeS (X C : ManyBodyOpS Λ N) :
    X * X * C - C * (X * X) = X * (X * C - C * X) + (X * C - C * X) * X := by
  rw [mul_sub, sub_mul]
  have h1 : X * (C * X) = X * C * X := (mul_assoc X C X).symm
  have h2 : X * X * C = X * (X * C) := mul_assoc X X C
  have h3 : C * (X * X) = C * X * X := (mul_assoc C X X).symm
  rw [h1, h2, h3]; abel

/-- Sublattice Casimir invariance for spin-`S`: `[(Ŝ_A)², Ŝ_A^(1)] = 0`. -/
theorem sublatticeSpinSquaredS_commutator_sublatticeSpinSOp1 (A : Λ → Bool) :
    sublatticeSpinSquaredS N A * sublatticeSpinSOp1 N A
        - sublatticeSpinSOp1 N A * sublatticeSpinSquaredS N A = 0 := by
  unfold sublatticeSpinSquaredS
  set P := sublatticeSpinSOp1 N A
  set Q := sublatticeSpinSOp2 N A
  set R := sublatticeSpinSOp3 N A
  have hPQ : P * Q - Q * P = Complex.I • R :=
    sublatticeSpinSOp1_commutator_sublatticeSpinSOp2 N A
  have hRP : R * P - P * R = Complex.I • Q :=
    sublatticeSpinSOp3_commutator_sublatticeSpinSOp1 N A
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show P * P * P + Q * Q * P + R * R * P - (P * (P * P) + P * (Q * Q) + P * (R * R))
        = (P * P * P - P * (P * P)) + (Q * Q * P - P * (Q * Q))
          + (R * R * P - P * (R * R)) from by abel]
  rw [square_commutator_sublatticeS N P P, square_commutator_sublatticeS N Q P,
    square_commutator_sublatticeS N R P]
  have hPP : P * P - P * P = (0 : ManyBodyOpS Λ N) := sub_self _
  have hQP : Q * P - P * Q = -(Complex.I • R) := by
    rw [show Q * P - P * Q = -(P * Q - Q * P) from by abel, hPQ]
  rw [hPP, hQP, hRP]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [zero_add]
  abel

/-- Sublattice Casimir invariance for spin-`S`: `[(Ŝ_A)², Ŝ_A^(2)] = 0`. -/
theorem sublatticeSpinSquaredS_commutator_sublatticeSpinSOp2 (A : Λ → Bool) :
    sublatticeSpinSquaredS N A * sublatticeSpinSOp2 N A
        - sublatticeSpinSOp2 N A * sublatticeSpinSquaredS N A = 0 := by
  unfold sublatticeSpinSquaredS
  set P := sublatticeSpinSOp1 N A
  set Q := sublatticeSpinSOp2 N A
  set R := sublatticeSpinSOp3 N A
  have hPQ : P * Q - Q * P = Complex.I • R :=
    sublatticeSpinSOp1_commutator_sublatticeSpinSOp2 N A
  have hQR : Q * R - R * Q = Complex.I • P :=
    sublatticeSpinSOp2_commutator_sublatticeSpinSOp3 N A
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show P * P * Q + Q * Q * Q + R * R * Q - (Q * (P * P) + Q * (Q * Q) + Q * (R * R))
        = (P * P * Q - Q * (P * P)) + (Q * Q * Q - Q * (Q * Q))
          + (R * R * Q - Q * (R * R)) from by abel]
  rw [square_commutator_sublatticeS N P Q, square_commutator_sublatticeS N Q Q,
    square_commutator_sublatticeS N R Q]
  have hQQ : Q * Q - Q * Q = (0 : ManyBodyOpS Λ N) := sub_self _
  have hRQ : R * Q - Q * R = -(Complex.I • P) := by
    rw [show R * Q - Q * R = -(Q * R - R * Q) from by abel, hQR]
  rw [hPQ, hQQ, hRQ]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- Sublattice Casimir invariance for spin-`S`: `[(Ŝ_A)², Ŝ_A^(3)] = 0`. -/
theorem sublatticeSpinSquaredS_commutator_sublatticeSpinSOp3 (A : Λ → Bool) :
    sublatticeSpinSquaredS N A * sublatticeSpinSOp3 N A
        - sublatticeSpinSOp3 N A * sublatticeSpinSquaredS N A = 0 := by
  unfold sublatticeSpinSquaredS
  set P := sublatticeSpinSOp1 N A
  set Q := sublatticeSpinSOp2 N A
  set R := sublatticeSpinSOp3 N A
  have hRP : R * P - P * R = Complex.I • Q :=
    sublatticeSpinSOp3_commutator_sublatticeSpinSOp1 N A
  have hQR : Q * R - R * Q = Complex.I • P :=
    sublatticeSpinSOp2_commutator_sublatticeSpinSOp3 N A
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show P * P * R + Q * Q * R + R * R * R - (R * (P * P) + R * (Q * Q) + R * (R * R))
        = (P * P * R - R * (P * P)) + (Q * Q * R - R * (Q * Q))
          + (R * R * R - R * (R * R)) from by abel]
  rw [square_commutator_sublatticeS N P R, square_commutator_sublatticeS N Q R,
    square_commutator_sublatticeS N R R]
  have hPR : P * R - R * P = -(Complex.I • Q) := by
    rw [show P * R - R * P = -(R * P - P * R) from by abel, hRP]
  have hRR : R * R - R * R = (0 : ManyBodyOpS Λ N) := sub_self _
  rw [hPR, hQR, hRR]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- `Commute (Ŝ_A)² Ŝ_A^(1)`. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOp1 (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp1 N A) :=
  sub_eq_zero.mp (sublatticeSpinSquaredS_commutator_sublatticeSpinSOp1 N A)

/-- `Commute (Ŝ_A)² Ŝ_A^(2)`. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOp2 (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp2 N A) :=
  sub_eq_zero.mp (sublatticeSpinSquaredS_commutator_sublatticeSpinSOp2 N A)

/-- `Commute (Ŝ_A)² Ŝ_A^(3)`. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOp3 (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp3 N A) :=
  sub_eq_zero.mp (sublatticeSpinSquaredS_commutator_sublatticeSpinSOp3 N A)

/-! ## Sublattice Casimir commutes with `Ŝ_¬A^(α)` (spin-`S`) -/

/-- `Commute (Ŝ_A)² Ŝ_¬A^(1)` (spin-`S`). Each axis-`β` square
`(Ŝ_A^(β))²` commutes with `Ŝ_¬A^(1)` by `Commute.mul_left`
applied to the mixed-axes cross-commute. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOp1_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A)
            (sublatticeSpinSOp1 N (fun x => ! A x)) := by
  unfold sublatticeSpinSquaredS
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact (sublatticeSpinSOp1_cross_commute N A).mul_left
      (sublatticeSpinSOp1_cross_commute N A)
  · exact (sublatticeSpinSOp2_cross_commute_op1 N A).mul_left
      (sublatticeSpinSOp2_cross_commute_op1 N A)
  · exact (sublatticeSpinSOp3_cross_commute_op1 N A).mul_left
      (sublatticeSpinSOp3_cross_commute_op1 N A)

/-- `Commute (Ŝ_A)² Ŝ_¬A^(2)`. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOp2_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A)
            (sublatticeSpinSOp2 N (fun x => ! A x)) := by
  unfold sublatticeSpinSquaredS
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact (sublatticeSpinSOp1_cross_commute_op2 N A).mul_left
      (sublatticeSpinSOp1_cross_commute_op2 N A)
  · exact (sublatticeSpinSOp2_cross_commute N A).mul_left
      (sublatticeSpinSOp2_cross_commute N A)
  · exact (sublatticeSpinSOp3_cross_commute_op2 N A).mul_left
      (sublatticeSpinSOp3_cross_commute_op2 N A)

/-- `Commute (Ŝ_A)² Ŝ_¬A^(3)`. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOp3_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A)
            (sublatticeSpinSOp3 N (fun x => ! A x)) := by
  unfold sublatticeSpinSquaredS
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact (sublatticeSpinSOp1_cross_commute_op3 N A).mul_left
      (sublatticeSpinSOp1_cross_commute_op3 N A)
  · exact (sublatticeSpinSOp2_cross_commute_op3 N A).mul_left
      (sublatticeSpinSOp2_cross_commute_op3 N A)
  · exact (sublatticeSpinSOp3_cross_commute N A).mul_left
      (sublatticeSpinSOp3_cross_commute N A)

/-- `Commute (Ŝ_A)² (Ŝ_¬A)²` for spin-`S`. Each pairwise
component `Commute ((Ŝ_A^(α))²) ((Ŝ_¬A^(β))²)` follows from the
mixed-axes cross-commute by chaining `Commute.mul_left` /
`Commute.mul_right`. Sets up the joint eigenbasis of
`(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` for the toy-Hamiltonian
eigenvalue analysis at general spin-`S`. -/
theorem sublatticeSpinSquaredS_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A)
            (sublatticeSpinSquaredS N (fun x => ! A x)) := by
  unfold sublatticeSpinSquaredS
  have hα1β1 := sublatticeSpinSOp1_cross_commute N A
  have hα1β2 := sublatticeSpinSOp1_cross_commute_op2 N A
  have hα1β3 := sublatticeSpinSOp1_cross_commute_op3 N A
  have hα2β1 := sublatticeSpinSOp2_cross_commute_op1 N A
  have hα2β2 := sublatticeSpinSOp2_cross_commute N A
  have hα2β3 := sublatticeSpinSOp2_cross_commute_op3 N A
  have hα3β1 := sublatticeSpinSOp3_cross_commute_op1 N A
  have hα3β2 := sublatticeSpinSOp3_cross_commute_op2 N A
  have hα3β3 := sublatticeSpinSOp3_cross_commute N A
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

/-! ## Sublattice Casimir commutes with the total spin generators -/

/-- `Commute (Ŝ_A)² (Ŝ_tot^(1))`. Combines self-invariance (axis 1) with
the `Ŝ_¬A^(1)` commutativity, since `Ŝ_tot^(1) = Ŝ_A^(1) + Ŝ_¬A^(1)`. -/
theorem sublatticeSpinSquaredS_commute_totalSpinSOp1 (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSOp1 Λ N) := by
  rw [totalSpinSOp1_eq_sublattice_sum (N := N) A]
  exact (sublatticeSpinSquaredS_commute_sublatticeSpinSOp1 N A).add_right
    (sublatticeSpinSquaredS_commute_sublatticeSpinSOp1_complement N A)

/-- `Commute (Ŝ_A)² (Ŝ_tot^(2))`. -/
theorem sublatticeSpinSquaredS_commute_totalSpinSOp2 (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSOp2 Λ N) := by
  rw [totalSpinSOp2_eq_sublattice_sum (N := N) A]
  exact (sublatticeSpinSquaredS_commute_sublatticeSpinSOp2 N A).add_right
    (sublatticeSpinSquaredS_commute_sublatticeSpinSOp2_complement N A)

/-- `Commute (Ŝ_A)² (Ŝ_tot^(3))`. -/
theorem sublatticeSpinSquaredS_commute_totalSpinSOp3 (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSOp3 Λ N) := by
  rw [totalSpinSOp3_eq_sublattice_sum (N := N) A]
  exact (sublatticeSpinSquaredS_commute_sublatticeSpinSOp3 N A).add_right
    (sublatticeSpinSquaredS_commute_sublatticeSpinSOp3_complement N A)

/-- `Commute (Ŝ_A)² (Ŝ_tot)²`. The third pairwise commutativity needed
for the joint eigenbasis of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` (Tasaki §2.5
toy-Hamiltonian eigenvalue analysis). -/
theorem sublatticeSpinSquaredS_commute_totalSpinSSquared (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSSquared Λ N) := by
  unfold totalSpinSSquared
  have h1 := sublatticeSpinSquaredS_commute_totalSpinSOp1 N A
  have h2 := sublatticeSpinSquaredS_commute_totalSpinSOp2 N A
  have h3 := sublatticeSpinSquaredS_commute_totalSpinSOp3 N A
  exact ((h1.mul_right h1).add_right (h2.mul_right h2)).add_right (h3.mul_right h3)

/-! ## Sublattice ladder operators (raising / lowering on `A`) -/

/-- Sublattice raising operator on `A`:
`Ŝ_A^+ := Σ_{x : A x} onSiteS x (spinSOpPlus N)`.

Mirror of `totalSpinSOpPlus` restricted to the `A`-sublattice. -/
noncomputable def sublatticeSpinSOpPlus (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOpPlus N) else 0

/-- Sublattice lowering operator on `A`:
`Ŝ_A^- := Σ_{x : A x} onSiteS x (spinSOpMinus N)`. -/
noncomputable def sublatticeSpinSOpMinus (A : Λ → Bool) : ManyBodyOpS Λ N :=
  ∑ x : Λ, if A x then onSiteS x (spinSOpMinus N) else 0

/-- `Ŝ_A^+ = Ŝ_A^(1) + i · Ŝ_A^(2)`. -/
theorem sublatticeSpinSOpPlus_eq_add (A : Λ → Bool) :
    sublatticeSpinSOpPlus N A =
      sublatticeSpinSOp1 N A + Complex.I • sublatticeSpinSOp2 N A := by
  unfold sublatticeSpinSOpPlus sublatticeSpinSOp1 sublatticeSpinSOp2
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA, if_pos hA]
    rw [← onSiteS_smul, ← onSiteS_add, spinSOpPlus_eq_one_add_I_smul_two]
  · cases h : A x
    · rw [if_neg, if_neg, if_neg]
      · rw [smul_zero, add_zero]
      · simp
      · simp
      · simp
    · exact absurd h hA

/-- `Ŝ_A^- = Ŝ_A^(1) − i · Ŝ_A^(2)`. -/
theorem sublatticeSpinSOpMinus_eq_sub (A : Λ → Bool) :
    sublatticeSpinSOpMinus N A =
      sublatticeSpinSOp1 N A - Complex.I • sublatticeSpinSOp2 N A := by
  unfold sublatticeSpinSOpMinus sublatticeSpinSOp1 sublatticeSpinSOp2
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA, if_pos hA]
    rw [← onSiteS_smul, ← onSiteS_sub, spinSOpMinus_eq_one_sub_I_smul_two]
  · cases h : A x
    · rw [if_neg, if_neg, if_neg]
      · rw [smul_zero, sub_zero]
      · simp
      · simp
      · simp
    · exact absurd h hA

/-- The total raising operator decomposes as a sum over sublattices:
`Ŝ^+_tot = Ŝ_A^+ + Ŝ_¬A^+`. -/
theorem totalSpinSOpPlus_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOpPlus Λ N =
      sublatticeSpinSOpPlus N A + sublatticeSpinSOpPlus N (fun x => ! A x) := by
  unfold totalSpinSOpPlus sublatticeSpinSOpPlus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total lowering operator decomposes as a sum over sublattices:
`Ŝ^-_tot = Ŝ_A^- + Ŝ_¬A^-`. -/
theorem totalSpinSOpMinus_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinSOpMinus Λ N =
      sublatticeSpinSOpMinus N A + sublatticeSpinSOpMinus N (fun x => ! A x) := by
  unfold totalSpinSOpMinus sublatticeSpinSOpMinus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- `Ŝ_A^+ · |σ_⊤⟩ = 0`: the sublattice raising operator annihilates
the all-up state (highest weight at each A-site). -/
theorem sublatticeSpinSOpPlus_mulVec_allAlignedStateS_zero (A : Λ → Bool) :
    (sublatticeSpinSOpPlus N A).mulVec
        (allAlignedStateS Λ N (0 : Fin (N + 1))) = 0 := by
  unfold sublatticeSpinSOpPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_spinSOpPlus_mulVec_allAlignedStateS_zero x
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-- `Ŝ_A^- · |σ_⊥⟩ = 0`: the sublattice lowering operator annihilates
the all-down state (lowest weight at each A-site). -/
theorem sublatticeSpinSOpMinus_mulVec_allAlignedStateS_last (A : Λ → Bool) :
    (sublatticeSpinSOpMinus N A).mulVec
        (allAlignedStateS Λ N (Fin.last N)) = 0 := by
  unfold sublatticeSpinSOpMinus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_spinSOpMinus_mulVec_allAlignedStateS_last x
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-! ## Sublattice Cartan relations -/

/-- Sublattice Cartan relation: `[Ŝ_A^(3), Ŝ_A^+] = Ŝ_A^+`. The sublattice
ladder raising operator shifts the A-sublattice S^z eigenvalue by +1.

Derived from the sublattice SU(2) algebra (PR #1048):
`[Ŝ_A^(3), Ŝ_A^(1)+iŜ_A^(2)] = iŜ_A^(2) + i(-iŜ_A^(1)) = Ŝ_A^(1)+iŜ_A^(2)`. -/
theorem sublatticeSpinSOp3_commutator_sublatticeSpinSOpPlus (A : Λ → Bool) :
    sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A
        - sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A =
      sublatticeSpinSOpPlus N A := by
  rw [sublatticeSpinSOpPlus_eq_add]
  have h31 := sublatticeSpinSOp3_commutator_sublatticeSpinSOp1 N A
  have h23 := sublatticeSpinSOp2_commutator_sublatticeSpinSOp3 N A
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  -- The goal is: S3 S1 + I•(S3 S2) - (S1 S3 + I•(S2 S3)) = S1 + I•S2
  -- Reorganize: (S3 S1 - S1 S3) + I•(S3 S2 - S2 S3) = (S3 S1 - S1 S3) - I•(S2 S3 - S3 S2)
  --           = I•S2 - I•(I•S1)
  --           = I•S2 - (I*I)•S1 = I•S2 + S1
  have hI2 : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
  have hkey : sublatticeSpinSOp3 N A * sublatticeSpinSOp1 N A +
        Complex.I • (sublatticeSpinSOp3 N A * sublatticeSpinSOp2 N A) -
      (sublatticeSpinSOp1 N A * sublatticeSpinSOp3 N A +
        Complex.I • (sublatticeSpinSOp2 N A * sublatticeSpinSOp3 N A)) =
      (sublatticeSpinSOp3 N A * sublatticeSpinSOp1 N A -
        sublatticeSpinSOp1 N A * sublatticeSpinSOp3 N A) -
      Complex.I • (sublatticeSpinSOp2 N A * sublatticeSpinSOp3 N A -
        sublatticeSpinSOp3 N A * sublatticeSpinSOp2 N A) := by
    rw [smul_sub]; abel
  rw [hkey, h31, h23, smul_smul, hI2, neg_smul, one_smul, sub_neg_eq_add]
  abel

/-- Sublattice Cartan relation: `[Ŝ_A^(3), Ŝ_A^-] = -Ŝ_A^-`. The sublattice
ladder lowering operator shifts the A-sublattice S^z eigenvalue by -1. -/
theorem sublatticeSpinSOp3_commutator_sublatticeSpinSOpMinus (A : Λ → Bool) :
    sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A
        - sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A =
      -sublatticeSpinSOpMinus N A := by
  rw [sublatticeSpinSOpMinus_eq_sub]
  have h31 := sublatticeSpinSOp3_commutator_sublatticeSpinSOp1 N A
  have h23 := sublatticeSpinSOp2_commutator_sublatticeSpinSOp3 N A
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  have hI2 : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
  have hkey : sublatticeSpinSOp3 N A * sublatticeSpinSOp1 N A -
        Complex.I • (sublatticeSpinSOp3 N A * sublatticeSpinSOp2 N A) -
      (sublatticeSpinSOp1 N A * sublatticeSpinSOp3 N A -
        Complex.I • (sublatticeSpinSOp2 N A * sublatticeSpinSOp3 N A)) =
      (sublatticeSpinSOp3 N A * sublatticeSpinSOp1 N A -
        sublatticeSpinSOp1 N A * sublatticeSpinSOp3 N A) +
      Complex.I • (sublatticeSpinSOp2 N A * sublatticeSpinSOp3 N A -
        sublatticeSpinSOp3 N A * sublatticeSpinSOp2 N A) := by
    rw [smul_sub]; abel
  rw [hkey, h31, h23, smul_smul, hI2, neg_smul, one_smul]
  rw [show -sublatticeSpinSOp1 N A = -(sublatticeSpinSOp1 N A -
      Complex.I • sublatticeSpinSOp2 N A) - Complex.I • sublatticeSpinSOp2 N A
      from by abel]
  abel

/-- Total Cartan relation for sublattice raising:
`[Ŝ_tot^(3), Ŝ_A^+] = Ŝ_A^+`. The sublattice raising operator shifts
the total S^z eigenvalue by +1 (since it acts only on A and the ¬A part
commutes via cross-sublattice commutativity). -/
theorem totalSpinSOp3_commutator_sublatticeSpinSOpPlus (A : Λ → Bool) :
    totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A
        - sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N =
      sublatticeSpinSOpPlus N A := by
  rw [totalSpinSOp3_eq_sublattice_sum (N := N) A]
  rw [add_mul, mul_add]
  -- Goal: Ŝ_A^(3) Ŝ_A^+ + Ŝ_¬A^(3) Ŝ_A^+ - (Ŝ_A^+ Ŝ_A^(3) + Ŝ_A^+ Ŝ_¬A^(3)) = Ŝ_A^+
  -- Use [Ŝ_¬A^(3), Ŝ_A^+] = 0 and [Ŝ_A^(3), Ŝ_A^+] = Ŝ_A^+.
  have h_self := sublatticeSpinSOp3_commutator_sublatticeSpinSOpPlus N A
  -- Ŝ_¬A^(3) commutes with Ŝ_A^+: cross-sublattice via Ŝ_A^+ = Ŝ_A^(1) + i Ŝ_A^(2)
  have h_cross : sublatticeSpinSOp3 N (fun x => ! A x) * sublatticeSpinSOpPlus N A =
      sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N (fun x => ! A x) := by
    rw [sublatticeSpinSOpPlus_eq_add]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    -- We want: Ŝ_¬A^(3) commutes with Ŝ_A^(1) and Ŝ_A^(2).
    -- `sublatticeSpinSOp1_cross_commute_op3 A : Commute (Ŝ_A^(1)) (Ŝ_¬A^(3))`.
    have h31 := (sublatticeSpinSOp1_cross_commute_op3 N A).symm.eq
    have h32 := (sublatticeSpinSOp2_cross_commute_op3 N A).symm.eq
    rw [h31, h32]
  rw [h_cross]
  -- Goal: Ŝ_A^(3) Ŝ_A^+ + Ŝ_A^+ Ŝ_¬A^(3) - (Ŝ_A^+ Ŝ_A^(3) + Ŝ_A^+ Ŝ_¬A^(3)) = Ŝ_A^+
  -- = (Ŝ_A^(3) Ŝ_A^+ - Ŝ_A^+ Ŝ_A^(3)) = Ŝ_A^+ ✓
  rw [show sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A +
        sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N (fun x => ! A x) -
      (sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A +
        sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N (fun x => ! A x)) =
      sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A -
        sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A from by abel]
  exact h_self

/-- Total Cartan relation for sublattice lowering:
`[Ŝ_tot^(3), Ŝ_A^-] = -Ŝ_A^-`. -/
theorem totalSpinSOp3_commutator_sublatticeSpinSOpMinus (A : Λ → Bool) :
    totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A
        - sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N =
      -sublatticeSpinSOpMinus N A := by
  rw [totalSpinSOp3_eq_sublattice_sum (N := N) A]
  rw [add_mul, mul_add]
  have h_self := sublatticeSpinSOp3_commutator_sublatticeSpinSOpMinus N A
  have h_cross : sublatticeSpinSOp3 N (fun x => ! A x) * sublatticeSpinSOpMinus N A =
      sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N (fun x => ! A x) := by
    rw [sublatticeSpinSOpMinus_eq_sub]
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    have h31 := (sublatticeSpinSOp1_cross_commute_op3 N A).symm.eq
    have h32 := (sublatticeSpinSOp2_cross_commute_op3 N A).symm.eq
    rw [h31, h32]
  rw [h_cross]
  rw [show sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A +
        sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N (fun x => ! A x) -
      (sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A +
        sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N (fun x => ! A x)) =
      sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A -
        sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A from by abel]
  exact h_self

/-! ## Sublattice ladder adjoint relations -/

/-- `(Ŝ_A^+)† = Ŝ_A^-`: the sublattice raising and lowering operators
are Hermitian conjugates of each other. -/
theorem sublatticeSpinSOpPlus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinSOpPlus N A).conjTranspose = sublatticeSpinSOpMinus N A := by
  unfold sublatticeSpinSOpPlus sublatticeSpinSOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSiteS_conjTranspose, spinSOpPlus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-- `(Ŝ_A^-)† = Ŝ_A^+`. -/
theorem sublatticeSpinSOpMinus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinSOpMinus N A).conjTranspose = sublatticeSpinSOpPlus N A := by
  unfold sublatticeSpinSOpPlus sublatticeSpinSOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSiteS_conjTranspose, spinSOpMinus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder operators shift the magnetization subspace -/

/-- `Ŝ_A^- · v ∈ magSubspaceS Λ N (M − 1)` for `v ∈ magSubspaceS Λ N M`.
The sublattice lowering operator shifts the (total) magnetisation by `-1`. -/
theorem sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (sublatticeSpinSOpMinus N A).mulVec v ∈ magSubspaceS Λ N (M - 1) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have h := totalSpinSOp3_commutator_sublatticeSpinSOpMinus N A
  have hcomm : totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A =
      sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N - sublatticeSpinSOpMinus N A := by
    have hadd : totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A =
        (totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A -
          sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N) +
        sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- `Ŝ_A^+ · v ∈ magSubspaceS Λ N (M + 1)` for `v ∈ magSubspaceS Λ N M`. -/
theorem sublatticeSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (sublatticeSpinSOpPlus N A).mulVec v ∈ magSubspaceS Λ N (M + 1) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have h := totalSpinSOp3_commutator_sublatticeSpinSOpPlus N A
  have hcomm : totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A =
      sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N + sublatticeSpinSOpPlus N A := by
    have hadd : totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A =
        (totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A -
          sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N) +
        sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

end LatticeSystem.Quantum
