import LatticeSystem.Quantum.TotalSpin
import LatticeSystem.Quantum.TotalSpin.Casimir
import LatticeSystem.Quantum.MagnetizationSubspace

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

/-! ## Sublattice SU(2) algebra `[Ŝ_A^α, Ŝ_A^β] = i ε^αβγ Ŝ_A^γ` -/

/-- Generic sublattice-spin commutator: if `[Sα, Sβ] = I • Sγ` then
`[Σ_x∈A onSite x Sα, Σ_x∈A onSite x Sβ] = I • Σ_x∈A onSite x Sγ`.

The proof follows the `totalSpin_commutator_general` structure,
with the indicator `if A x then ... else 0` factored through.

For `x ≠ y`, the cross-pair vanishes (`onSite_mul_onSite_of_ne`);
for `x = y` and `A x = true`, the diagonal contribution gives
`onSite x [Sα, Sβ] = I • onSite x Sγ`. -/
private lemma sublatticeSpin_commutator_general
    (A : Λ → Bool)
    {Sα Sβ Sγ : Matrix (Fin 2) (Fin 2) ℂ}
    (hab : Sα * Sβ - Sβ * Sα = Complex.I • Sγ) :
    ((∑ x : Λ, if A x then onSite x Sα else 0) *
        (∑ x : Λ, if A x then onSite x Sβ else 0) -
      (∑ x : Λ, if A x then onSite x Sβ else 0) *
        (∑ x : Λ, if A x then onSite x Sα else 0) : ManyBodyOp Λ) =
      Complex.I • ∑ x : Λ, if A x then onSite x Sγ else 0 := by
  calc (∑ x : Λ, if A x then onSite x Sα else 0) *
            (∑ x : Λ, if A x then onSite x Sβ else 0) -
          (∑ x : Λ, if A x then onSite x Sβ else 0) *
            (∑ x : Λ, if A x then onSite x Sα else 0)
      = ∑ x : Λ, ∑ y : Λ,
          ((if A x then onSite x Sα else 0) *
              (if A y then onSite y Sβ else 0) -
            (if A y then onSite y Sβ else 0) *
              (if A x then onSite x Sα else 0)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm
          (f := fun y x => (if A y then onSite y Sβ else 0) *
              (if A x then onSite x Sα else 0))
          (s := Finset.univ) (t := Finset.univ)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Λ, (if A x then Complex.I • onSite x Sγ else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · -- diagonal term: y = x.
          by_cases hAx : A x = true
          · simp only [if_pos hAx]
            rw [onSite_commutator_same, hab, onSite_smul]
          · simp only [if_neg hAx, mul_zero, sub_zero]
        · -- off-diagonal term: y ≠ x, vanishes.
          intros y _ hyx
          by_cases hAx : A x = true
          · by_cases hAy : A y = true
            · simp only [if_pos hAx, if_pos hAy]
              rw [onSite_mul_onSite_of_ne hyx.symm]; simp
            · simp only [if_pos hAx, if_neg hAy, mul_zero, zero_mul, sub_zero]
          · simp only [if_neg hAx, mul_zero, zero_mul, sub_zero]
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = Complex.I • ∑ x : Λ, if A x then onSite x Sγ else 0 := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hAx : A x = true
        · rw [if_pos hAx, if_pos hAx]
        · rw [if_neg hAx, if_neg hAx, smul_zero]

/-- Sublattice spin commutator: `[Ŝ_A^(1), Ŝ_A^(2)] = i · Ŝ_A^(3)`. -/
theorem sublatticeSpinHalfOp1_commutator_sublatticeSpinHalfOp2 (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp2 A
        - sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp1 A : ManyBodyOp Λ) =
      Complex.I • sublatticeSpinHalfOp3 A := by
  unfold sublatticeSpinHalfOp1 sublatticeSpinHalfOp2 sublatticeSpinHalfOp3
  exact sublatticeSpin_commutator_general A spinHalfOp1_commutator_spinHalfOp2

/-- Sublattice spin commutator: `[Ŝ_A^(2), Ŝ_A^(3)] = i · Ŝ_A^(1)`. -/
theorem sublatticeSpinHalfOp2_commutator_sublatticeSpinHalfOp3 (A : Λ → Bool) :
    (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp3 A
        - sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp2 A : ManyBodyOp Λ) =
      Complex.I • sublatticeSpinHalfOp1 A := by
  unfold sublatticeSpinHalfOp1 sublatticeSpinHalfOp2 sublatticeSpinHalfOp3
  exact sublatticeSpin_commutator_general A spinHalfOp2_commutator_spinHalfOp3

/-- Sublattice spin commutator: `[Ŝ_A^(3), Ŝ_A^(1)] = i · Ŝ_A^(2)`. -/
theorem sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOp1 (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp1 A
        - sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp3 A : ManyBodyOp Λ) =
      Complex.I • sublatticeSpinHalfOp2 A := by
  unfold sublatticeSpinHalfOp1 sublatticeSpinHalfOp2 sublatticeSpinHalfOp3
  exact sublatticeSpin_commutator_general A spinHalfOp3_commutator_spinHalfOp1

/-! ## Sublattice Casimir self-invariance `[(Ŝ_A)², Ŝ_A^(α)] = 0` -/

/-- Internal Leibniz: `[X·X, C] = X·[X,C] + [X,C]·X`. Pure ring identity,
the sublattice analog of `square_commutator_totalSpin`. -/
private lemma square_commutator_sublattice (X C : ManyBodyOp Λ) :
    X * X * C - C * (X * X) = X * (X * C - C * X) + (X * C - C * X) * X := by
  rw [mul_sub, sub_mul]
  have h1 : X * (C * X) = X * C * X := (mul_assoc X C X).symm
  have h2 : X * X * C = X * (X * C) := mul_assoc X X C
  have h3 : C * (X * X) = C * X * X := (mul_assoc C X X).symm
  rw [h1, h2, h3]; abel

/-- Sublattice Casimir invariance: `[(Ŝ_A)², Ŝ_A^(1)] = 0`. -/
theorem sublatticeSpinHalfSquared_commutator_sublatticeSpinHalfOp1 (A : Λ → Bool) :
    sublatticeSpinHalfSquared A * sublatticeSpinHalfOp1 A
        - sublatticeSpinHalfOp1 A * sublatticeSpinHalfSquared A = 0 := by
  unfold sublatticeSpinHalfSquared
  set P := sublatticeSpinHalfOp1 A
  set Q := sublatticeSpinHalfOp2 A
  set R := sublatticeSpinHalfOp3 A
  have hPQ : P * Q - Q * P = Complex.I • R :=
    sublatticeSpinHalfOp1_commutator_sublatticeSpinHalfOp2 A
  have hRP : R * P - P * R = Complex.I • Q :=
    sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOp1 A
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show P * P * P + Q * Q * P + R * R * P - (P * (P * P) + P * (Q * Q) + P * (R * R))
        = (P * P * P - P * (P * P)) + (Q * Q * P - P * (Q * Q))
          + (R * R * P - P * (R * R)) from by abel]
  rw [square_commutator_sublattice P P, square_commutator_sublattice Q P,
    square_commutator_sublattice R P]
  have hPP : P * P - P * P = (0 : ManyBodyOp Λ) := sub_self _
  have hQP : Q * P - P * Q = -(Complex.I • R) := by
    rw [show Q * P - P * Q = -(P * Q - Q * P) from by abel, hPQ]
  rw [hPP, hQP, hRP]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [zero_add]
  abel

/-- Sublattice Casimir invariance: `[(Ŝ_A)², Ŝ_A^(2)] = 0`. -/
theorem sublatticeSpinHalfSquared_commutator_sublatticeSpinHalfOp2 (A : Λ → Bool) :
    sublatticeSpinHalfSquared A * sublatticeSpinHalfOp2 A
        - sublatticeSpinHalfOp2 A * sublatticeSpinHalfSquared A = 0 := by
  unfold sublatticeSpinHalfSquared
  set P := sublatticeSpinHalfOp1 A
  set Q := sublatticeSpinHalfOp2 A
  set R := sublatticeSpinHalfOp3 A
  have hPQ : P * Q - Q * P = Complex.I • R :=
    sublatticeSpinHalfOp1_commutator_sublatticeSpinHalfOp2 A
  have hQR : Q * R - R * Q = Complex.I • P :=
    sublatticeSpinHalfOp2_commutator_sublatticeSpinHalfOp3 A
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show P * P * Q + Q * Q * Q + R * R * Q - (Q * (P * P) + Q * (Q * Q) + Q * (R * R))
        = (P * P * Q - Q * (P * P)) + (Q * Q * Q - Q * (Q * Q))
          + (R * R * Q - Q * (R * R)) from by abel]
  rw [square_commutator_sublattice P Q, square_commutator_sublattice Q Q,
    square_commutator_sublattice R Q]
  have hQQ : Q * Q - Q * Q = (0 : ManyBodyOp Λ) := sub_self _
  have hRQ : R * Q - Q * R = -(Complex.I • P) := by
    rw [show R * Q - Q * R = -(Q * R - R * Q) from by abel, hQR]
  rw [hPQ, hQQ, hRQ]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- Sublattice Casimir invariance: `[(Ŝ_A)², Ŝ_A^(3)] = 0`. -/
theorem sublatticeSpinHalfSquared_commutator_sublatticeSpinHalfOp3 (A : Λ → Bool) :
    sublatticeSpinHalfSquared A * sublatticeSpinHalfOp3 A
        - sublatticeSpinHalfOp3 A * sublatticeSpinHalfSquared A = 0 := by
  unfold sublatticeSpinHalfSquared
  set P := sublatticeSpinHalfOp1 A
  set Q := sublatticeSpinHalfOp2 A
  set R := sublatticeSpinHalfOp3 A
  have hRP : R * P - P * R = Complex.I • Q :=
    sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOp1 A
  have hQR : Q * R - R * Q = Complex.I • P :=
    sublatticeSpinHalfOp2_commutator_sublatticeSpinHalfOp3 A
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show P * P * R + Q * Q * R + R * R * R - (R * (P * P) + R * (Q * Q) + R * (R * R))
        = (P * P * R - R * (P * P)) + (Q * Q * R - R * (Q * Q))
          + (R * R * R - R * (R * R)) from by abel]
  rw [square_commutator_sublattice P R, square_commutator_sublattice Q R,
    square_commutator_sublattice R R]
  have hPR : P * R - R * P = -(Complex.I • Q) := by
    rw [show P * R - R * P = -(R * P - P * R) from by abel, hRP]
  have hRR : R * R - R * R = (0 : ManyBodyOp Λ) := sub_self _
  rw [hPR, hQR, hRR]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- `Commute (Ŝ_A)² (Ŝ_A^(1))`. -/
theorem sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp1 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp1 A) :=
  sub_eq_zero.mp (sublatticeSpinHalfSquared_commutator_sublatticeSpinHalfOp1 A)

/-- `Commute (Ŝ_A)² (Ŝ_A^(2))`. -/
theorem sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp2 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp2 A) :=
  sub_eq_zero.mp (sublatticeSpinHalfSquared_commutator_sublatticeSpinHalfOp2 A)

/-- `Commute (Ŝ_A)² (Ŝ_A^(3))`. -/
theorem sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp3 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp3 A) :=
  sub_eq_zero.mp (sublatticeSpinHalfSquared_commutator_sublatticeSpinHalfOp3 A)

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

/-! ## Sublattice Casimir commutes with `Ŝ_¬A^(α)` -/

/-- `Commute (Ŝ_A)² (Ŝ_¬A^(1))`.  Each axis-`β` square `(Ŝ_A^(β))²` commutes
with `Ŝ_¬A^(1)` by `Commute.mul_left` applied to the mixed-axes
cross-commute. -/
theorem sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp1_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp1 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfSquared
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact (sublatticeSpinHalfOp1_cross_commute A).mul_left
      (sublatticeSpinHalfOp1_cross_commute A)
  · exact (sublatticeSpinHalfOp2_cross_commute_op1 A).mul_left
      (sublatticeSpinHalfOp2_cross_commute_op1 A)
  · exact (sublatticeSpinHalfOp3_cross_commute_op1 A).mul_left
      (sublatticeSpinHalfOp3_cross_commute_op1 A)

/-- `Commute (Ŝ_A)² (Ŝ_¬A^(2))`. -/
theorem sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp2_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp2 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfSquared
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact (sublatticeSpinHalfOp1_cross_commute_op2 A).mul_left
      (sublatticeSpinHalfOp1_cross_commute_op2 A)
  · exact (sublatticeSpinHalfOp2_cross_commute A).mul_left
      (sublatticeSpinHalfOp2_cross_commute A)
  · exact (sublatticeSpinHalfOp3_cross_commute_op2 A).mul_left
      (sublatticeSpinHalfOp3_cross_commute_op2 A)

/-- `Commute (Ŝ_A)² (Ŝ_¬A^(3))`. -/
theorem sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp3_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (sublatticeSpinHalfOp3 (fun x => ! A x)) := by
  unfold sublatticeSpinHalfSquared
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact (sublatticeSpinHalfOp1_cross_commute_op3 A).mul_left
      (sublatticeSpinHalfOp1_cross_commute_op3 A)
  · exact (sublatticeSpinHalfOp2_cross_commute_op3 A).mul_left
      (sublatticeSpinHalfOp2_cross_commute_op3 A)
  · exact (sublatticeSpinHalfOp3_cross_commute A).mul_left
      (sublatticeSpinHalfOp3_cross_commute A)

/-! ## Sublattice Casimir commutes with the total spin generators and Casimir -/

/-- `Commute (Ŝ_A)² (Ŝ_tot^(1))`. Combines self-invariance (axis 1) with
the Ŝ_¬A^(1) commutativity above, since `Ŝ_tot^(1) = Ŝ_A^(1) + Ŝ_¬A^(1)`. -/
theorem sublatticeSpinHalfSquared_commute_totalSpinHalfOp1 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (totalSpinHalfOp1 Λ) := by
  rw [totalSpinHalfOp1_eq_sublattice_sum A]
  exact (sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp1 A).add_right
    (sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp1_complement A)

/-- `Commute (Ŝ_A)² (Ŝ_tot^(2))`. -/
theorem sublatticeSpinHalfSquared_commute_totalSpinHalfOp2 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (totalSpinHalfOp2 Λ) := by
  rw [totalSpinHalfOp2_eq_sublattice_sum A]
  exact (sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp2 A).add_right
    (sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp2_complement A)

/-- `Commute (Ŝ_A)² (Ŝ_tot^(3))`. -/
theorem sublatticeSpinHalfSquared_commute_totalSpinHalfOp3 (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (totalSpinHalfOp3 Λ) := by
  rw [totalSpinHalfOp3_eq_sublattice_sum A]
  exact (sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp3 A).add_right
    (sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp3_complement A)

/-- `Commute (Ŝ_A)² (Ŝ_tot)²`. The third pairwise commutativity needed
for the joint eigenbasis of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` (Tasaki §2.5
toy-Hamiltonian eigenvalue analysis). -/
theorem sublatticeSpinHalfSquared_commute_totalSpinHalfSquared (A : Λ → Bool) :
    Commute (sublatticeSpinHalfSquared A) (totalSpinHalfSquared Λ) := by
  unfold totalSpinHalfSquared
  have h1 := sublatticeSpinHalfSquared_commute_totalSpinHalfOp1 A
  have h2 := sublatticeSpinHalfSquared_commute_totalSpinHalfOp2 A
  have h3 := sublatticeSpinHalfSquared_commute_totalSpinHalfOp3 A
  exact ((h1.mul_right h1).add_right (h2.mul_right h2)).add_right (h3.mul_right h3)

/-! ## Sublattice ladder operators (raising / lowering on `A`) -/

/-- Sublattice raising operator on `A`: `Ŝ_A^+ := Σ_{x : A x} onSite x spinHalfOpPlus`.

Spin-`1/2` mirror of `sublatticeSpinSOpPlus` (PR #1085). -/
noncomputable def sublatticeSpinHalfOpPlus (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOpPlus else 0

/-- Sublattice lowering operator on `A`: `Ŝ_A^- := Σ_{x : A x} onSite x spinHalfOpMinus`. -/
noncomputable def sublatticeSpinHalfOpMinus (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOpMinus else 0

/-- `Ŝ_A^+ = Ŝ_A^(1) + i · Ŝ_A^(2)`. -/
theorem sublatticeSpinHalfOpPlus_eq_add (A : Λ → Bool) :
    sublatticeSpinHalfOpPlus A =
      sublatticeSpinHalfOp1 A + Complex.I • sublatticeSpinHalfOp2 A := by
  unfold sublatticeSpinHalfOpPlus sublatticeSpinHalfOp1 sublatticeSpinHalfOp2
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA, if_pos hA]
    rw [← onSite_smul, ← onSite_add, spinHalfOpPlus_eq_add]
  · cases h : A x
    · rw [if_neg, if_neg, if_neg]
      · rw [smul_zero, add_zero]
      · simp
      · simp
      · simp
    · exact absurd h hA

/-- `Ŝ_A^- = Ŝ_A^(1) − i · Ŝ_A^(2)`. -/
theorem sublatticeSpinHalfOpMinus_eq_sub (A : Λ → Bool) :
    sublatticeSpinHalfOpMinus A =
      sublatticeSpinHalfOp1 A - Complex.I • sublatticeSpinHalfOp2 A := by
  unfold sublatticeSpinHalfOpMinus sublatticeSpinHalfOp1 sublatticeSpinHalfOp2
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA, if_pos hA]
    rw [← onSite_smul, ← onSite_sub, spinHalfOpMinus_eq_sub]
  · cases h : A x
    · rw [if_neg, if_neg, if_neg]
      · rw [smul_zero, sub_zero]
      · simp
      · simp
      · simp
    · exact absurd h hA

/-- The total raising operator decomposes as a sum over sublattices:
`Ŝ^+_tot = Ŝ_A^+ + Ŝ_¬A^+`. -/
theorem totalSpinHalfOpPlus_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOpPlus Λ =
      sublatticeSpinHalfOpPlus A + sublatticeSpinHalfOpPlus (fun x => ! A x) := by
  unfold totalSpinHalfOpPlus sublatticeSpinHalfOpPlus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total lowering operator decomposes as a sum over sublattices:
`Ŝ^-_tot = Ŝ_A^- + Ŝ_¬A^-`. -/
theorem totalSpinHalfOpMinus_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOpMinus Λ =
      sublatticeSpinHalfOpMinus A + sublatticeSpinHalfOpMinus (fun x => ! A x) := by
  unfold totalSpinHalfOpMinus sublatticeSpinHalfOpMinus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-! ## Sublattice Cartan relations -/

/-- Sublattice Cartan relation: `[Ŝ_A^(3), Ŝ_A^+] = Ŝ_A^+`. Mirror of
spin-`S` PR #1088. -/
theorem sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOpPlus (A : Λ → Bool) :
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOpPlus A
        - sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOp3 A =
      sublatticeSpinHalfOpPlus A := by
  rw [sublatticeSpinHalfOpPlus_eq_add]
  have h31 := sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOp1 A
  have h23 := sublatticeSpinHalfOp2_commutator_sublatticeSpinHalfOp3 A
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  have hI2 : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
  have hkey : sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp1 A +
        Complex.I • (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp2 A) -
      (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp3 A +
        Complex.I • (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp3 A)) =
      (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp1 A -
        sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp3 A) -
      Complex.I • (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp3 A -
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp2 A) := by
    rw [smul_sub]; abel
  rw [hkey, h31, h23, smul_smul, hI2, neg_smul, one_smul, sub_neg_eq_add]
  abel

/-- Sublattice Cartan relation: `[Ŝ_A^(3), Ŝ_A^-] = -Ŝ_A^-`. -/
theorem sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOpMinus (A : Λ → Bool) :
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOpMinus A
        - sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOp3 A =
      -sublatticeSpinHalfOpMinus A := by
  rw [sublatticeSpinHalfOpMinus_eq_sub]
  have h31 := sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOp1 A
  have h23 := sublatticeSpinHalfOp2_commutator_sublatticeSpinHalfOp3 A
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  have hI2 : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
  have hkey : sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp1 A -
        Complex.I • (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp2 A) -
      (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp3 A -
        Complex.I • (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp3 A)) =
      (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp1 A -
        sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp3 A) +
      Complex.I • (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp3 A -
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp2 A) := by
    rw [smul_sub]; abel
  rw [hkey, h31, h23, smul_smul, hI2, neg_smul, one_smul]
  rw [show -sublatticeSpinHalfOp1 A = -(sublatticeSpinHalfOp1 A -
      Complex.I • sublatticeSpinHalfOp2 A) - Complex.I • sublatticeSpinHalfOp2 A
      from by abel]
  abel

/-- Total Cartan relation: `[Ŝ_tot^(3), Ŝ_A^+] = Ŝ_A^+`. -/
theorem totalSpinHalfOp3_commutator_sublatticeSpinHalfOpPlus (A : Λ → Bool) :
    totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A
        - sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ =
      sublatticeSpinHalfOpPlus A := by
  rw [totalSpinHalfOp3_eq_sublattice_sum A]
  rw [add_mul, mul_add]
  have h_self := sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOpPlus A
  have h_cross : sublatticeSpinHalfOp3 (fun x => ! A x) * sublatticeSpinHalfOpPlus A =
      sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOp3 (fun x => ! A x) := by
    rw [sublatticeSpinHalfOpPlus_eq_add]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [(sublatticeSpinHalfOp1_cross_commute_op3 A).symm.eq,
        (sublatticeSpinHalfOp2_cross_commute_op3 A).symm.eq]
  rw [h_cross]
  rw [show sublatticeSpinHalfOp3 A * sublatticeSpinHalfOpPlus A +
        sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOp3 (fun x => ! A x) -
      (sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOp3 A +
        sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOp3 (fun x => ! A x)) =
      sublatticeSpinHalfOp3 A * sublatticeSpinHalfOpPlus A -
        sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOp3 A from by abel]
  exact h_self

/-- Total Cartan relation: `[Ŝ_tot^(3), Ŝ_A^-] = -Ŝ_A^-`. -/
theorem totalSpinHalfOp3_commutator_sublatticeSpinHalfOpMinus (A : Λ → Bool) :
    totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A
        - sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ =
      -sublatticeSpinHalfOpMinus A := by
  rw [totalSpinHalfOp3_eq_sublattice_sum A]
  rw [add_mul, mul_add]
  have h_self := sublatticeSpinHalfOp3_commutator_sublatticeSpinHalfOpMinus A
  have h_cross : sublatticeSpinHalfOp3 (fun x => ! A x) * sublatticeSpinHalfOpMinus A =
      sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOp3 (fun x => ! A x) := by
    rw [sublatticeSpinHalfOpMinus_eq_sub]
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    rw [(sublatticeSpinHalfOp1_cross_commute_op3 A).symm.eq,
        (sublatticeSpinHalfOp2_cross_commute_op3 A).symm.eq]
  rw [h_cross]
  rw [show sublatticeSpinHalfOp3 A * sublatticeSpinHalfOpMinus A +
        sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOp3 (fun x => ! A x) -
      (sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOp3 A +
        sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOp3 (fun x => ! A x)) =
      sublatticeSpinHalfOp3 A * sublatticeSpinHalfOpMinus A -
        sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOp3 A from by abel]
  exact h_self

/-! ## Edge cases: empty sublattice -/

/-- `Ŝ_A^(α)` vanishes on the empty sublattice (`A = const false`). -/
theorem sublatticeSpinHalfOp1_const_false :
    sublatticeSpinHalfOp1 (Λ := Λ) (fun _ => false) = 0 := by
  unfold sublatticeSpinHalfOp1
  apply Finset.sum_eq_zero
  intro x _
  simp

theorem sublatticeSpinHalfOp2_const_false :
    sublatticeSpinHalfOp2 (Λ := Λ) (fun _ => false) = 0 := by
  unfold sublatticeSpinHalfOp2
  apply Finset.sum_eq_zero
  intro x _
  simp

theorem sublatticeSpinHalfOp3_const_false :
    sublatticeSpinHalfOp3 (Λ := Λ) (fun _ => false) = 0 := by
  unfold sublatticeSpinHalfOp3
  apply Finset.sum_eq_zero
  intro x _
  simp

theorem sublatticeSpinHalfSquared_const_false :
    sublatticeSpinHalfSquared (Λ := Λ) (fun _ => false) = 0 := by
  unfold sublatticeSpinHalfSquared
  rw [sublatticeSpinHalfOp1_const_false, sublatticeSpinHalfOp2_const_false,
      sublatticeSpinHalfOp3_const_false]
  simp

theorem sublatticeSpinHalfOpPlus_const_false :
    sublatticeSpinHalfOpPlus (Λ := Λ) (fun _ => false) = 0 := by
  unfold sublatticeSpinHalfOpPlus
  apply Finset.sum_eq_zero
  intro x _
  simp

theorem sublatticeSpinHalfOpMinus_const_false :
    sublatticeSpinHalfOpMinus (Λ := Λ) (fun _ => false) = 0 := by
  unfold sublatticeSpinHalfOpMinus
  apply Finset.sum_eq_zero
  intro x _
  simp

/-! ## Edge cases: full sublattice -/

/-- `Ŝ_A^(α)` equals the total `Ŝ_tot^(α)` for the full sublattice
(`A = const true`). -/
theorem sublatticeSpinHalfOp1_const_true :
    sublatticeSpinHalfOp1 (Λ := Λ) (fun _ => true) = totalSpinHalfOp1 Λ := by
  unfold sublatticeSpinHalfOp1 totalSpinHalfOp1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinHalfOp2_const_true :
    sublatticeSpinHalfOp2 (Λ := Λ) (fun _ => true) = totalSpinHalfOp2 Λ := by
  unfold sublatticeSpinHalfOp2 totalSpinHalfOp2
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinHalfOp3_const_true :
    sublatticeSpinHalfOp3 (Λ := Λ) (fun _ => true) = totalSpinHalfOp3 Λ := by
  unfold sublatticeSpinHalfOp3 totalSpinHalfOp3
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinHalfSquared_const_true :
    sublatticeSpinHalfSquared (Λ := Λ) (fun _ => true) = totalSpinHalfSquared Λ := by
  unfold sublatticeSpinHalfSquared totalSpinHalfSquared
  rw [sublatticeSpinHalfOp1_const_true, sublatticeSpinHalfOp2_const_true,
      sublatticeSpinHalfOp3_const_true]

theorem sublatticeSpinHalfOpPlus_const_true :
    sublatticeSpinHalfOpPlus (Λ := Λ) (fun _ => true) = totalSpinHalfOpPlus Λ := by
  unfold sublatticeSpinHalfOpPlus totalSpinHalfOpPlus
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem sublatticeSpinHalfOpMinus_const_true :
    sublatticeSpinHalfOpMinus (Λ := Λ) (fun _ => true) = totalSpinHalfOpMinus Λ := by
  unfold sublatticeSpinHalfOpMinus totalSpinHalfOpMinus
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-! ## Reverse identities -/

/-- `Ŝ_A^+ + Ŝ_A^- = 2 • Ŝ_A^(1)`. -/
theorem sublatticeSpinHalfOpPlus_add_sublatticeSpinHalfOpMinus (A : Λ → Bool) :
    sublatticeSpinHalfOpPlus A + sublatticeSpinHalfOpMinus A =
      (2 : ℂ) • sublatticeSpinHalfOp1 A := by
  rw [sublatticeSpinHalfOpPlus_eq_add, sublatticeSpinHalfOpMinus_eq_sub, two_smul]
  abel

/-- `Ŝ_A^+ - Ŝ_A^- = 2i • Ŝ_A^(2)`. -/
theorem sublatticeSpinHalfOpPlus_sub_sublatticeSpinHalfOpMinus (A : Λ → Bool) :
    sublatticeSpinHalfOpPlus A - sublatticeSpinHalfOpMinus A =
      (2 * Complex.I) • sublatticeSpinHalfOp2 A := by
  rw [sublatticeSpinHalfOpPlus_eq_add, sublatticeSpinHalfOpMinus_eq_sub]
  rw [show (2 * Complex.I : ℂ) = Complex.I + Complex.I from by ring]
  rw [add_smul]
  abel

/-! ## Sublattice axis squared as conjTranspose product -/

/-- `(Ŝ_A^(1))² = (Ŝ_A^(1))ᴴ * Ŝ_A^(1)`. Direct from Hermiticity. -/
theorem sublatticeSpinHalfOp1_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A =
      (sublatticeSpinHalfOp1 A).conjTranspose * sublatticeSpinHalfOp1 A := by
  rw [(sublatticeSpinHalfOp1_isHermitian A).eq]

theorem sublatticeSpinHalfOp2_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A =
      (sublatticeSpinHalfOp2 A).conjTranspose * sublatticeSpinHalfOp2 A := by
  rw [(sublatticeSpinHalfOp2_isHermitian A).eq]

theorem sublatticeSpinHalfOp3_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 A =
      (sublatticeSpinHalfOp3 A).conjTranspose * sublatticeSpinHalfOp3 A := by
  rw [(sublatticeSpinHalfOp3_isHermitian A).eq]

/-! ## Sublattice axis-1 / axis-3 matrix element realness -/

/-- The single-site spin-`1/2` axis-1 operator has real entries. -/
private theorem spinHalfOp1_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOp1 i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp1, pauliX]

/-- The single-site spin-`1/2` axis-3 operator has real entries. -/
private theorem spinHalfOp3_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOp3 i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp3, pauliZ]

/-- The on-site embedded `Ŝ^(1)` has real matrix elements. -/
theorem onSite_spinHalfOp1_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOp1 : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOp1_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]; simp

/-- The on-site embedded `Ŝ^(3)` has real matrix elements. -/
theorem onSite_spinHalfOp3_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOp3 : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOp3_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]; simp

/-- The sublattice axis-1 operator has real matrix elements. -/
theorem sublatticeSpinHalfOp1_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOp1 A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOp1
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOp1_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-- The sublattice axis-3 operator has real matrix elements. -/
theorem sublatticeSpinHalfOp3_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOp3 A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOp3
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOp3_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder matrix element realness -/

/-- The single-site spin-`1/2` raising operator has real entries. -/
private theorem spinHalfOpPlus_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOpPlus i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOpPlus]

/-- The single-site spin-`1/2` lowering operator has real entries. -/
private theorem spinHalfOpMinus_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOpMinus i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOpMinus]

/-- The on-site embedded `Ŝ^+` has real matrix elements. -/
theorem onSite_spinHalfOpPlus_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOpPlus : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOpPlus_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]
    simp

/-- The on-site embedded `Ŝ^-` has real matrix elements. -/
theorem onSite_spinHalfOpMinus_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOpMinus : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOpMinus_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]
    simp

/-- The sublattice raising operator has real matrix elements:
`((Ŝ_A^+) σ' σ).im = 0`. Spin-`1/2` mirror of γ-4 step 57. -/
theorem sublatticeSpinHalfOpPlus_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOpPlus A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOpPlus
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOpPlus_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-- The sublattice lowering operator has real matrix elements:
`((Ŝ_A^-) σ' σ).im = 0`. -/
theorem sublatticeSpinHalfOpMinus_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOpMinus A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOpMinus
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOpMinus_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder adjoint relations -/

/-- `(Ŝ_A^+)† = Ŝ_A^-`: the spin-`1/2` sublattice raising and lowering
operators are Hermitian conjugates. Mirror of γ-4 step 54. -/
theorem sublatticeSpinHalfOpPlus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A).conjTranspose = sublatticeSpinHalfOpMinus A := by
  unfold sublatticeSpinHalfOpPlus sublatticeSpinHalfOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSite_conjTranspose, spinHalfOpPlus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-- `(Ŝ_A^-)† = Ŝ_A^+`. -/
theorem sublatticeSpinHalfOpMinus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A).conjTranspose = sublatticeSpinHalfOpPlus A := by
  unfold sublatticeSpinHalfOpPlus sublatticeSpinHalfOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSite_conjTranspose, spinHalfOpMinus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder operators annihilate extremal states -/

/-- `Ŝ_A^+ · |0...0⟩ = 0`: the sublattice raising operator annihilates
the all-up basis vector. Spin-`1/2` mirror of γ-4 step 45. -/
theorem sublatticeSpinHalfOpPlus_mulVec_basisVec_zero (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
  unfold sublatticeSpinHalfOpPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    rw [onSite_spinHalfOpPlus_mulVec_basisVec]
    simp
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-- `Ŝ_A^- · |1...1⟩ = 0`: the sublattice lowering operator annihilates
the all-down basis vector. -/
theorem sublatticeSpinHalfOpMinus_mulVec_basisVec_one (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
  unfold sublatticeSpinHalfOpMinus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    rw [onSite_spinHalfOpMinus_mulVec_basisVec]
    simp
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-! ## Sublattice ladder operators shift the magnetization subspace -/

/-- `Ŝ_A^- · v ∈ magnetizationSubspace Λ (M − 1)` for `v ∈ magnetizationSubspace Λ M`.
Spin-`1/2` mirror of γ-4 step 48. -/
theorem sublatticeSpinHalfOpMinus_mulVec_mem_magnetizationSubspace_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (sublatticeSpinHalfOpMinus A).mulVec v ∈ magnetizationSubspace Λ (M - 1) := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  have h := totalSpinHalfOp3_commutator_sublatticeSpinHalfOpMinus A
  have hcomm : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A =
      sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ - sublatticeSpinHalfOpMinus A := by
    have hadd : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A =
        (totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A -
          sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ) +
        sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- `Ŝ_A^+ · v ∈ magnetizationSubspace Λ (M + 1)` for `v ∈ magnetizationSubspace Λ M`. -/
theorem sublatticeSpinHalfOpPlus_mulVec_mem_magnetizationSubspace_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (sublatticeSpinHalfOpPlus A).mulVec v ∈ magnetizationSubspace Λ (M + 1) := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  have h := totalSpinHalfOp3_commutator_sublatticeSpinHalfOpPlus A
  have hcomm : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A =
      sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ + sublatticeSpinHalfOpPlus A := by
    have hadd : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A =
        (totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A -
          sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ) +
        sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

end LatticeSystem.Quantum
