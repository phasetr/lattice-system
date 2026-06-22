import LatticeSystem.Quantum.TotalSpin
import LatticeSystem.Quantum.TotalSpin.Casimir
import LatticeSystem.Quantum.MagnetizationSubspaceCore
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinCore

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


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

end LatticeSystem.Quantum
