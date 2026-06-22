import LatticeSystem.Quantum.SpinS.SublatticeSpin

/-!
# Sublattice spin ladder operators and Cartan relations (foundation)

Foundational layer extracted from `SublatticeSpinLadderDef.lean` for build speed.
This file defines the sublattice ladder operators (raising / lowering on a sublattice `A`)
and proves the sublattice Cartan relations among them.

The empty/full sublattice edge cases, the reverse identities, and the sublattice axis
squared as a `conjTranspose` product are kept in the capstone module
`SublatticeSpinLadderDef.lean`.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

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

end LatticeSystem.Quantum
