import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinLadderPropertiesCore

/-!
# Spin-`1/2` sublattice ladder properties (annihilation, adjoint,
extremal states, magnetization shift, Cartan identity,
cross-sublattice commute)

Extracted from `SublatticeSpin.lean` (build-speed refactor).
This file contains the spin-`1/2` sublattice-ladder operator
analysis: when they annihilate, their adjoint relations,
extremal-state behaviour, magnetization-subspace shifts,
sublattice Cartan identity, and cross-sublattice commutativity.

Theorems are γ-4 step mirrors for the spin-`1/2` case.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Cartan identity for sublattice ladders (spin-`1/2`) -/

/-- Spin-`1/2` mirror of `sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq`:
`Ŝ_A^+·Ŝ_A^- = (Ŝ_A^(1))² + (Ŝ_A^(2))² + Ŝ_A^(3)`. -/
theorem sublatticeSpinHalfOpPlus_mul_sublatticeSpinHalfOpMinus_eq (A : Λ → Bool) :
    sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOpMinus A =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A +
        sublatticeSpinHalfOp3 A := by
  rw [sublatticeSpinHalfOpPlus_eq_add, sublatticeSpinHalfOpMinus_eq_sub]
  have hcomm := sublatticeSpinHalfOp1_commutator_sublatticeSpinHalfOp2 A
  set S1 := sublatticeSpinHalfOp1 A
  set S2 := sublatticeSpinHalfOp2 A
  set S3 := sublatticeSpinHalfOp3 A
  have hexp : (S1 + Complex.I • S2) * (S1 - Complex.I • S2) =
      S1 * S1 - Complex.I • (S1 * S2) + Complex.I • (S2 * S1) -
        Complex.I • Complex.I • (S2 * S2) := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]
    abel
  rw [hexp]
  rw [show (Complex.I : ℂ) • Complex.I • (S2 * S2) = -(S2 * S2) from by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]]
  have hcommS3 : Complex.I • (S2 * S1) - Complex.I • (S1 * S2) = S3 := by
    rw [← smul_sub]
    have hr : (S2 * S1) - (S1 * S2) = -(S1 * S2 - S2 * S1) := by abel
    rw [hr, hcomm, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have : S1 * S1 - Complex.I • (S1 * S2) + Complex.I • (S2 * S1) -
      -(S2 * S2) =
    S1 * S1 + S2 * S2 + (Complex.I • (S2 * S1) - Complex.I • (S1 * S2)) := by abel
  rw [this, hcommS3]

/-- Dual: spin-`1/2` mirror of `sublatticeSpinSOpMinus_mul_sublatticeSpinSOpPlus_eq`. -/
theorem sublatticeSpinHalfOpMinus_mul_sublatticeSpinHalfOpPlus_eq (A : Λ → Bool) :
    sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOpPlus A =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A -
        sublatticeSpinHalfOp3 A := by
  rw [sublatticeSpinHalfOpPlus_eq_add, sublatticeSpinHalfOpMinus_eq_sub]
  have hcomm := sublatticeSpinHalfOp1_commutator_sublatticeSpinHalfOp2 A
  set S1 := sublatticeSpinHalfOp1 A
  set S2 := sublatticeSpinHalfOp2 A
  set S3 := sublatticeSpinHalfOp3 A
  have hexp : (S1 - Complex.I • S2) * (S1 + Complex.I • S2) =
      S1 * S1 + Complex.I • (S1 * S2) - Complex.I • (S2 * S1) -
        Complex.I • Complex.I • (S2 * S2) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]
    abel
  rw [hexp]
  rw [show (Complex.I : ℂ) • Complex.I • (S2 * S2) = -(S2 * S2) from by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]]
  have hcommS3 : Complex.I • (S1 * S2) - Complex.I • (S2 * S1) = -S3 := by
    rw [← smul_sub, hcomm, smul_smul, Complex.I_mul_I, neg_one_smul]
  have : S1 * S1 + Complex.I • (S1 * S2) - Complex.I • (S2 * S1) -
      -(S2 * S2) =
    S1 * S1 + S2 * S2 + (Complex.I • (S1 * S2) - Complex.I • (S2 * S1)) := by abel
  rw [this, hcommS3]
  abel

/-- Cross-axis identity (spin-`1/2` mirror of γ-4 step 122):
`Ŝ_A^(1)·Ŝ_B^(1) + Ŝ_A^(2)·Ŝ_B^(2) = (1/2)(Ŝ_A^+·Ŝ_B^- + Ŝ_A^-·Ŝ_B^+)`. -/
theorem sublatticeSpinHalfOp1_mul_op1_add_op2_mul_op2_eq_ladder
    (A B : Λ → Bool) :
    sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 B +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 B =
      (1 / 2 : ℂ) • (sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOpMinus B +
          sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOpPlus B) := by
  rw [sublatticeSpinHalfOpPlus_eq_add, sublatticeSpinHalfOpMinus_eq_sub,
    sublatticeSpinHalfOpPlus_eq_add, sublatticeSpinHalfOpMinus_eq_sub]
  set S1A := sublatticeSpinHalfOp1 A
  set S2A := sublatticeSpinHalfOp2 A
  set S1B := sublatticeSpinHalfOp1 B
  set S2B := sublatticeSpinHalfOp2 B
  have hexp : (S1A + Complex.I • S2A) * (S1B - Complex.I • S2B) +
      (S1A - Complex.I • S2A) * (S1B + Complex.I • S2B) =
      (2 : ℂ) • (S1A * S1B + S2A * S2B) := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul, smul_add, two_smul]
    abel
  rw [hexp, smul_smul]
  norm_num

/-- Sublattice Cartan commutator: `[Ŝ_A^+, Ŝ_A^-] = 2 · Ŝ_A^(3)`. Spin-`1/2`
mirror of γ-4 step 106. -/
theorem sublatticeSpinHalfOpPlus_commutator_sublatticeSpinHalfOpMinus
    (A : Λ → Bool) :
    sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOpMinus A -
        sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOpPlus A =
      (2 : ℂ) • sublatticeSpinHalfOp3 A := by
  rw [sublatticeSpinHalfOpPlus_mul_sublatticeSpinHalfOpMinus_eq,
    sublatticeSpinHalfOpMinus_mul_sublatticeSpinHalfOpPlus_eq]
  rw [two_smul]
  abel

/-! ## Cross-sublattice commute for ladder operators (spin-`1/2`) -/

/-- Spin-`1/2` mirror of `sublatticeSpinSOpPlus_cross_commute`. -/
theorem sublatticeSpinHalfOpPlus_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOpPlus A)
      (sublatticeSpinHalfOpPlus (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOpPlus
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOpPlus spinHalfOpPlus

/-- Spin-`1/2` mirror of `sublatticeSpinSOpMinus_cross_commute`. -/
theorem sublatticeSpinHalfOpMinus_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOpMinus A)
      (sublatticeSpinHalfOpMinus (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOpMinus
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOpMinus spinHalfOpMinus

/-- Spin-`1/2` mirror of `sublatticeSpinSOpPlus_cross_commute_minus`. -/
theorem sublatticeSpinHalfOpPlus_cross_commute_minus (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOpPlus A)
      (sublatticeSpinHalfOpMinus (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOpPlus sublatticeSpinHalfOpMinus
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOpPlus spinHalfOpMinus

/-- Spin-`1/2` mirror of `sublatticeSpinSOpMinus_cross_commute_plus`. -/
theorem sublatticeSpinHalfOpMinus_cross_commute_plus (A : Λ → Bool) :
    Commute (sublatticeSpinHalfOpMinus A)
      (sublatticeSpinHalfOpPlus (fun x => ! A x)) := by
  unfold sublatticeSpinHalfOpMinus sublatticeSpinHalfOpPlus
  exact sublatticeSpinHalfOpGeneric_cross_commute A spinHalfOpMinus spinHalfOpPlus


end LatticeSystem.Quantum
