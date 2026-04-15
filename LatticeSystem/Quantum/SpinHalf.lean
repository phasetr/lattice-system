/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.Pauli

/-!
# Spin-1/2 operators following Tasaki §2.1

This module introduces the S = 1/2 spin operators

```
spinHalfOp1 := (1/2 : ℂ) • pauliX
spinHalfOp2 := (1/2 : ℂ) • pauliY
spinHalfOp3 := (1/2 : ℂ) • pauliZ
```

corresponding to Tasaki *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1, eq. (2.1.7) on p. 15. The Pauli convention
`σ^(α) = 2 · Ŝ^(α)` from eq. (2.1.8) on p. 15 is recorded as a
theorem.

We prove the four families of algebraic identities listed in Tasaki
at or just after eq. (2.1.7):

* Hermiticity of each `Ŝ^(α)`.
* `(Ŝ^(α))² = (1/4) · I`.
* Anticommutation `Ŝ^(α) Ŝ^(β) + Ŝ^(β) Ŝ^(α) = 0` for `α ≠ β`.
* The commutator identities `[Ŝ^(1), Ŝ^(2)] = i · Ŝ^(3)` and its
  cyclic permutations — the S = 1/2 instance of Tasaki eq. (2.1.1).
* The total spin identity `(Ŝ^(1))² + (Ŝ^(2))² + (Ŝ^(3))² = (3/4) · I`,
  i.e., the S = 1/2 case of the convention `Ŝ² = S(S+1) I`.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Definitions (Tasaki eq 2.1.7, p. 15) -/

/-- The S = 1/2 spin operator in the 1-direction: `Ŝ^(1) = σ^x / 2`. -/
noncomputable def spinHalfOp1 : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • pauliX

/-- The S = 1/2 spin operator in the 2-direction: `Ŝ^(2) = σ^y / 2`. -/
noncomputable def spinHalfOp2 : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • pauliY

/-- The S = 1/2 spin operator in the 3-direction: `Ŝ^(3) = σ^z / 2`. -/
noncomputable def spinHalfOp3 : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • pauliZ

/-! ## Pauli-spin relation (Tasaki eq 2.1.8, p. 15) -/

/-- Tasaki eq. (2.1.8): `σ^x = 2 · Ŝ^(1)`. -/
theorem pauliX_eq_two_smul_spinHalfOp1 :
    pauliX = (2 : ℂ) • spinHalfOp1 := by
  unfold spinHalfOp1
  rw [smul_smul]
  norm_num

/-- Tasaki eq. (2.1.8): `σ^y = 2 · Ŝ^(2)`. -/
theorem pauliY_eq_two_smul_spinHalfOp2 :
    pauliY = (2 : ℂ) • spinHalfOp2 := by
  unfold spinHalfOp2
  rw [smul_smul]
  norm_num

/-- Tasaki eq. (2.1.8): `σ^z = 2 · Ŝ^(3)`. -/
theorem pauliZ_eq_two_smul_spinHalfOp3 :
    pauliZ = (2 : ℂ) • spinHalfOp3 := by
  unfold spinHalfOp3
  rw [smul_smul]
  norm_num

/-! ## Hermiticity -/

private lemma star_one_half_complex : star ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
  simp

/-- `Ŝ^(1)` is Hermitian. -/
theorem spinHalfOp1_isHermitian : spinHalfOp1.IsHermitian := by
  unfold spinHalfOp1 Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, pauliX_isHermitian, star_one_half_complex]

/-- `Ŝ^(2)` is Hermitian. -/
theorem spinHalfOp2_isHermitian : spinHalfOp2.IsHermitian := by
  unfold spinHalfOp2 Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, pauliY_isHermitian, star_one_half_complex]

/-- `Ŝ^(3)` is Hermitian. -/
theorem spinHalfOp3_isHermitian : spinHalfOp3.IsHermitian := by
  unfold spinHalfOp3 Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, pauliZ_isHermitian, star_one_half_complex]

/-! ## Squared operators: `(Ŝ^(α))² = (1/4) · I` (Tasaki p. 15, below 2.1.8) -/

/-- `Ŝ^(1) · Ŝ^(1) = (1/4) · I`. -/
theorem spinHalfOp1_mul_self : spinHalfOp1 * spinHalfOp1 = (1 / 4 : ℂ) • 1 := by
  unfold spinHalfOp1
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliX_mul_self]
  congr 1
  norm_num

/-- `Ŝ^(2) · Ŝ^(2) = (1/4) · I`. -/
theorem spinHalfOp2_mul_self : spinHalfOp2 * spinHalfOp2 = (1 / 4 : ℂ) • 1 := by
  unfold spinHalfOp2
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliY_mul_self]
  congr 1
  norm_num

/-- `Ŝ^(3) · Ŝ^(3) = (1/4) · I`. -/
theorem spinHalfOp3_mul_self : spinHalfOp3 * spinHalfOp3 = (1 / 4 : ℂ) • 1 := by
  unfold spinHalfOp3
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliZ_mul_self]
  congr 1
  norm_num

/-! ## Anticommutation at distinct axes (Tasaki p. 15, below 2.1.8) -/

/-- `Ŝ^(1) · Ŝ^(2) + Ŝ^(2) · Ŝ^(1) = 0`. -/
theorem spinHalfOp1_anticomm_spinHalfOp2 :
    spinHalfOp1 * spinHalfOp2 + spinHalfOp2 * spinHalfOp1 = 0 := by
  unfold spinHalfOp1 spinHalfOp2
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_add, pauliX_anticomm_pauliY, smul_zero]

/-- `Ŝ^(2) · Ŝ^(3) + Ŝ^(3) · Ŝ^(2) = 0`. -/
theorem spinHalfOp2_anticomm_spinHalfOp3 :
    spinHalfOp2 * spinHalfOp3 + spinHalfOp3 * spinHalfOp2 = 0 := by
  unfold spinHalfOp2 spinHalfOp3
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_add, pauliY_anticomm_pauliZ, smul_zero]

/-- `Ŝ^(3) · Ŝ^(1) + Ŝ^(1) · Ŝ^(3) = 0`. -/
theorem spinHalfOp3_anticomm_spinHalfOp1 :
    spinHalfOp3 * spinHalfOp1 + spinHalfOp1 * spinHalfOp3 = 0 := by
  unfold spinHalfOp3 spinHalfOp1
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_add, pauliZ_anticomm_pauliX, smul_zero]

/-! ## Commutation relations (Tasaki eq 2.1.1, p. 13, S = 1/2 case) -/

private lemma pauliY_mul_pauliX : pauliY * pauliX = (-I) • pauliZ := by
  have h : pauliY * pauliX = -(pauliX * pauliY) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact pauliX_anticomm_pauliY
  rw [h, pauliX_mul_pauliY, neg_smul]

private lemma pauliZ_mul_pauliY : pauliZ * pauliY = (-I) • pauliX := by
  have h : pauliZ * pauliY = -(pauliY * pauliZ) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact pauliY_anticomm_pauliZ
  rw [h, pauliY_mul_pauliZ, neg_smul]

private lemma pauliX_mul_pauliZ : pauliX * pauliZ = (-I) • pauliY := by
  have h : pauliX * pauliZ = -(pauliZ * pauliX) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact pauliZ_anticomm_pauliX
  rw [h, pauliZ_mul_pauliX, neg_smul]

/-- `[Ŝ^(1), Ŝ^(2)] = i · Ŝ^(3)` (Tasaki eq 2.1.1, S = 1/2 case). -/
theorem spinHalfOp1_commutator_spinHalfOp2 :
    spinHalfOp1 * spinHalfOp2 - spinHalfOp2 * spinHalfOp1 = I • spinHalfOp3 := by
  unfold spinHalfOp1 spinHalfOp2 spinHalfOp3
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      pauliX_mul_pauliY, pauliY_mul_pauliX,
      smul_smul, smul_smul, ← sub_smul, smul_smul]
  congr 1
  ring

/-- `[Ŝ^(2), Ŝ^(3)] = i · Ŝ^(1)` (Tasaki eq 2.1.1, S = 1/2 case, cyclic). -/
theorem spinHalfOp2_commutator_spinHalfOp3 :
    spinHalfOp2 * spinHalfOp3 - spinHalfOp3 * spinHalfOp2 = I • spinHalfOp1 := by
  unfold spinHalfOp2 spinHalfOp3 spinHalfOp1
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      pauliY_mul_pauliZ, pauliZ_mul_pauliY,
      smul_smul, smul_smul, ← sub_smul, smul_smul]
  congr 1
  ring

/-- `[Ŝ^(3), Ŝ^(1)] = i · Ŝ^(2)` (Tasaki eq 2.1.1, S = 1/2 case, cyclic). -/
theorem spinHalfOp3_commutator_spinHalfOp1 :
    spinHalfOp3 * spinHalfOp1 - spinHalfOp1 * spinHalfOp3 = I • spinHalfOp2 := by
  unfold spinHalfOp3 spinHalfOp1 spinHalfOp2
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      pauliZ_mul_pauliX, pauliX_mul_pauliZ,
      smul_smul, smul_smul, ← sub_smul, smul_smul]
  congr 1
  ring

/-! ## Total spin squared (Tasaki convention `Ŝ² = S(S+1) I`, S = 1/2) -/

/-- `(Ŝ^(1))² + (Ŝ^(2))² + (Ŝ^(3))² = (3/4) · I`, i.e., `S(S+1)` with `S = 1/2`. -/
theorem spinHalf_total_spin_squared :
    spinHalfOp1 * spinHalfOp1 + spinHalfOp2 * spinHalfOp2 +
      spinHalfOp3 * spinHalfOp3 = (3 / 4 : ℂ) • 1 := by
  rw [spinHalfOp1_mul_self, spinHalfOp2_mul_self, spinHalfOp3_mul_self,
    ← add_smul, ← add_smul]
  congr 1
  norm_num

/-! ## Cyclic products `Ŝ^(α) Ŝ^(β) = (i/2) · Ŝ^(γ)` -/

/-- `Ŝ^(1) · Ŝ^(2) = (i/2) · Ŝ^(3)`. Corollary of `σ^x σ^y = i · σ^z`. -/
theorem spinHalfOp1_mul_spinHalfOp2 :
    spinHalfOp1 * spinHalfOp2 = (I / 2) • spinHalfOp3 := by
  unfold spinHalfOp1 spinHalfOp2 spinHalfOp3
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliX_mul_pauliY]
  congr 1
  ring

/-- `Ŝ^(2) · Ŝ^(3) = (i/2) · Ŝ^(1)`. -/
theorem spinHalfOp2_mul_spinHalfOp3 :
    spinHalfOp2 * spinHalfOp3 = (I / 2) • spinHalfOp1 := by
  unfold spinHalfOp1 spinHalfOp2 spinHalfOp3
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliY_mul_pauliZ]
  congr 1
  ring

/-- `Ŝ^(3) · Ŝ^(1) = (i/2) · Ŝ^(2)`. -/
theorem spinHalfOp3_mul_spinHalfOp1 :
    spinHalfOp3 * spinHalfOp1 = (I / 2) • spinHalfOp2 := by
  unfold spinHalfOp1 spinHalfOp2 spinHalfOp3
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliZ_mul_pauliX]
  congr 1
  ring

end LatticeSystem.Quantum
