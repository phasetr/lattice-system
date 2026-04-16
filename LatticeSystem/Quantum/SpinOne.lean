/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-!
# Spin-1 operators following Tasaki §2.1

This module introduces the `S = 1` spin operators as `3 × 3` complex
matrices per Tasaki *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1, eq. (2.1.9) on p. 15:

```
spinOneOp1 = (1/√2) · !![0, 1, 0; 1, 0, 1; 0, 1, 0]
spinOneOp2 = (1/√2) · !![0, -i, 0; i, 0, -i; 0, i, 0]
spinOneOp3 =          !![1, 0, 0; 0, 0, 0; 0, 0, -1]
```

We prove:

* Hermiticity of each `Ŝ^(α)`.
* The commutation relations `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` for
  `(α, β, γ)` cyclic — the `S = 1` case of Tasaki eq. (2.1.1).
* The total spin identity `(Ŝ^(1))² + (Ŝ^(2))² + (Ŝ^(3))² = 2 · I`,
  i.e. the `S = 1` case of `Ŝ² = S(S+1) I`.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-- Convenience scalar `1 / √2 ∈ ℂ` appearing in the S = 1 spin-1
and spin-2 operators. Exposed publicly so that downstream files can
`unfold` it when relating Hermitian/anti-Hermitian spin operators
(e.g. `Ŝ^± = Ŝ^(1) ± i·Ŝ^(2)` for S = 1). -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℂ))⁻¹

/-- `1/√2` is real, i.e. self-conjugate. -/
private lemma star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  unfold invSqrt2
  simp [star_inv₀]

/-- `(1/√2) * (1/√2) = 1/2`. -/
private lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = (1 / 2 : ℂ) := by
  unfold invSqrt2
  rw [← mul_inv]
  rw [show ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = (2 : ℂ) from by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num]
  norm_num

/-- The squared form: `(1/√2)^2 = 1/2`. Convenient for use after `ring_nf`. -/
private lemma invSqrt2_sq : invSqrt2 ^ 2 = (1 / 2 : ℂ) := by
  rw [sq]; exact invSqrt2_mul_self

/-! ## Definitions (Tasaki eq 2.1.9, p. 15) -/

/-- The S = 1 spin operator in the 1-direction. -/
noncomputable def spinOneOp1 : Matrix (Fin 3) (Fin 3) ℂ :=
  invSqrt2 • !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- The S = 1 spin operator in the 2-direction. -/
noncomputable def spinOneOp2 : Matrix (Fin 3) (Fin 3) ℂ :=
  invSqrt2 • !![0, -I, 0; I, 0, -I; 0, I, 0]

/-- The S = 1 spin operator in the 3-direction. -/
def spinOneOp3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 0, 0; 0, 0, -1]

/-! ## Hermiticity -/

/-- `Ŝ^(1)` (S = 1) is Hermitian. -/
theorem spinOneOp1_isHermitian : spinOneOp1.IsHermitian := by
  unfold spinOneOp1 Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, star_invSqrt2]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]

/-- `Ŝ^(2)` (S = 1) is Hermitian. -/
theorem spinOneOp2_isHermitian : spinOneOp2.IsHermitian := by
  unfold spinOneOp2 Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, star_invSqrt2]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]

/-- `Ŝ^(3)` (S = 1) is Hermitian. -/
theorem spinOneOp3_isHermitian : spinOneOp3.IsHermitian := by
  unfold spinOneOp3 Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]

/-! ## Squared single-axis spin operators (S = 1) -/

/-- `(Ŝ^(1))² = (1/2) · !![1,0,1; 0,2,0; 1,0,1]`. Public-form helper
for proving `Û^(1)_π = û_1` from the closed-form rotation. -/
theorem spinOneOp1_mul_self :
    spinOneOp1 * spinOneOp1 =
      (1 / 2 : ℂ) • !![1, 0, 1; 0, 2, 0; 1, 0, 1] := by
  unfold spinOneOp1
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three]
     <;> ring_nf
     <;> simp only [invSqrt2_sq]
     <;> ring)

/-- `(Ŝ^(2))² = (1/2) · !![1,0,-1; 0,2,0; -1,0,1]`. -/
theorem spinOneOp2_mul_self :
    spinOneOp2 * spinOneOp2 =
      (1 / 2 : ℂ) • !![1, 0, -1; 0, 2, 0; -1, 0, 1] := by
  unfold spinOneOp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three]
     <;> ring_nf
     <;> simp only [invSqrt2_sq, Complex.I_sq]
     <;> ring)

/-! ## Total spin (Tasaki convention `Ŝ² = S(S+1) I`, S = 1) -/

/-- `(Ŝ^(1))² + (Ŝ^(2))² + (Ŝ^(3))² = 2 · I`. -/
theorem spinOne_total_spin_squared :
    spinOneOp1 * spinOneOp1 + spinOneOp2 * spinOneOp2 +
      spinOneOp3 * spinOneOp3 = (2 : ℂ) • 1 := by
  unfold spinOneOp1 spinOneOp2 spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.add_apply]
     try ring_nf
     try simp only [Complex.I_sq, invSqrt2_sq]
     try ring)

/-! ## Commutation relations (Tasaki eq 2.1.1, p. 13, S = 1 case) -/

/-- `[Ŝ^(1), Ŝ^(2)] = i · Ŝ^(3)`. -/
theorem spinOneOp1_commutator_spinOneOp2 :
    spinOneOp1 * spinOneOp2 - spinOneOp2 * spinOneOp1 = I • spinOneOp3 := by
  unfold spinOneOp1 spinOneOp2 spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.sub_apply]
     try ring_nf
     try simp only [invSqrt2_sq]
     try ring)

/-- `[Ŝ^(2), Ŝ^(3)] = i · Ŝ^(1)`. -/
theorem spinOneOp2_commutator_spinOneOp3 :
    spinOneOp2 * spinOneOp3 - spinOneOp3 * spinOneOp2 = I • spinOneOp1 := by
  unfold spinOneOp1 spinOneOp2 spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.sub_apply]
     try ring_nf
     try simp only [Complex.I_sq, invSqrt2_sq]
     try ring)

/-- `[Ŝ^(3), Ŝ^(1)] = i · Ŝ^(2)`. -/
theorem spinOneOp3_commutator_spinOneOp1 :
    spinOneOp3 * spinOneOp1 - spinOneOp1 * spinOneOp3 = I • spinOneOp2 := by
  unfold spinOneOp1 spinOneOp2 spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.sub_apply]
     try ring_nf
     try simp only [Complex.I_sq]
     try ring)

end LatticeSystem.Quantum
