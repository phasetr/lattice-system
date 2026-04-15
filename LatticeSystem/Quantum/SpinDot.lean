/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin

/-!
# Two-site spin inner product (Tasaki §2.2 eq (2.2.16))

For any two lattice sites `x, y : Λ`, define the two-site inner
product

```
Ŝ_x · Ŝ_y := Ŝ_x^(1) Ŝ_y^(1) + Ŝ_x^(2) Ŝ_y^(2) + Ŝ_x^(3) Ŝ_y^(3).
```

This module formalizes Tasaki *Physics and Mathematics of Quantum
Many-Body Systems*, §2.2, eq. (2.2.16), which rewrites `Ŝ_x · Ŝ_y`
(for `S = 1/2`) in terms of the raising/lowering operators:

```
Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^(3) Ŝ_y^(3).
```
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Two-site spin inner product:
`Ŝ_x · Ŝ_y := Σ_{α=1,2,3} onSite x Ŝ^(α) · onSite y Ŝ^(α)`. -/
noncomputable def spinHalfDot (x y : Λ) : ManyBodyOp Λ :=
  onSite x spinHalfOp1 * onSite y spinHalfOp1 +
    onSite x spinHalfOp2 * onSite y spinHalfOp2 +
    onSite x spinHalfOp3 * onSite y spinHalfOp3

/-- The raising/lowering decomposition (Tasaki eq (2.2.16), S = 1/2):
`Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^(3) Ŝ_y^(3)`. -/
theorem spinHalfDot_eq_plus_minus (x y : Λ) :
    (spinHalfDot x y : ManyBodyOp Λ) =
      (1 / 2 : ℂ) •
        (onSite x spinHalfOpPlus * onSite y spinHalfOpMinus +
          onSite x spinHalfOpMinus * onSite y spinHalfOpPlus) +
        onSite x spinHalfOp3 * onSite y spinHalfOp3 := by
  unfold spinHalfDot
  rw [spinHalfOpPlus_eq_add, spinHalfOpMinus_eq_sub]
  simp only [onSite_add, onSite_sub, onSite_smul]
  set a1 := (onSite x spinHalfOp1 : ManyBodyOp Λ)
  set a2 := (onSite x spinHalfOp2 : ManyBodyOp Λ)
  set b1 := (onSite y spinHalfOp1 : ManyBodyOp Λ)
  set b2 := (onSite y spinHalfOp2 : ManyBodyOp Λ)
  -- Expand each factor
  have e1 : (a1 + Complex.I • a2) * (b1 - Complex.I • b2) =
      a1 * b1 + a2 * b2 + (Complex.I • (a2 * b1) - Complex.I • (a1 * b2)) := by
    rw [add_mul, mul_sub, mul_sub]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel
  have e2 : (a1 - Complex.I • a2) * (b1 + Complex.I • b2) =
      a1 * b1 + a2 * b2 - (Complex.I • (a2 * b1) - Complex.I • (a1 * b2)) := by
    rw [sub_mul, mul_add, mul_add]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel
  rw [e1, e2]
  have key : ∀ (p r : ManyBodyOp Λ),
      (p + r) + (p - r) = (2 : ℂ) • p := by
    intros p r
    rw [two_smul]; abel
  set p : ManyBodyOp Λ := a1 * b1 + a2 * b2 with hp
  set r : ManyBodyOp Λ := Complex.I • (a2 * b1) - Complex.I • (a1 * b2) with hr
  rw [key p r, smul_smul]
  norm_num

end LatticeSystem.Quantum
