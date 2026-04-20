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

/-- Symmetry: `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x`. For `x = y` this is trivial;
for `x ≠ y` the site-embedded operators commute
(`onSite_mul_onSite_of_ne`). -/
theorem spinHalfDot_comm (x y : Λ) :
    (spinHalfDot x y : ManyBodyOp Λ) = spinHalfDot y x := by
  unfold spinHalfDot
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [onSite_mul_onSite_of_ne hxy spinHalfOp1 spinHalfOp1,
      onSite_mul_onSite_of_ne hxy spinHalfOp2 spinHalfOp2,
      onSite_mul_onSite_of_ne hxy spinHalfOp3 spinHalfOp3]

/-- Same-site dot product: `Ŝ_x · Ŝ_x = (3/4) · 1` (the S = 1/2
`S(S+1) = 3/4` identity, lifted to the many-body space). -/
theorem spinHalfDot_self (x : Λ) :
    (spinHalfDot x x : ManyBodyOp Λ) = (3 / 4 : ℂ) • 1 := by
  unfold spinHalfDot
  rw [onSite_mul_onSite_same, onSite_mul_onSite_same, onSite_mul_onSite_same]
  rw [spinHalfOp1_mul_self, spinHalfOp2_mul_self, spinHalfOp3_mul_self]
  rw [← onSite_add, ← onSite_add]
  rw [show ((1 / 4 : ℂ) • 1 + (1 / 4 : ℂ) • 1 + (1 / 4 : ℂ) • 1 : Matrix (Fin 2) (Fin 2) ℂ)
        = (3 / 4 : ℂ) • 1 from by
    rw [← add_smul, ← add_smul]; norm_num]
  rw [onSite_smul, onSite_one]

/-- `Ŝ_x · Ŝ_y` is Hermitian: for `x = y`, it reduces to the scalar
`(3/4)·1`; for `x ≠ y`, each of the three axis terms is a product of
commuting site embeddings of Hermitian single-site operators. -/
theorem spinHalfDot_isHermitian (x y : Λ) :
    (spinHalfDot x y : ManyBodyOp Λ).IsHermitian := by
  by_cases hxy : x = y
  · subst hxy
    rw [spinHalfDot_self]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul,
      show star ((3 / 4 : ℂ)) = (3 / 4 : ℂ) from by simp,
      Matrix.conjTranspose_one]
  · unfold spinHalfDot
    refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
    · exact Matrix.IsHermitian.mul_of_commute
        (onSite_isHermitian x spinHalfOp1_isHermitian)
        (onSite_isHermitian y spinHalfOp1_isHermitian)
        (onSite_mul_onSite_of_ne hxy _ _)
    · exact Matrix.IsHermitian.mul_of_commute
        (onSite_isHermitian x spinHalfOp2_isHermitian)
        (onSite_isHermitian y spinHalfOp2_isHermitian)
        (onSite_mul_onSite_of_ne hxy _ _)
    · exact Matrix.IsHermitian.mul_of_commute
        (onSite_isHermitian x spinHalfOp3_isHermitian)
        (onSite_isHermitian y spinHalfOp3_isHermitian)
        (onSite_mul_onSite_of_ne hxy _ _)

/-! ## Squared-sum decomposition (Tasaki eq (2.2.18)) -/

/-- The two-site total spin squared: `(Ŝ_x + Ŝ_y)²`, i.e.
`Σ_α (Ŝ_x^(α) + Ŝ_y^(α))²`. -/
noncomputable def spinHalfPairSpinSq (x y : Λ) : ManyBodyOp Λ :=
  (onSite x spinHalfOp1 + onSite y spinHalfOp1) *
    (onSite x spinHalfOp1 + onSite y spinHalfOp1) +
    (onSite x spinHalfOp2 + onSite y spinHalfOp2) *
      (onSite x spinHalfOp2 + onSite y spinHalfOp2) +
    (onSite x spinHalfOp3 + onSite y spinHalfOp3) *
      (onSite x spinHalfOp3 + onSite y spinHalfOp3)

/-- Site embeddings of the *same* operator at any two sites commute,
regardless of whether the sites coincide. -/
private lemma onSite_mul_onSite_self_comm (x y : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite x A : ManyBodyOp Λ) * onSite y A = onSite y A * onSite x A := by
  by_cases hxy : x = y
  · subst hxy; rfl
  · exact onSite_mul_onSite_of_ne hxy A A

/-! ## SU(2) invariance (partial, Tasaki eq (2.2.17)) -/

/-- The Leibniz rule for commutators of products: `[A·B, T] = A·[B,T] + [A,T]·B`. -/
private lemma leibniz_commutator (A B T : ManyBodyOp Λ) :
    A * B * T - T * (A * B) = A * (B * T - T * B) + (A * T - T * A) * B := by
  rw [mul_sub, sub_mul]
  have h1 : A * (T * B) = A * T * B := (mul_assoc A T B).symm
  have h2 : A * B * T = A * (B * T) := mul_assoc A B T
  have h3 : T * (A * B) = T * A * B := (mul_assoc T A B).symm
  rw [h1, h2, h3]
  abel

/-- SU(2) invariance at axis 3: `[Ŝ_x · Ŝ_y, Ŝ_tot^(3)] = 0`. This is the
axis-3 case of Tasaki eq. (2.2.17). -/
theorem spinHalfDot_commutator_totalSpinHalfOp3 (x y : Λ) :
    spinHalfDot x y * totalSpinHalfOp3 Λ - totalSpinHalfOp3 Λ * spinHalfDot x y = 0 := by
  unfold spinHalfDot totalSpinHalfOp3
  set T := (∑ z : Λ, onSite z spinHalfOp3 : ManyBodyOp Λ)
  -- Distribute the commutator over the α-sum in spinHalfDot
  have distrib : ∀ (A B C : ManyBodyOp Λ),
      (A + B + C) * T - T * (A + B + C) = (A * T - T * A) + (B * T - T * B) + (C * T - T * C) := by
    intros A B C
    rw [add_mul, add_mul, mul_add, mul_add]; abel
  rw [distrib]
  set a1 := (onSite x spinHalfOp1 * onSite y spinHalfOp1 : ManyBodyOp Λ)
  set a2 := (onSite x spinHalfOp2 * onSite y spinHalfOp2 : ManyBodyOp Λ)
  set a3 := (onSite x spinHalfOp3 * onSite y spinHalfOp3 : ManyBodyOp Λ)
  -- Compute each commutator via Leibniz
  have h1 : a1 * T - T * a1 =
      onSite x spinHalfOp1 *
          onSite y (spinHalfOp1 * spinHalfOp3 - spinHalfOp3 * spinHalfOp1) +
        onSite x (spinHalfOp1 * spinHalfOp3 - spinHalfOp3 * spinHalfOp1) *
          onSite y spinHalfOp1 := by
    change (onSite x spinHalfOp1) * (onSite y spinHalfOp1) * T
        - T * ((onSite x spinHalfOp1) * (onSite y spinHalfOp1)) = _
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp1 spinHalfOp3,
        onSite_commutator_totalOnSite Λ x spinHalfOp1 spinHalfOp3]
  have h2 : a2 * T - T * a2 =
      onSite x spinHalfOp2 *
          onSite y (spinHalfOp2 * spinHalfOp3 - spinHalfOp3 * spinHalfOp2) +
        onSite x (spinHalfOp2 * spinHalfOp3 - spinHalfOp3 * spinHalfOp2) *
          onSite y spinHalfOp2 := by
    change (onSite x spinHalfOp2) * (onSite y spinHalfOp2) * T
        - T * ((onSite x spinHalfOp2) * (onSite y spinHalfOp2)) = _
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp2 spinHalfOp3,
        onSite_commutator_totalOnSite Λ x spinHalfOp2 spinHalfOp3]
  have h3 : a3 * T - T * a3 = 0 := by
    change (onSite x spinHalfOp3) * (onSite y spinHalfOp3) * T
        - T * ((onSite x spinHalfOp3) * (onSite y spinHalfOp3)) = 0
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp3 spinHalfOp3,
        onSite_commutator_totalOnSite Λ x spinHalfOp3 spinHalfOp3]
    rw [sub_self]
    simp [onSite_zero]
  rw [h1, h2, h3]
  -- Substitute the single-site commutators with their known values
  rw [show spinHalfOp1 * spinHalfOp3 - spinHalfOp3 * spinHalfOp1 =
      -(Complex.I • spinHalfOp2) from by
    rw [show spinHalfOp1 * spinHalfOp3 - spinHalfOp3 * spinHalfOp1 =
        -(spinHalfOp3 * spinHalfOp1 - spinHalfOp1 * spinHalfOp3) from by abel,
      spinHalfOp3_commutator_spinHalfOp1]]
  rw [spinHalfOp2_commutator_spinHalfOp3]
  rw [onSite_smul, onSite_smul]
  rw [show onSite x (-(Complex.I • spinHalfOp2)) =
      -(Complex.I • onSite x spinHalfOp2) from by
    rw [show -(Complex.I • spinHalfOp2) = (-Complex.I) • spinHalfOp2 from by
      rw [neg_smul]]
    rw [onSite_smul]
    rw [neg_smul]]
  rw [show onSite y (-(Complex.I • spinHalfOp2)) =
      -(Complex.I • onSite y spinHalfOp2) from by
    rw [show -(Complex.I • spinHalfOp2) = (-Complex.I) • spinHalfOp2 from by
      rw [neg_smul]]
    rw [onSite_smul]
    rw [neg_smul]]
  -- Now the terms should cancel
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- SU(2) invariance at axis 1: `[Ŝ_x · Ŝ_y, Ŝ_tot^(1)] = 0`. -/
theorem spinHalfDot_commutator_totalSpinHalfOp1 (x y : Λ) :
    spinHalfDot x y * totalSpinHalfOp1 Λ - totalSpinHalfOp1 Λ * spinHalfDot x y = 0 := by
  unfold spinHalfDot totalSpinHalfOp1
  set T := (∑ z : Λ, onSite z spinHalfOp1 : ManyBodyOp Λ)
  have distrib : ∀ (A B C : ManyBodyOp Λ),
      (A + B + C) * T - T * (A + B + C) =
        (A * T - T * A) + (B * T - T * B) + (C * T - T * C) := by
    intros A B C
    rw [add_mul, add_mul, mul_add, mul_add]; abel
  rw [distrib]
  set a1 := (onSite x spinHalfOp1 * onSite y spinHalfOp1 : ManyBodyOp Λ)
  set a2 := (onSite x spinHalfOp2 * onSite y spinHalfOp2 : ManyBodyOp Λ)
  set a3 := (onSite x spinHalfOp3 * onSite y spinHalfOp3 : ManyBodyOp Λ)
  have h1 : a1 * T - T * a1 = 0 := by
    change (onSite x spinHalfOp1) * (onSite y spinHalfOp1) * T
        - T * ((onSite x spinHalfOp1) * (onSite y spinHalfOp1)) = 0
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp1 spinHalfOp1,
        onSite_commutator_totalOnSite Λ x spinHalfOp1 spinHalfOp1]
    rw [sub_self]
    simp [onSite_zero]
  have h2 : a2 * T - T * a2 =
      onSite x spinHalfOp2 *
          onSite y (spinHalfOp2 * spinHalfOp1 - spinHalfOp1 * spinHalfOp2) +
        onSite x (spinHalfOp2 * spinHalfOp1 - spinHalfOp1 * spinHalfOp2) *
          onSite y spinHalfOp2 := by
    change (onSite x spinHalfOp2) * (onSite y spinHalfOp2) * T
        - T * ((onSite x spinHalfOp2) * (onSite y spinHalfOp2)) = _
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp2 spinHalfOp1,
        onSite_commutator_totalOnSite Λ x spinHalfOp2 spinHalfOp1]
  have h3 : a3 * T - T * a3 =
      onSite x spinHalfOp3 *
          onSite y (spinHalfOp3 * spinHalfOp1 - spinHalfOp1 * spinHalfOp3) +
        onSite x (spinHalfOp3 * spinHalfOp1 - spinHalfOp1 * spinHalfOp3) *
          onSite y spinHalfOp3 := by
    change (onSite x spinHalfOp3) * (onSite y spinHalfOp3) * T
        - T * ((onSite x spinHalfOp3) * (onSite y spinHalfOp3)) = _
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp3 spinHalfOp1,
        onSite_commutator_totalOnSite Λ x spinHalfOp3 spinHalfOp1]
  rw [h1, h2, h3]
  rw [show spinHalfOp2 * spinHalfOp1 - spinHalfOp1 * spinHalfOp2 =
      -(Complex.I • spinHalfOp3) from by
    rw [show spinHalfOp2 * spinHalfOp1 - spinHalfOp1 * spinHalfOp2 =
        -(spinHalfOp1 * spinHalfOp2 - spinHalfOp2 * spinHalfOp1) from by abel,
      spinHalfOp1_commutator_spinHalfOp2]]
  rw [spinHalfOp3_commutator_spinHalfOp1]
  rw [show onSite x (-(Complex.I • spinHalfOp3)) =
      -(Complex.I • onSite x spinHalfOp3) from by
    rw [show -(Complex.I • spinHalfOp3) = (-Complex.I) • spinHalfOp3 from by
      rw [neg_smul]]
    rw [onSite_smul, neg_smul]]
  rw [show onSite y (-(Complex.I • spinHalfOp3)) =
      -(Complex.I • onSite y spinHalfOp3) from by
    rw [show -(Complex.I • spinHalfOp3) = (-Complex.I) • spinHalfOp3 from by
      rw [neg_smul]]
    rw [onSite_smul, neg_smul]]
  rw [onSite_smul, onSite_smul]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc]
  abel

/-- SU(2) invariance at axis 2: `[Ŝ_x · Ŝ_y, Ŝ_tot^(2)] = 0`. -/
theorem spinHalfDot_commutator_totalSpinHalfOp2 (x y : Λ) :
    spinHalfDot x y * totalSpinHalfOp2 Λ - totalSpinHalfOp2 Λ * spinHalfDot x y = 0 := by
  unfold spinHalfDot totalSpinHalfOp2
  set T := (∑ z : Λ, onSite z spinHalfOp2 : ManyBodyOp Λ)
  have distrib : ∀ (A B C : ManyBodyOp Λ),
      (A + B + C) * T - T * (A + B + C) =
        (A * T - T * A) + (B * T - T * B) + (C * T - T * C) := by
    intros A B C
    rw [add_mul, add_mul, mul_add, mul_add]; abel
  rw [distrib]
  set a1 := (onSite x spinHalfOp1 * onSite y spinHalfOp1 : ManyBodyOp Λ)
  set a2 := (onSite x spinHalfOp2 * onSite y spinHalfOp2 : ManyBodyOp Λ)
  set a3 := (onSite x spinHalfOp3 * onSite y spinHalfOp3 : ManyBodyOp Λ)
  have h1 : a1 * T - T * a1 =
      onSite x spinHalfOp1 *
          onSite y (spinHalfOp1 * spinHalfOp2 - spinHalfOp2 * spinHalfOp1) +
        onSite x (spinHalfOp1 * spinHalfOp2 - spinHalfOp2 * spinHalfOp1) *
          onSite y spinHalfOp1 := by
    change (onSite x spinHalfOp1) * (onSite y spinHalfOp1) * T
        - T * ((onSite x spinHalfOp1) * (onSite y spinHalfOp1)) = _
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp1 spinHalfOp2,
        onSite_commutator_totalOnSite Λ x spinHalfOp1 spinHalfOp2]
  have h2 : a2 * T - T * a2 = 0 := by
    change (onSite x spinHalfOp2) * (onSite y spinHalfOp2) * T
        - T * ((onSite x spinHalfOp2) * (onSite y spinHalfOp2)) = 0
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp2 spinHalfOp2,
        onSite_commutator_totalOnSite Λ x spinHalfOp2 spinHalfOp2]
    rw [sub_self]
    simp [onSite_zero]
  have h3 : a3 * T - T * a3 =
      onSite x spinHalfOp3 *
          onSite y (spinHalfOp3 * spinHalfOp2 - spinHalfOp2 * spinHalfOp3) +
        onSite x (spinHalfOp3 * spinHalfOp2 - spinHalfOp2 * spinHalfOp3) *
          onSite y spinHalfOp3 := by
    change (onSite x spinHalfOp3) * (onSite y spinHalfOp3) * T
        - T * ((onSite x spinHalfOp3) * (onSite y spinHalfOp3)) = _
    rw [leibniz_commutator]
    rw [onSite_commutator_totalOnSite Λ y spinHalfOp3 spinHalfOp2,
        onSite_commutator_totalOnSite Λ x spinHalfOp3 spinHalfOp2]
  rw [h1, h2, h3]
  rw [spinHalfOp1_commutator_spinHalfOp2]
  rw [show spinHalfOp3 * spinHalfOp2 - spinHalfOp2 * spinHalfOp3 =
      -(Complex.I • spinHalfOp1) from by
    rw [show spinHalfOp3 * spinHalfOp2 - spinHalfOp2 * spinHalfOp3 =
        -(spinHalfOp2 * spinHalfOp3 - spinHalfOp3 * spinHalfOp2) from by abel,
      spinHalfOp2_commutator_spinHalfOp3]]
  rw [onSite_smul, onSite_smul]
  rw [show onSite x (-(Complex.I • spinHalfOp1)) =
      -(Complex.I • onSite x spinHalfOp1) from by
    rw [show -(Complex.I • spinHalfOp1) = (-Complex.I) • spinHalfOp1 from by
      rw [neg_smul]]
    rw [onSite_smul, neg_smul]]
  rw [show onSite y (-(Complex.I • spinHalfOp1)) =
      -(Complex.I • onSite y spinHalfOp1) from by
    rw [show -(Complex.I • spinHalfOp1) = (-Complex.I) • spinHalfOp1 from by
      rw [neg_smul]]
    rw [onSite_smul, neg_smul]]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc]
  abel

/-- SU(2) invariance with the raising operator:
`[Ŝ_x · Ŝ_y, Ŝ^+_tot] = 0`. -/
theorem spinHalfDot_commutator_totalSpinHalfOpPlus (x y : Λ) :
    spinHalfDot x y * totalSpinHalfOpPlus Λ -
        totalSpinHalfOpPlus Λ * spinHalfDot x y = 0 := by
  rw [totalSpinHalfOpPlus_eq_add, mul_add, add_mul]
  rw [mul_smul_comm, smul_mul_assoc]
  have h1 := spinHalfDot_commutator_totalSpinHalfOp1 x y
  have h2 := spinHalfDot_commutator_totalSpinHalfOp2 x y
  rw [show spinHalfDot x y * totalSpinHalfOp1 Λ +
            Complex.I • (spinHalfDot x y * totalSpinHalfOp2 Λ) -
          (totalSpinHalfOp1 Λ * spinHalfDot x y +
            Complex.I • (totalSpinHalfOp2 Λ * spinHalfDot x y)) =
        (spinHalfDot x y * totalSpinHalfOp1 Λ -
            totalSpinHalfOp1 Λ * spinHalfDot x y) +
          Complex.I • (spinHalfDot x y * totalSpinHalfOp2 Λ -
            totalSpinHalfOp2 Λ * spinHalfDot x y) from by
    rw [smul_sub]; abel]
  rw [h1, h2, smul_zero, add_zero]

/-- SU(2) invariance with the lowering operator:
`[Ŝ_x · Ŝ_y, Ŝ^-_tot] = 0`. -/
theorem spinHalfDot_commutator_totalSpinHalfOpMinus (x y : Λ) :
    spinHalfDot x y * totalSpinHalfOpMinus Λ -
        totalSpinHalfOpMinus Λ * spinHalfDot x y = 0 := by
  rw [totalSpinHalfOpMinus_eq_sub, mul_sub, sub_mul]
  rw [mul_smul_comm, smul_mul_assoc]
  have h1 := spinHalfDot_commutator_totalSpinHalfOp1 x y
  have h2 := spinHalfDot_commutator_totalSpinHalfOp2 x y
  rw [show spinHalfDot x y * totalSpinHalfOp1 Λ -
            Complex.I • (spinHalfDot x y * totalSpinHalfOp2 Λ) -
          (totalSpinHalfOp1 Λ * spinHalfDot x y -
            Complex.I • (totalSpinHalfOp2 Λ * spinHalfDot x y)) =
        (spinHalfDot x y * totalSpinHalfOp1 Λ -
            totalSpinHalfOp1 Λ * spinHalfDot x y) -
          Complex.I • (spinHalfDot x y * totalSpinHalfOp2 Λ -
            totalSpinHalfOp2 Λ * spinHalfDot x y) from by
    rw [smul_sub]; abel]
  rw [h1, h2, smul_zero, sub_zero]

/-- Tasaki eq. (2.2.18) (the defining identity, rearranged):
`(Ŝ_x + Ŝ_y)² = 2·(Ŝ_x · Ŝ_y) + Ŝ_x · Ŝ_x + Ŝ_y · Ŝ_y`. -/
theorem spinHalfPairSpinSq_eq (x y : Λ) :
    (spinHalfPairSpinSq x y : ManyBodyOp Λ) =
      (2 : ℂ) • spinHalfDot x y + spinHalfDot x x + spinHalfDot y y := by
  unfold spinHalfPairSpinSq spinHalfDot
  simp_rw [mul_add, add_mul]
  rw [onSite_mul_onSite_self_comm y x spinHalfOp1,
      onSite_mul_onSite_self_comm y x spinHalfOp2,
      onSite_mul_onSite_self_comm y x spinHalfOp3]
  rw [show (2 : ℂ) • (onSite x spinHalfOp1 * onSite y spinHalfOp1 +
        onSite x spinHalfOp2 * onSite y spinHalfOp2 +
        onSite x spinHalfOp3 * onSite y spinHalfOp3 : ManyBodyOp Λ) =
      (onSite x spinHalfOp1 * onSite y spinHalfOp1 +
        onSite x spinHalfOp2 * onSite y spinHalfOp2 +
        onSite x spinHalfOp3 * onSite y spinHalfOp3) +
      (onSite x spinHalfOp1 * onSite y spinHalfOp1 +
        onSite x spinHalfOp2 * onSite y spinHalfOp2 +
        onSite x spinHalfOp3 * onSite y spinHalfOp3) from two_smul _ _]
  abel

/-! ## Total spin squared as sum of two-site dot products -/

/-- `(Ŝ_tot)² = Σ_{x,y} Ŝ_x · Ŝ_y` — the total spin squared decomposes
into a double sum of two-site inner products. This is the natural
companion to Tasaki eq. (2.2.16). -/
theorem totalSpinHalfSquared_eq_sum_dot :
    totalSpinHalfSquared Λ = ∑ x : Λ, ∑ y : Λ, spinHalfDot x y := by
  unfold totalSpinHalfSquared totalSpinHalfOp1 totalSpinHalfOp2 totalSpinHalfOp3
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [spinHalfDot_comm]
  rfl

/-! ## Two-spin Ŝ_x · Ŝ_y eigenvalues on basis states (Tasaki eq (2.2.19))

For two distinct sites `x ≠ y`, the two-site dot product `Ŝ_x · Ŝ_y`
acts on a computational-basis state `|σ⟩` according to whether the two
spins are parallel (`σ x = σ y`) or anti-parallel (`σ x ≠ σ y`).

* **Parallel** (`σ x = σ y`): `Ŝ_x · Ŝ_y |σ⟩ = (1/4) |σ⟩`. The ladder
  terms vanish (one factor of `Ŝ^±` annihilates `|σ⟩`) and the diagonal
  term contributes `(±1/2)·(±1/2) = +1/4`.
* **Anti-parallel** (`σ x ≠ σ y`): `Ŝ_x · Ŝ_y |σ⟩ = (1/2)|σ_swap⟩
  + (-1/4)|σ⟩` where `|σ_swap⟩` is the basis state with sites `x` and
  `y` swapped. From this one recovers the spin-1/2 triplet/singlet
  eigenvalues `1/4`, `-3/4`. -/

/-- Parallel-spin eigenvalue: if `σ x = σ y` (and `x ≠ y`), then
`Ŝ_x · Ŝ_y |σ⟩ = (1/4) |σ⟩`. -/
theorem spinHalfDot_mulVec_basisVec_parallel
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x = σ y) :
    (spinHalfDot x y).mulVec (basisVec σ) = (1 / 4 : ℂ) • basisVec σ := by
  have hupd0 : Function.update σ y (0 : Fin 2) x = σ x :=
    Function.update_of_ne hxy 0 σ
  have hupd1 : Function.update σ y (1 : Fin 2) x = σ x :=
    Function.update_of_ne hxy 1 σ
  rw [spinHalfDot_eq_plus_minus]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [onSite_spinHalfOp3_mulVec_basisVec, Matrix.mulVec_smul,
      onSite_spinHalfOp3_mulVec_basisVec, smul_smul]
  rw [onSite_spinHalfOpMinus_mulVec_basisVec,
      onSite_spinHalfOpPlus_mulVec_basisVec]
  by_cases hsx : σ x = 0
  · have hsy : σ y = 0 := h ▸ hsx
    rw [if_pos hsy, if_neg (by rw [hsy]; exact zero_ne_one)]
    rw [onSite_spinHalfOpPlus_mulVec_basisVec]
    rw [if_neg (by rw [hupd1, hsx]; exact zero_ne_one)]
    simp only [Matrix.mulVec_zero, smul_zero, add_zero, zero_add]
    rw [hsx, hsy]
    have hsign : (spinHalfSign 0 * spinHalfSign 0 : ℂ) = (1 / 4 : ℂ) := by
      unfold spinHalfSign; norm_num
    rw [hsign]
  · have hsx1 : σ x = 1 := by
      match hxv : σ x with
      | 0 => exact absurd hxv hsx
      | 1 => rfl
    have hsy1 : σ y = 1 := h ▸ hsx1
    rw [if_neg (by rw [hsy1]; exact one_ne_zero), if_pos hsy1]
    rw [onSite_spinHalfOpMinus_mulVec_basisVec]
    rw [if_neg (by rw [hupd0, hsx1]; exact one_ne_zero)]
    simp only [Matrix.mulVec_zero, smul_zero, add_zero, zero_add]
    rw [hsx1, hsy1]
    have hsign : (spinHalfSign 1 * spinHalfSign 1 : ℂ) = (1 / 4 : ℂ) := by
      unfold spinHalfSign; norm_num
    rw [hsign]

/-- Two-spin both-up: `Ŝ_x · Ŝ_y |↑↑⟩ = (1/4) |↑↑⟩` (the spin-1
triplet eigenvalue). -/
theorem spinHalfDot_mulVec_basisVec_both_up
    {x y : Λ} (hxy : x ≠ y) :
    (spinHalfDot x y).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      (1 / 4 : ℂ) • basisVec (fun _ : Λ => (0 : Fin 2)) :=
  spinHalfDot_mulVec_basisVec_parallel hxy _ rfl

/-- Two-spin both-down: `Ŝ_x · Ŝ_y |↓↓⟩ = (1/4) |↓↓⟩` (the spin-1
triplet eigenvalue at `m = -1`). -/
theorem spinHalfDot_mulVec_basisVec_both_down
    {x y : Λ} (hxy : x ≠ y) :
    (spinHalfDot x y).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      (1 / 4 : ℂ) • basisVec (fun _ : Λ => (1 : Fin 2)) :=
  spinHalfDot_mulVec_basisVec_parallel hxy _ rfl

/-- Site-swap of `σ` at sites `x, y`: swaps the values `σ x` and `σ y`,
leaving the other coordinates unchanged. -/
def basisSwap (σ : Λ → Fin 2) (x y : Λ) : Λ → Fin 2 :=
  Function.update (Function.update σ x (σ y)) y (σ x)

/-- Anti-parallel-spin action: if `σ x ≠ σ y` (and `x ≠ y`), then
`Ŝ_x · Ŝ_y |σ⟩ = (1/2) |swap σ⟩ - (1/4) |σ⟩`. The single non-zero
ladder term implements the swap; the diagonal contributes
`spinHalfSign(σ x) · spinHalfSign(σ y) = -1/4`. -/
theorem spinHalfDot_mulVec_basisVec_antiparallel
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    (spinHalfDot x y).mulVec (basisVec σ) =
      (1 / 2 : ℂ) • basisVec (basisSwap σ x y) - (1 / 4 : ℂ) • basisVec σ := by
  have hupd0 : Function.update σ y (0 : Fin 2) x = σ x :=
    Function.update_of_ne hxy 0 σ
  have hupd1 : Function.update σ y (1 : Fin 2) x = σ x :=
    Function.update_of_ne hxy 1 σ
  rw [spinHalfDot_eq_plus_minus]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [onSite_spinHalfOp3_mulVec_basisVec, Matrix.mulVec_smul,
      onSite_spinHalfOp3_mulVec_basisVec, smul_smul]
  rw [onSite_spinHalfOpMinus_mulVec_basisVec,
      onSite_spinHalfOpPlus_mulVec_basisVec]
  by_cases hsx : σ x = 0
  · have hsy : σ y = 1 := by
      match hyv : σ y with
      | 0 => rw [hsx, hyv] at h; exact absurd rfl h
      | 1 => rfl
    rw [if_neg (by rw [hsy]; exact one_ne_zero), if_pos hsy]
    rw [onSite_spinHalfOpMinus_mulVec_basisVec]
    rw [if_pos (by rw [hupd0, hsx])]
    have hswap : Function.update (Function.update σ y (0 : Fin 2)) x (1 : Fin 2) =
        basisSwap σ x y := by
      unfold basisSwap
      rw [hsx, hsy, Function.update_comm hxy.symm]
    rw [hswap, hsx, hsy]
    have hsign : (spinHalfSign 1 * spinHalfSign 0 : ℂ) = -(1 / 4 : ℂ) := by
      unfold spinHalfSign; norm_num
    rw [hsign]
    simp only [Matrix.mulVec_zero, zero_add]
    rw [neg_smul, ← sub_eq_add_neg]
  · have hsx1 : σ x = 1 := by
      match hxv : σ x with
      | 0 => exact absurd hxv hsx
      | 1 => rfl
    have hsy0 : σ y = 0 := by
      match hyv : σ y with
      | 0 => rfl
      | 1 => rw [hsx1, hyv] at h; exact absurd rfl h
    rw [if_pos hsy0, if_neg (by rw [hsy0]; exact zero_ne_one)]
    rw [onSite_spinHalfOpPlus_mulVec_basisVec]
    rw [if_pos (by rw [hupd1, hsx1])]
    have hswap : Function.update (Function.update σ y (1 : Fin 2)) x (0 : Fin 2) =
        basisSwap σ x y := by
      unfold basisSwap
      rw [hsx1, hsy0, Function.update_comm hxy.symm]
    rw [hswap, hsx1, hsy0]
    have hsign : (spinHalfSign 0 * spinHalfSign 1 : ℂ) = -(1 / 4 : ℂ) := by
      unfold spinHalfSign; norm_num
    rw [hsign]
    simp only [Matrix.mulVec_zero, add_zero]
    rw [neg_smul, ← sub_eq_add_neg]

omit [Fintype Λ] in
/-- The swap is involutive: `swap (swap σ) = σ` (under `x ≠ y`). -/
theorem basisSwap_involutive {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) :
    basisSwap (basisSwap σ x y) x y = σ := by
  funext z
  unfold basisSwap
  have hyx : y ≠ x := hxy.symm
  have hsx : Function.update (Function.update σ x (σ y)) y (σ x) x = σ y := by
    rw [Function.update_of_ne hxy, Function.update_self]
  have hsy : Function.update (Function.update σ x (σ y)) y (σ x) y = σ x :=
    Function.update_self _ _ _
  rw [hsx, hsy]
  by_cases hzy : z = y
  · subst hzy
    rw [Function.update_self]
  · rw [Function.update_of_ne hzy]
    by_cases hzx : z = x
    · subst hzx
      rw [Function.update_self]
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzy,
          Function.update_of_ne hzx]

omit [Fintype Λ] in
/-- The swap of an anti-parallel configuration is anti-parallel:
`(swap σ) x ≠ (swap σ) y`. -/
theorem basisSwap_antiparallel {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2)
    (h : σ x ≠ σ y) : basisSwap σ x y x ≠ basisSwap σ x y y := by
  unfold basisSwap
  rw [Function.update_self]
  rw [Function.update_of_ne hxy, Function.update_self]
  exact h.symm

/-- Singlet eigenvalue (Tasaki (2.2.19)): for `x ≠ y` and σ
anti-parallel, the unsymmetric combination `|σ⟩ - |swap σ⟩` is an
eigenvector of `Ŝ_x · Ŝ_y` with eigenvalue `-3/4`. -/
theorem spinHalfDot_mulVec_singlet
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    (spinHalfDot x y).mulVec (basisVec σ - basisVec (basisSwap σ x y)) =
      -(3 / 4 : ℂ) • (basisVec σ - basisVec (basisSwap σ x y)) := by
  rw [Matrix.mulVec_sub]
  rw [spinHalfDot_mulVec_basisVec_antiparallel hxy σ h]
  rw [spinHalfDot_mulVec_basisVec_antiparallel hxy (basisSwap σ x y)
      (basisSwap_antiparallel hxy σ h)]
  rw [basisSwap_involutive hxy σ]
  -- Now: (1/2) |σ'⟩ - (1/4) |σ⟩ - ((1/2) |σ⟩ - (1/4) |σ'⟩) = -(3/4) (|σ⟩ - |σ'⟩)
  set u : (Λ → Fin 2) → ℂ := basisVec σ
  set v : (Λ → Fin 2) → ℂ := basisVec (basisSwap σ x y)
  change ((1 / 2 : ℂ) • v - (1 / 4 : ℂ) • u) - ((1 / 2 : ℂ) • u - (1 / 4 : ℂ) • v) =
       -(3 / 4 : ℂ) • (u - v)
  rw [smul_sub, neg_smul]
  module

/-- Triplet eigenvalue (Tasaki (2.2.19)): for `x ≠ y` and σ
anti-parallel, the symmetric combination `|σ⟩ + |swap σ⟩` is an
eigenvector of `Ŝ_x · Ŝ_y` with eigenvalue `1/4` — matching the
parallel-spin case. -/
theorem spinHalfDot_mulVec_triplet_anti
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    (spinHalfDot x y).mulVec (basisVec σ + basisVec (basisSwap σ x y)) =
      (1 / 4 : ℂ) • (basisVec σ + basisVec (basisSwap σ x y)) := by
  rw [Matrix.mulVec_add]
  rw [spinHalfDot_mulVec_basisVec_antiparallel hxy σ h]
  rw [spinHalfDot_mulVec_basisVec_antiparallel hxy (basisSwap σ x y)
      (basisSwap_antiparallel hxy σ h)]
  rw [basisSwap_involutive hxy σ]
  set u : (Λ → Fin 2) → ℂ := basisVec σ
  set v : (Λ → Fin 2) → ℂ := basisVec (basisSwap σ x y)
  change ((1 / 2 : ℂ) • v - (1 / 4 : ℂ) • u) + ((1 / 2 : ℂ) • u - (1 / 4 : ℂ) • v) =
       (1 / 4 : ℂ) • (u + v)
  rw [smul_add]
  module

/-! ## Heisenberg-type SU(2)-invariant Hamiltonian (Tasaki §2.2 (2.2.13)) -/

/-- The general Heisenberg-type Hamiltonian
`H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y`. Any choice of coupling `J` yields an
SU(2)-invariant operator (proved below). -/
noncomputable def heisenbergHamiltonian (J : Λ → Λ → ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, ∑ y : Λ, J x y • spinHalfDot x y

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ_tot^(1)` (Tasaki
§2.2 SU(2)-invariance, eq. (2.2.13) for axis 1). -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOp1 (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOp1 Λ -
        totalSpinHalfOp1 Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOp1, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ_tot^(2)`. -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOp2 (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOp2 Λ -
        totalSpinHalfOp2 Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOp2, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ_tot^(3)`. -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOp3 (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOp3 Λ -
        totalSpinHalfOp3 Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOp3, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ^+_tot` (ladder
form of SU(2) invariance). -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOpPlus (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOpPlus Λ -
        totalSpinHalfOpPlus Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOpPlus, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ^-_tot`. -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOpMinus (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOpMinus Λ -
        totalSpinHalfOpMinus Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOpMinus, smul_zero]

/-! ## Casimir eigenvalue on the all-up / all-down states -/

/-- `Ŝ_x · Ŝ_y` action on a uniformly-aligned basis state (constant `s`):
`(3/4) |s⟩` for `x = y`, `(1/4) |s⟩` for `x ≠ y`. -/
private theorem spinHalfDot_mulVec_const (s : Fin 2) (x y : Λ) :
    (spinHalfDot x y).mulVec (basisVec (fun _ : Λ => s)) =
      (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) •
        basisVec (fun _ : Λ => s) := by
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, spinHalfDot_self]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  · rw [if_neg hxy]
    exact spinHalfDot_mulVec_basisVec_parallel hxy _ rfl

/-- Specialization to the all-up state. -/
private theorem spinHalfDot_mulVec_all_up (x y : Λ) :
    (spinHalfDot x y).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  spinHalfDot_mulVec_const 0 x y

/-- The Casimir eigenvalue on a uniformly-aligned basis state:
`Ŝ_tot² |s s … s⟩ = (N(N+2)/4) |s s … s⟩` where `N = |Λ|`. Both
the all-up and all-down states are eigenvectors with eigenvalue
`S(S+1) = (N/2)(N/2+1)`, the maximum total spin `S = N/2`. -/
theorem totalSpinHalfSquared_mulVec_basisVec_const (s : Fin 2) :
    (totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => s)) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        basisVec (fun _ : Λ => s) := by
  rw [totalSpinHalfSquared_eq_sum_dot]
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec, spinHalfDot_mulVec_const]
  simp_rw [← Finset.sum_smul]
  congr 1
  have hinner : ∀ x : Λ, (∑ y : Λ, (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) =
      (Fintype.card Λ : ℂ) / 4 + 1 / 2 := by
    intro x
    have hsplit : ∀ y : Λ, (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) =
        (1 / 4 : ℂ) + (if x = y then (1 / 2 : ℂ) else 0) := by
      intro y
      by_cases h : x = y
      · simp [h]; ring
      · simp [h]
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq Finset.univ x (fun _ => (1 / 2 : ℂ))]
    rw [if_pos (Finset.mem_univ _)]
    ring
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Specialization to the all-up state. -/
theorem totalSpinHalfSquared_mulVec_basisVec_all_up :
    (totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  totalSpinHalfSquared_mulVec_basisVec_const 0

/-- Specialization to the all-down state. -/
theorem totalSpinHalfSquared_mulVec_basisVec_all_down :
    (totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        basisVec (fun _ : Λ => (1 : Fin 2)) :=
  totalSpinHalfSquared_mulVec_basisVec_const 1

/-! ## Heisenberg Hamiltonian on the fully-polarised state (Tasaki §2.4 (2.4.5))

Tasaki *Physics and Mathematics of Quantum Many-Body Systems* §2.4
"The Ferromagnetic Heisenberg Model", eq. (2.4.5), p. 32, asserts that
the fully-polarised state `|Φ↑⟩ = ⊗_x |ψ_x^S⟩` satisfies

```
- Ŝ_x · Ŝ_y |Φ↑⟩ = - Ŝ_x^(3) Ŝ_y^(3) |Φ↑⟩ = - S² |Φ↑⟩,
```

so each bond term contributes the minimum eigenvalue `-S²`. Summed over
the bond set `B`, this gives `E_GS = -|B| S²` (the ferromagnetic
ground-state energy).

For `S = 1/2` this lifts to: every Heisenberg-type Hamiltonian
`H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` acts on a constant-spin basis state
`|s s … s⟩` as a scalar, with eigenvalue determined entirely by `J`. -/

/-- Heisenberg Hamiltonian on a uniformly-aligned basis state (constant
spin configuration `s : Fin 2`): the state is a simultaneous eigenvector
of every Heisenberg-type Hamiltonian, and the eigenvalue is the
weighted bilinear sum of the couplings.

This is the bilinear-sum lift of Tasaki §2.4 eq. (2.4.5), p. 32, for
`S = 1/2`: each bond term `Ŝ_x · Ŝ_y` (for `x ≠ y`) contributes
`1/4 = S²` (the maximum eigenvalue of `Ŝ_x · Ŝ_y` for `S = 1/2`),
and each diagonal term `Ŝ_x · Ŝ_x` contributes `3/4 = S(S+1)`
(via `spinHalfDot_self`). The diagonal `3/4` summand is an
extension beyond Tasaki's bond-only statement (which only treats
`x ≠ y`). The eigenvalue equals the ground-state energy only for
suitable ferromagnetic `J`; that step is not asserted here. -/
theorem heisenbergHamiltonian_mulVec_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec (basisVec (fun _ : Λ => s)) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        basisVec (fun _ : Λ => s) := by
  unfold heisenbergHamiltonian
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec,
    spinHalfDot_mulVec_const s, smul_smul]
  simp_rw [← Finset.sum_smul]

/-- Specialisation of `heisenbergHamiltonian_mulVec_basisVec_const`
to the all-up state (Tasaki §2.4 eq. (2.4.5), p. 32, for `S = 1/2`). -/
theorem heisenbergHamiltonian_mulVec_basisVec_all_up (J : Λ → Λ → ℂ) :
    (heisenbergHamiltonian J).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  heisenbergHamiltonian_mulVec_basisVec_const J 0

/-- Specialisation of `heisenbergHamiltonian_mulVec_basisVec_const`
to the all-down state (Tasaki §2.4 eq. (2.4.5), p. 32, for `S = 1/2`,
flipped). -/
theorem heisenbergHamiltonian_mulVec_basisVec_all_down (J : Λ → Λ → ℂ) :
    (heisenbergHamiltonian J).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        basisVec (fun _ : Λ => (1 : Fin 2)) :=
  heisenbergHamiltonian_mulVec_basisVec_const J 1

/-! ## Eigenvalue propagation under Ŝ_tot^± (Tasaki §2.4 (2.4.7)/(2.4.9))

Since `[H, Ŝ_tot^±] = 0` for any Heisenberg-type Hamiltonian
(`heisenbergHamiltonian_commutator_totalSpinHalfOp{Plus,Minus}`), and
the constant configuration `|s s … s⟩` is an `H`-eigenvector
(`heisenbergHamiltonian_mulVec_basisVec_const`), the lowered state
`Ŝ_tot^- · |s s … s⟩` is again an `H`-eigenvector with the same
eigenvalue. Iterating gives the entire ferromagnetic ground-state
ladder `(Ŝ_tot^-)^k · |Φ↑⟩ ∝ |Φ_M⟩` of Tasaki eq. (2.4.9). -/

/-- Eigenvalue propagation under `Ŝ_tot^+`: applying the global raising
operator to a constant-spin basis state preserves the H-eigenvalue.
This is a direct corollary of the SU(2) invariance of every Heisenberg
Hamiltonian (Tasaki §2.4, eq. (2.4.7), p. 33). The companion `_Minus_`
result is the explicit lowering ladder Tasaki uses in eq. (2.4.9). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfOpPlus Λ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfOpPlus Λ).mulVec (basisVec (fun _ : Λ => s)) := by
  have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpPlus J
  have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpPlus Λ =
      totalSpinHalfOpPlus Λ * heisenbergHamiltonian J :=
    sub_eq_zero.mp hcomm
  rw [Matrix.mulVec_mulVec, hcomm', ← Matrix.mulVec_mulVec,
    heisenbergHamiltonian_mulVec_basisVec_const, Matrix.mulVec_smul]

/-- Eigenvalue propagation under `Ŝ_tot^-`: applying the global lowering
operator to a constant-spin basis state preserves the H-eigenvalue.
Tasaki §2.4 eqs. (2.4.7)/(2.4.9), p. 33, for `S = 1/2`. This is the
ladder step generating the ferromagnetic ground states `|Φ_M⟩` from
`|Φ↑⟩` in eq. (2.4.9). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfOpMinus Λ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfOpMinus Λ).mulVec (basisVec (fun _ : Λ => s)) := by
  have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpMinus J
  have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpMinus Λ =
      totalSpinHalfOpMinus Λ * heisenbergHamiltonian J :=
    sub_eq_zero.mp hcomm
  rw [Matrix.mulVec_mulVec, hcomm', ← Matrix.mulVec_mulVec,
    heisenbergHamiltonian_mulVec_basisVec_const, Matrix.mulVec_smul]

/-- Iterated form of
`heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_basisVec_const`:
for any constant `s : Fin 2` and every natural-number power `k`,
`(Ŝ_tot^-)^k · |s..s⟩` is an `H`-eigenvector with the same eigenvalue
as `|s..s⟩`. Specialised to `s = 0` (the all-up state `|Φ↑⟩`), this is
the unnormalised version of Tasaki §2.4 eq. (2.4.9), p. 33: the
ferromagnetic ground states `|Φ_M⟩ ∝ (Ŝ_tot^-)^{|Λ|S - M} · |Φ↑⟩` all
share the eigenvalue of `|Φ↑⟩`. -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) (k : ℕ) :
    (heisenbergHamiltonian J).mulVec
        (((totalSpinHalfOpMinus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        ((totalSpinHalfOpMinus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact heisenbergHamiltonian_mulVec_basisVec_const J s
  | succ k ih =>
    have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpMinus J
    have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpMinus Λ =
        totalSpinHalfOpMinus Λ * heisenbergHamiltonian J :=
      sub_eq_zero.mp hcomm
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm',
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

/-- Iterated form of
`heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_basisVec_const`:
for any constant `s : Fin 2` and every `k : ℕ`,
`(Ŝ_tot^+)^k · |s..s⟩` is an `H`-eigenvector with the same eigenvalue
as `|s..s⟩`. Companion to the lowering version above; both are
direct corollaries of the SU(2) invariance of every Heisenberg
Hamiltonian (Tasaki §2.4, eq. (2.4.7), p. 33), iterated. -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) (k : ℕ) :
    (heisenbergHamiltonian J).mulVec
        (((totalSpinHalfOpPlus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        ((totalSpinHalfOpPlus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact heisenbergHamiltonian_mulVec_basisVec_const J s
  | succ k ih =>
    have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpPlus J
    have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpPlus Λ =
        totalSpinHalfOpPlus Λ * heisenbergHamiltonian J :=
      sub_eq_zero.mp hcomm
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm',
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

/-! ## Two-site singlet / triplet Casimir eigenvalues

For `Λ = Fin 2`, the natural anti-parallel basis state `|↑↓⟩` satisfies:

* `Ŝ_tot² (|↑↓⟩ - |↓↑⟩) = 0` (singlet, `S = 0`).
* `Ŝ_tot² (|↑↓⟩ + |↓↑⟩) = 2 (|↑↓⟩ + |↓↑⟩)` (triplet `m = 0`, `S = 1`).

Combined with the all-up/all-down statements, this exhausts the
`Ŝ_tot²` spectrum of two spin-1/2 particles. -/

/-- The two-site `↑↓` configuration (anti-parallel: site 0 up, site 1 down). -/
def upDown : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

/-- `upDown` maps site 0 to spin-up. -/
lemma upDown_zero : upDown 0 = 0 := rfl
/-- `upDown` maps site 1 to spin-down. -/
lemma upDown_one : upDown 1 = 1 := rfl

/-- The two sites carry opposite spins under `upDown`. -/
lemma upDown_antiparallel : upDown 0 ≠ upDown 1 := by
  rw [upDown_zero, upDown_one]; exact zero_ne_one

/-- Explicit form of the swap of `upDown` at sites `0` and `1`. -/
lemma basisSwap_upDown :
    basisSwap upDown (0 : Fin 2) 1 = fun (i : Fin 2) =>
      match i with | 0 => 1 | 1 => 0 := by
  funext i
  unfold basisSwap upDown
  fin_cases i <;> simp

/-- Two-site singlet eigenvalue: `Ŝ_tot² (|↑↓⟩ - |↓↑⟩) = 0`. -/
theorem totalSpinHalfSquared_mulVec_two_site_singlet :
    (totalSpinHalfSquared (Fin 2)).mulVec
        (basisVec upDown - basisVec (basisSwap upDown 0 1)) = 0 := by
  rw [totalSpinHalfSquared_eq_sum_dot]
  have hzo : (0 : Fin 2) ≠ 1 := zero_ne_one
  have hoz : (1 : Fin 2) ≠ 0 := one_ne_zero
  have hud_swap : basisSwap upDown 1 0 = basisSwap upDown 0 1 := by
    funext i; unfold basisSwap upDown
    fin_cases i <;> simp
  -- Distribute the double sum into 4 terms
  rw [show (∑ x : Fin 2, ∑ y : Fin 2, spinHalfDot x y :) =
      spinHalfDot 0 0 + spinHalfDot 0 1 + spinHalfDot 1 0 + spinHalfDot 1 1 from by
    simp [Fin.sum_univ_two]; abel]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  -- Each diagonal term = (3/4)·1, off-diagonal terms = -(3/4)
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_mulVec_singlet hzo upDown upDown_antiparallel]
  rw [spinHalfDot_comm 1 0]
  rw [spinHalfDot_mulVec_singlet hzo upDown upDown_antiparallel]
  -- Now: (3/4)·v + -(3/4)·v + -(3/4)·v + (3/4)·v = 0
  set v : (Fin 2 → Fin 2) → ℂ := basisVec upDown - basisVec (basisSwap upDown 0 1)
  change (3 / 4 : ℂ) • v + -(3 / 4 : ℂ) • v + -(3 / 4 : ℂ) • v + (3 / 4 : ℂ) • v = 0
  module

/-- Two-site triplet `m = 0` eigenvalue: `Ŝ_tot² (|↑↓⟩ + |↓↑⟩) = 2 (|↑↓⟩ + |↓↑⟩)`. -/
theorem totalSpinHalfSquared_mulVec_two_site_triplet_zero :
    (totalSpinHalfSquared (Fin 2)).mulVec
        (basisVec upDown + basisVec (basisSwap upDown 0 1)) =
      (2 : ℂ) • (basisVec upDown + basisVec (basisSwap upDown 0 1)) := by
  rw [totalSpinHalfSquared_eq_sum_dot]
  have hzo : (0 : Fin 2) ≠ 1 := zero_ne_one
  rw [show (∑ x : Fin 2, ∑ y : Fin 2, spinHalfDot x y :) =
      spinHalfDot 0 0 + spinHalfDot 0 1 + spinHalfDot 1 0 + spinHalfDot 1 1 from by
    simp [Fin.sum_univ_two]; abel]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_mulVec_triplet_anti hzo upDown upDown_antiparallel]
  rw [spinHalfDot_comm 1 0]
  rw [spinHalfDot_mulVec_triplet_anti hzo upDown upDown_antiparallel]
  set v : (Fin 2 → Fin 2) → ℂ := basisVec upDown + basisVec (basisSwap upDown 0 1)
  change (3 / 4 : ℂ) • v + (1 / 4 : ℂ) • v + (1 / 4 : ℂ) • v + (3 / 4 : ℂ) • v =
       (2 : ℂ) • v
  module

/-- The two-site singlet is annihilated by `Ŝ_tot^(3)`: zero magnetization. -/
theorem totalSpinHalfOp3_mulVec_two_site_singlet :
    (totalSpinHalfOp3 (Fin 2)).mulVec
        (basisVec upDown - basisVec (basisSwap upDown 0 1)) = 0 := by
  rw [Matrix.mulVec_sub]
  rw [totalSpinHalfOp3_mulVec_basisVec]
  rw [totalSpinHalfOp3_mulVec_basisVec]
  -- Σ spinHalfSign upDown = (1/2) + (-1/2) = 0
  have h_ud : ∑ x : Fin 2, spinHalfSign (upDown x) = 0 := by
    rw [Fin.sum_univ_two]
    simp [upDown_zero, upDown_one, spinHalfSign]
  -- For swap σ x = 1, swap σ y = 0: Σ spinHalfSign = (-1/2) + (1/2) = 0
  have h_swap : ∑ x : Fin 2, spinHalfSign (basisSwap upDown 0 1 x) = 0 := by
    rw [Fin.sum_univ_two]
    rw [basisSwap_upDown]; simp [spinHalfSign]
  rw [h_ud, h_swap, zero_smul, zero_smul, sub_self]

end LatticeSystem.Quantum
