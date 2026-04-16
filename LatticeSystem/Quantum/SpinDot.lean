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

end LatticeSystem.Quantum
