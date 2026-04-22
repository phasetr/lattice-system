/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin

/-!
# Total spin squared (Casimir) + magnetic-quantum-number ladder

Tasaki §2.4 (2.4.9) ladder structure on the all-up / all-down
states + the generic eigenvalue preservation lemma for commuting
operators.

(Refactor Phase 2 PR 19 — second TotalSpin extraction, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-! ## Total spin squared (Casimir operator) -/

/-- The total spin squared `(Ŝ_tot)² := Σ_α (Ŝ_tot^(α))²`. This is the
quantum-mechanical Casimir invariant of the `su(2)` algebra acting on
the many-body Hilbert space. -/
noncomputable def totalSpinHalfSquared : ManyBodyOp Λ :=
  totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
    totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ +
    totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ

/-- `(Ŝ_tot)²` is Hermitian. -/
theorem totalSpinHalfSquared_isHermitian :
    (totalSpinHalfSquared Λ).IsHermitian := by
  unfold totalSpinHalfSquared
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinHalfOp1_isHermitian Λ)]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinHalfOp2_isHermitian Λ)]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinHalfOp3_isHermitian Λ)]

/-- Internal Leibniz: `[X·X, C] = X·[X,C] + [X,C]·X`. -/
private lemma square_commutator_totalSpin (X C : ManyBodyOp Λ) :
    X * X * C - C * (X * X) = X * (X * C - C * X) + (X * C - C * X) * X := by
  rw [mul_sub, sub_mul]
  have h1 : X * (C * X) = X * C * X := (mul_assoc X C X).symm
  have h2 : X * X * C = X * (X * C) := mul_assoc X X C
  have h3 : C * (X * X) = C * X * X := (mul_assoc C X X).symm
  rw [h1, h2, h3]; abel

/-- Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^(3)] = 0`. -/
theorem totalSpinHalfSquared_commutator_totalSpinHalfOp3 :
    totalSpinHalfSquared Λ * totalSpinHalfOp3 Λ
        - totalSpinHalfOp3 Λ * totalSpinHalfSquared Λ = 0 := by
  unfold totalSpinHalfSquared
  set A := totalSpinHalfOp1 Λ
  set B := totalSpinHalfOp2 Λ
  set C := totalSpinHalfOp3 Λ
  have hCA : C * A - A * C = Complex.I • B :=
    totalSpinHalfOp3_commutator_totalSpinHalfOp1 Λ
  have hBC : B * C - C * B = Complex.I • A :=
    totalSpinHalfOp2_commutator_totalSpinHalfOp3 Λ
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show A * A * C + B * B * C + C * C * C - (C * (A * A) + C * (B * B) + C * (C * C))
        = (A * A * C - C * (A * A)) + (B * B * C - C * (B * B))
          + (C * C * C - C * (C * C)) from by abel]
  rw [square_commutator_totalSpin Λ A, square_commutator_totalSpin Λ B,
    square_commutator_totalSpin Λ C]
  have hAC : A * C - C * A = -(Complex.I • B) := by
    rw [show A * C - C * A = -(C * A - A * C) from by abel, hCA]
  have hCC : C * C - C * C = (0 : ManyBodyOp Λ) := sub_self _
  rw [hAC, hBC, hCC]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^(1)] = 0`. -/
theorem totalSpinHalfSquared_commutator_totalSpinHalfOp1 :
    totalSpinHalfSquared Λ * totalSpinHalfOp1 Λ
        - totalSpinHalfOp1 Λ * totalSpinHalfSquared Λ = 0 := by
  unfold totalSpinHalfSquared
  set A := totalSpinHalfOp1 Λ
  set B := totalSpinHalfOp2 Λ
  set C := totalSpinHalfOp3 Λ
  have hAB : A * B - B * A = Complex.I • C :=
    totalSpinHalfOp1_commutator_totalSpinHalfOp2 Λ
  have hCA : C * A - A * C = Complex.I • B :=
    totalSpinHalfOp3_commutator_totalSpinHalfOp1 Λ
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show A * A * A + B * B * A + C * C * A - (A * (A * A) + A * (B * B) + A * (C * C))
        = (A * A * A - A * (A * A)) + (B * B * A - A * (B * B))
          + (C * C * A - A * (C * C)) from by abel]
  rw [square_commutator_totalSpin Λ A, square_commutator_totalSpin Λ B,
    square_commutator_totalSpin Λ C]
  have hAA : A * A - A * A = (0 : ManyBodyOp Λ) := sub_self _
  have hBA : B * A - A * B = -(Complex.I • C) := by
    rw [show B * A - A * B = -(A * B - B * A) from by abel, hAB]
  rw [hAA, hBA, hCA]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [zero_add]
  abel

/-- Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^(2)] = 0`. -/
theorem totalSpinHalfSquared_commutator_totalSpinHalfOp2 :
    totalSpinHalfSquared Λ * totalSpinHalfOp2 Λ
        - totalSpinHalfOp2 Λ * totalSpinHalfSquared Λ = 0 := by
  unfold totalSpinHalfSquared
  set A := totalSpinHalfOp1 Λ
  set B := totalSpinHalfOp2 Λ
  set C := totalSpinHalfOp3 Λ
  have hAB : A * B - B * A = Complex.I • C :=
    totalSpinHalfOp1_commutator_totalSpinHalfOp2 Λ
  have hBC : B * C - C * B = Complex.I • A :=
    totalSpinHalfOp2_commutator_totalSpinHalfOp3 Λ
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show A * A * B + B * B * B + C * C * B - (B * (A * A) + B * (B * B) + B * (C * C))
        = (A * A * B - B * (A * A)) + (B * B * B - B * (B * B))
          + (C * C * B - B * (C * C)) from by abel]
  rw [square_commutator_totalSpin Λ A, square_commutator_totalSpin Λ B,
    square_commutator_totalSpin Λ C]
  have hBB : B * B - B * B = (0 : ManyBodyOp Λ) := sub_self _
  have hCB : C * B - B * C = -(Complex.I • A) := by
    rw [show C * B - B * C = -(B * C - C * B) from by abel, hBC]
  rw [hAB, hBB, hCB]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [add_zero]
  abel

/-- Casimir invariance with the raising operator: `[(Ŝ_tot)², Ŝ^+_tot] = 0`. -/
theorem totalSpinHalfSquared_commutator_totalSpinHalfOpPlus :
    totalSpinHalfSquared Λ * totalSpinHalfOpPlus Λ
        - totalSpinHalfOpPlus Λ * totalSpinHalfSquared Λ = 0 := by
  rw [totalSpinHalfOpPlus_eq_add, mul_add, add_mul]
  rw [mul_smul_comm, smul_mul_assoc]
  have h1 := totalSpinHalfSquared_commutator_totalSpinHalfOp1 Λ
  have h2 := totalSpinHalfSquared_commutator_totalSpinHalfOp2 Λ
  rw [show totalSpinHalfSquared Λ * totalSpinHalfOp1 Λ +
            Complex.I • (totalSpinHalfSquared Λ * totalSpinHalfOp2 Λ) -
          (totalSpinHalfOp1 Λ * totalSpinHalfSquared Λ +
            Complex.I • (totalSpinHalfOp2 Λ * totalSpinHalfSquared Λ)) =
        (totalSpinHalfSquared Λ * totalSpinHalfOp1 Λ -
            totalSpinHalfOp1 Λ * totalSpinHalfSquared Λ) +
          Complex.I • (totalSpinHalfSquared Λ * totalSpinHalfOp2 Λ -
            totalSpinHalfOp2 Λ * totalSpinHalfSquared Λ) from by
    rw [smul_sub]; abel]
  rw [h1, h2, smul_zero, add_zero]

/-- Casimir invariance with the lowering operator: `[(Ŝ_tot)², Ŝ^-_tot] = 0`. -/
theorem totalSpinHalfSquared_commutator_totalSpinHalfOpMinus :
    totalSpinHalfSquared Λ * totalSpinHalfOpMinus Λ
        - totalSpinHalfOpMinus Λ * totalSpinHalfSquared Λ = 0 := by
  rw [totalSpinHalfOpMinus_eq_sub, mul_sub, sub_mul]
  rw [mul_smul_comm, smul_mul_assoc]
  have h1 := totalSpinHalfSquared_commutator_totalSpinHalfOp1 Λ
  have h2 := totalSpinHalfSquared_commutator_totalSpinHalfOp2 Λ
  rw [show totalSpinHalfSquared Λ * totalSpinHalfOp1 Λ -
            Complex.I • (totalSpinHalfSquared Λ * totalSpinHalfOp2 Λ) -
          (totalSpinHalfOp1 Λ * totalSpinHalfSquared Λ -
            Complex.I • (totalSpinHalfOp2 Λ * totalSpinHalfSquared Λ)) =
        (totalSpinHalfSquared Λ * totalSpinHalfOp1 Λ -
            totalSpinHalfOp1 Λ * totalSpinHalfSquared Λ) -
          Complex.I • (totalSpinHalfSquared Λ * totalSpinHalfOp2 Λ -
            totalSpinHalfOp2 Λ * totalSpinHalfSquared Λ) from by
    rw [smul_sub]; abel]
  rw [h1, h2, smul_zero, sub_zero]

/-- Total ladder commutator: `[Ŝ^+_tot, Ŝ^-_tot] = 2 · Ŝ_tot^(3)`. -/
theorem totalSpinHalfOpPlus_commutator_totalSpinHalfOpMinus :
    (totalSpinHalfOpPlus Λ * totalSpinHalfOpMinus Λ
        - totalSpinHalfOpMinus Λ * totalSpinHalfOpPlus Λ : ManyBodyOp Λ) =
      (2 : ℂ) • totalSpinHalfOp3 Λ := by
  unfold totalSpinHalfOpPlus totalSpinHalfOpMinus totalSpinHalfOp3
  -- Reuse the generic commutator framework with Sα=Ŝ^+, Sβ=Ŝ^-, but the RHS
  -- is `2 • Ŝ^(3)` rather than `I • Sγ`; we redo the calculation directly.
  calc (∑ x : Λ, onSite x spinHalfOpPlus) * (∑ x : Λ, onSite x spinHalfOpMinus)
          - (∑ x : Λ, onSite x spinHalfOpMinus) * (∑ x : Λ, onSite x spinHalfOpPlus)
      = ∑ x : Λ, ∑ y : Λ,
          (onSite x spinHalfOpPlus * onSite y spinHalfOpMinus
            - onSite y spinHalfOpMinus * onSite x spinHalfOpPlus) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (f := fun y x =>
          onSite y spinHalfOpMinus * onSite x spinHalfOpPlus)
          (s := Finset.univ) (t := Finset.univ)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Λ, ((2 : ℂ) • onSite x spinHalfOp3) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · rw [onSite_commutator_same, spinHalfOpPlus_commutator_spinHalfOpMinus,
              onSite_smul]
        · intros y _ hyx
          rw [onSite_mul_onSite_of_ne hyx.symm]
          simp
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = (2 : ℂ) • ∑ x : Λ, onSite x spinHalfOp3 := by
        rw [← Finset.smul_sum]

/-! ## Magnetic-quantum-number ladder on the all-up state (Tasaki §2.4 (2.4.9))

The all-up state `|↑..↑⟩` has `Ŝtot^(3)` eigenvalue `Smax = |Λ|/2`.
Iterating the global lowering operator `Ŝtot^-` lowers the eigenvalue
by one each step (Cartan ladder relation
`[Ŝtot^(3), Ŝtot^-] = -Ŝtot^-`), so
`Ŝtot^(3) · (Ŝtot^-)^k · |↑..↑⟩ = (Smax - k) · (Ŝtot^-)^k · |↑..↑⟩`.

This is the magnetic-quantum-number `M = Smax - k` labelling of
Tasaki's ferromagnetic ground states `|Φ_M⟩ ∝ (Ŝtot^-)^{Smax - M} |Φ↑⟩`
(eq. (2.4.9), p. 33). The normalisation factor of (2.4.9) and the
restriction to `M ∈ {-Smax, ..., +Smax}` are not asserted here. -/

/-- `Ŝ_tot^(3) · (Ŝ_tot^-)^k · |↑..↑⟩ = (|Λ|/2 - k) · (Ŝ_tot^-)^k · |↑..↑⟩`:
the magnetic-quantum-number labelling of Tasaki's ferromagnetic
ground-state ladder (eq. (2.4.9), p. 33). -/
theorem totalSpinHalfOp3_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up (k : ℕ) :
    (totalSpinHalfOp3 Λ).mulVec
        (((totalSpinHalfOpMinus Λ) ^ k).mulVec
          (basisVec (fun _ : Λ => (0 : Fin 2)))) =
      (((Fintype.card Λ : ℂ) / 2) - (k : ℂ)) •
        ((totalSpinHalfOpMinus Λ) ^ k).mulVec
          (basisVec (fun _ : Λ => (0 : Fin 2))) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, sub_zero]
    rw [totalSpinHalfOp3_mulVec_basisVec]
    congr 1
    have hsign : (∑ _x : Λ, spinHalfSign (0 : Fin 2)) = (Fintype.card Λ : ℂ) / 2 := by
      simp only [spinHalfSign, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    convert hsign
  | succ k ih =>
    have h := totalSpinHalfOp3_commutator_totalSpinHalfOpMinus Λ
    have hcomm : totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ =
        totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ - totalSpinHalfOpMinus Λ := by
      have hadd : totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ =
          (totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ -
            totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ) +
          totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ := by abel
      rw [hadd, h]; abel
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm,
      Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]
    set v : (Λ → Fin 2) → ℂ := (totalSpinHalfOpMinus Λ).mulVec
      (((totalSpinHalfOpMinus Λ) ^ k).mulVec
        (basisVec (fun _ : Λ => (0 : Fin 2))))
    push_cast
    module

/-- `Ŝ_tot^(3) · (Ŝ_tot^+)^k · |↓..↓⟩ = (-|Λ|/2 + k) · (Ŝ_tot^+)^k · |↓..↓⟩`:
the dual ladder. Starting from the all-down state with eigenvalue
`-Smax`, the Cartan relation `[Ŝ_tot^(3), Ŝ_tot^+] = +Ŝ_tot^+`
raises the eigenvalue by one at each step, giving the unnormalised
iterates magnetic quantum number `M = -Smax + k` (Tasaki §2.4
eq. (2.4.9), p. 33, parameterised from the lowest weight). -/
theorem totalSpinHalfOp3_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down (k : ℕ) :
    (totalSpinHalfOp3 Λ).mulVec
        (((totalSpinHalfOpPlus Λ) ^ k).mulVec
          (basisVec (fun _ : Λ => (1 : Fin 2)))) =
      ((-((Fintype.card Λ : ℂ) / 2)) + (k : ℂ)) •
        ((totalSpinHalfOpPlus Λ) ^ k).mulVec
          (basisVec (fun _ : Λ => (1 : Fin 2))) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, add_zero]
    rw [totalSpinHalfOp3_mulVec_basisVec]
    congr 1
    have hone : ((1 : Fin 2) = 0) ↔ False := by decide
    have hsign : (∑ _x : Λ, spinHalfSign (1 : Fin 2)) = -((Fintype.card Λ : ℂ) / 2) := by
      simp only [spinHalfSign, hone, if_false, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    exact hsign
  | succ k ih =>
    have h := totalSpinHalfOp3_commutator_totalSpinHalfOpPlus Λ
    have hcomm : totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ =
        totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ + totalSpinHalfOpPlus Λ := by
      have hadd : totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ =
          (totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ -
            totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ) +
          totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ := by abel
      rw [hadd, h]; abel
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]
    set v : (Λ → Fin 2) → ℂ := (totalSpinHalfOpPlus Λ).mulVec
      (((totalSpinHalfOpPlus Λ) ^ k).mulVec
        (basisVec (fun _ : Λ => (1 : Fin 2))))
    push_cast
    module

/-! ## Generic eigenvalue preservation under commuting operators

The abstract pattern underlying PRs #82/#83/#86/#87/#93/#106: if
`[A, B] = 0` and `v` is an `A`-eigenvector with eigenvalue `λ`, then
`B · v` is another `A`-eigenvector with the same eigenvalue. -/

/-- Generic eigenvalue preservation: if `Commute A B` and `A · v = λ · v`,
then `A · (B · v) = λ · (B · v)`. -/
theorem mulVec_preserves_eigenvalue_of_commute
    {A B : ManyBodyOp Λ} (h : Commute A B)
    {lam : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : A.mulVec v = lam • v) :
    A.mulVec (B.mulVec v) = lam • B.mulVec v := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]


end LatticeSystem.Quantum
