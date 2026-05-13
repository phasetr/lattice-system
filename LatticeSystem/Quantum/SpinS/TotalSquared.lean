import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.MultiSiteCommutator
import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Spin-`S` total spin squared `(Ŝ_tot)²`
(Tasaki §2.5 Phase B-β β-3p)

The quantum-mechanical Casimir invariant of the `su(2)` algebra
acting on the multi-site spin-`S` Hilbert space:

  `(Ŝ_tot)² := Σ_{α=1,2,3} (Ŝ_tot^{(α)})²`.

Direct generalisation of `totalSpinHalfSquared` to arbitrary spin.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- Total spin-`S` squared. -/
noncomputable def totalSpinSSquared : ManyBodyOpS Λ N :=
  totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
    totalSpinSOp2 Λ N * totalSpinSOp2 Λ N +
    totalSpinSOp3 Λ N * totalSpinSOp3 Λ N

/-- Definitional unfolding. -/
theorem totalSpinSSquared_def :
    totalSpinSSquared Λ N =
      totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
        totalSpinSOp2 Λ N * totalSpinSOp2 Λ N +
        totalSpinSOp3 Λ N * totalSpinSOp3 Λ N := rfl

/-- Re-expression of `totalSpinSSquared` as a finite sum of squares
of total operators (matching the definition with `^2` instead of
`mul` self). -/
theorem totalSpinSSquared_eq_pow_sum :
    totalSpinSSquared Λ N =
      totalSpinSOp1 Λ N ^ 2 + totalSpinSOp2 Λ N ^ 2 + totalSpinSOp3 Λ N ^ 2 := by
  unfold totalSpinSSquared
  simp only [pow_two]

/-- `(Ŝ_tot)²` is Hermitian. -/
theorem totalSpinSSquared_isHermitian :
    (totalSpinSSquared Λ N).IsHermitian := by
  unfold totalSpinSSquared
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinSOp1_isHermitian Λ N)]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinSOp2_isHermitian Λ N)]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinSOp3_isHermitian Λ N)]

/-! ## Total-spin SU(2) cyclic commutators in named form -/

/-- `[Ŝ_tot^{(1)}, Ŝ_tot^{(2)}] = i · Ŝ_tot^{(3)}` (named-operator form). -/
theorem totalSpinSOp1_commutator_totalSpinSOp2_named :
    (totalSpinSOp1 Λ N * totalSpinSOp2 Λ N
        - totalSpinSOp2 Λ N * totalSpinSOp1 Λ N : ManyBodyOpS Λ N) =
      Complex.I • totalSpinSOp3 Λ N := by
  unfold totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  exact totalSpinSOp1_commutator_totalSpinSOp2 (Λ := Λ) N

/-- `[Ŝ_tot^{(2)}, Ŝ_tot^{(3)}] = i · Ŝ_tot^{(1)}` (named-operator form). -/
theorem totalSpinSOp2_commutator_totalSpinSOp3_named :
    (totalSpinSOp2 Λ N * totalSpinSOp3 Λ N
        - totalSpinSOp3 Λ N * totalSpinSOp2 Λ N : ManyBodyOpS Λ N) =
      Complex.I • totalSpinSOp1 Λ N := by
  unfold totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  exact totalSpinSOp2_commutator_totalSpinSOp3 (Λ := Λ) N

/-- `[Ŝ_tot^{(3)}, Ŝ_tot^{(1)}] = i · Ŝ_tot^{(2)}` (named-operator form). -/
theorem totalSpinSOp3_commutator_totalSpinSOp1_named :
    (totalSpinSOp3 Λ N * totalSpinSOp1 Λ N
        - totalSpinSOp1 Λ N * totalSpinSOp3 Λ N : ManyBodyOpS Λ N) =
      Complex.I • totalSpinSOp2 Λ N := by
  unfold totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  exact totalSpinSOp3_commutator_totalSpinSOp1 (Λ := Λ) N

/-! ## Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^{(α)}] = 0` -/

/-- Internal Leibniz: `[X·X, C] = X·[X,C] + [X,C]·X`. -/
private lemma square_commutator_totalSpinS (X C : ManyBodyOpS Λ N) :
    X * X * C - C * (X * X) = X * (X * C - C * X) + (X * C - C * X) * X := by
  rw [mul_sub, sub_mul]
  have h1 : X * (C * X) = X * C * X := (mul_assoc X C X).symm
  have h2 : X * X * C = X * (X * C) := mul_assoc X X C
  have h3 : C * (X * X) = C * X * X := (mul_assoc C X X).symm
  rw [h1, h2, h3]; abel

/-- Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^{(3)}] = 0`. -/
theorem totalSpinSSquared_commutator_totalSpinSOp3 :
    totalSpinSSquared Λ N * totalSpinSOp3 Λ N
        - totalSpinSOp3 Λ N * totalSpinSSquared Λ N = 0 := by
  unfold totalSpinSSquared
  set A := totalSpinSOp1 Λ N
  set B := totalSpinSOp2 Λ N
  set C := totalSpinSOp3 Λ N
  have hCA : C * A - A * C = Complex.I • B :=
    totalSpinSOp3_commutator_totalSpinSOp1_named Λ N
  have hBC : B * C - C * B = Complex.I • A :=
    totalSpinSOp2_commutator_totalSpinSOp3_named Λ N
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show A * A * C + B * B * C + C * C * C - (C * (A * A) + C * (B * B) + C * (C * C))
        = (A * A * C - C * (A * A)) + (B * B * C - C * (B * B))
          + (C * C * C - C * (C * C)) from by abel]
  rw [square_commutator_totalSpinS Λ N A, square_commutator_totalSpinS Λ N B,
    square_commutator_totalSpinS Λ N C]
  have hAC : A * C - C * A = -(Complex.I • B) := by
    rw [show A * C - C * A = -(C * A - A * C) from by abel, hCA]
  have hCC : C * C - C * C = (0 : ManyBodyOpS Λ N) := sub_self _
  rw [hAC, hBC, hCC]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-- Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^{(1)}] = 0`. -/
theorem totalSpinSSquared_commutator_totalSpinSOp1 :
    totalSpinSSquared Λ N * totalSpinSOp1 Λ N
        - totalSpinSOp1 Λ N * totalSpinSSquared Λ N = 0 := by
  unfold totalSpinSSquared
  set A := totalSpinSOp1 Λ N
  set B := totalSpinSOp2 Λ N
  set C := totalSpinSOp3 Λ N
  have hAB : A * B - B * A = Complex.I • C :=
    totalSpinSOp1_commutator_totalSpinSOp2_named Λ N
  have hCA : C * A - A * C = Complex.I • B :=
    totalSpinSOp3_commutator_totalSpinSOp1_named Λ N
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show A * A * A + B * B * A + C * C * A - (A * (A * A) + A * (B * B) + A * (C * C))
        = (A * A * A - A * (A * A)) + (B * B * A - A * (B * B))
          + (C * C * A - A * (C * C)) from by abel]
  rw [square_commutator_totalSpinS Λ N A, square_commutator_totalSpinS Λ N B,
    square_commutator_totalSpinS Λ N C]
  have hAA : A * A - A * A = (0 : ManyBodyOpS Λ N) := sub_self _
  have hBA : B * A - A * B = -(Complex.I • C) := by
    rw [show B * A - A * B = -(A * B - B * A) from by abel, hAB]
  rw [hAA, hBA, hCA]
  rw [mul_zero, zero_mul, add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [zero_add]
  abel

/-- Casimir invariance: `[(Ŝ_tot)², Ŝ_tot^{(2)}] = 0`. -/
theorem totalSpinSSquared_commutator_totalSpinSOp2 :
    totalSpinSSquared Λ N * totalSpinSOp2 Λ N
        - totalSpinSOp2 Λ N * totalSpinSSquared Λ N = 0 := by
  unfold totalSpinSSquared
  set A := totalSpinSOp1 Λ N
  set B := totalSpinSOp2 Λ N
  set C := totalSpinSOp3 Λ N
  have hAB : A * B - B * A = Complex.I • C :=
    totalSpinSOp1_commutator_totalSpinSOp2_named Λ N
  have hBC : B * C - C * B = Complex.I • A :=
    totalSpinSOp2_commutator_totalSpinSOp3_named Λ N
  rw [add_mul, add_mul, mul_add, mul_add]
  rw [show A * A * B + B * B * B + C * C * B - (B * (A * A) + B * (B * B) + B * (C * C))
        = (A * A * B - B * (A * A)) + (B * B * B - B * (B * B))
          + (C * C * B - B * (C * C)) from by abel]
  rw [square_commutator_totalSpinS Λ N A, square_commutator_totalSpinS Λ N B,
    square_commutator_totalSpinS Λ N C]
  have hBB : B * B - B * B = (0 : ManyBodyOpS Λ N) := sub_self _
  have hCB : C * B - B * C = -(Complex.I • A) := by
    rw [show C * B - B * C = -(B * C - C * B) from by abel, hBC]
  rw [hAB, hBB, hCB]
  rw [mul_zero, zero_mul]
  rw [show (0 : ManyBodyOpS Λ N) + 0 = 0 from by abel]
  rw [add_zero]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  abel

/-! ## Casimir as a sum of two-site dot products -/

/-- **Casimir expansion**: `(Ŝ_tot)² = Σ_{x, y : Λ} Ŝ_x · Ŝ_y`.

The spin-`S` generalisation of Tasaki §2.2 eq. (2.2.18). Together
with `spinSDot_self` (β-3e), this exhibits `(Ŝ_tot)²` as a finite
sum of (i) per-site Casimir terms `(N(N+2)/4) • 1` and (ii)
off-diagonal `Ŝ_x · Ŝ_y` couplings. -/
theorem totalSpinSSquared_eq_sum_spinSDot :
    (totalSpinSSquared Λ N : ManyBodyOpS Λ N) =
      ∑ x : Λ, ∑ y : Λ, spinSDot x y N := by
  unfold totalSpinSSquared totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  -- Each axis: (∑ x ax) * (∑ y ay) = ∑ x ∑ y ax * ay
  have expand : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      (∑ x : Λ, onSiteS x A : ManyBodyOpS Λ N) * (∑ y : Λ, onSiteS y A) =
        ∑ x : Λ, ∑ y : Λ, onSiteS x A * onSiteS y A := by
    intro A
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  rw [expand (spinSOp1 N), expand (spinSOp2 N), expand (spinSOp3 N)]
  -- Combine the three Σ x Σ y A_α B_α into Σ x Σ y (A_1 + A_2 + A_3)
  rw [show (∑ x : Λ, ∑ y : Λ,
              onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) : ManyBodyOpS Λ N) +
          (∑ x : Λ, ∑ y : Λ,
              onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)) +
          (∑ x : Λ, ∑ y : Λ,
              onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) =
          ∑ x : Λ, ∑ y : Λ,
            (onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
             onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) +
             onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) from by
    simp [Finset.sum_add_distrib]]
  rfl

/-- For trivial spin (`N = 0`), `(Ŝ_tot)² = 0` (every per-site
contribution vanishes). -/
theorem totalSpinSSquared_N_zero :
    (totalSpinSSquared Λ 0 : ManyBodyOpS Λ 0) = 0 := by
  rw [totalSpinSSquared_eq_sum_spinSDot]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  refine Finset.sum_eq_zero (fun y _ => ?_)
  exact spinSDot_N_zero_total x y

end LatticeSystem.Quantum
