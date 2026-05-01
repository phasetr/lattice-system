import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteCommutator
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# SU(2) invariance: `[Ŝ_x · Ŝ_y, Ŝ_tot^{(α)}] = 0` (general spin)
(Tasaki §2.5 Phase B-β β-3m)

For any sites `x, y : Λ` and any axis `α ∈ {1, 2, 3}`, the two-site
spin-`S` dot product `Ŝ_x · Ŝ_y` commutes with the total spin
operator `Ŝ_tot^{(α)}`. This is the spin-`S` generalisation of
Tasaki §2.2 eq. (2.2.17).

We start with the **axis-3** case as the simplest of the three:
the diagonal nature of `Ŝ^{(3)}` makes the cancellation cleanest.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The Leibniz rule for commutators of products: `[A·B, T] = A·[B,T] + [A,T]·B`. -/
private lemma leibniz_commutatorS {N : ℕ} (A B T : ManyBodyOpS Λ N) :
    A * B * T - T * (A * B) = A * (B * T - T * B) + (A * T - T * A) * B := by
  rw [mul_sub, sub_mul]
  have h1 : A * (T * B) = A * T * B := (mul_assoc A T B).symm
  have h2 : A * B * T = A * (B * T) := mul_assoc A B T
  have h3 : T * (A * B) = T * A * B := (mul_assoc T A B).symm
  rw [h1, h2, h3]
  abel

/-- **SU(2) invariance, axis 3**: `[Ŝ_x · Ŝ_y, Ŝ_tot^{(3)}] = 0`.

Spin-`S` generalisation of Tasaki §2.2 eq. (2.2.17), axis 3. -/
theorem spinSDot_commutator_totalSpinSOp3 (x y : Λ) (N : ℕ) :
    spinSDot x y N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * spinSDot x y N = 0 := by
  unfold spinSDot totalSpinSOp3
  set T := (∑ z : Λ, onSiteS z (spinSOp3 N) : ManyBodyOpS Λ N)
  have distrib : ∀ (A B C : ManyBodyOpS Λ N),
      (A + B + C) * T - T * (A + B + C) =
        (A * T - T * A) + (B * T - T * B) + (C * T - T * C) := by
    intros A B C
    rw [add_mul, add_mul, mul_add, mul_add]; abel
  rw [distrib]
  set a1 := (onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) : ManyBodyOpS Λ N)
  set a2 := (onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) : ManyBodyOpS Λ N)
  set a3 := (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) : ManyBodyOpS Λ N)
  have h1 : a1 * T - T * a1 =
      onSiteS x (spinSOp1 N) *
          onSiteS y (spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N) +
        onSiteS x (spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N) *
          onSiteS y (spinSOp1 N) := by
    change onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) * T
        - T * (onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N)) = _
    rw [leibniz_commutatorS]
    rw [onSiteS_commutator_totalOnSiteS y (spinSOp1 N) (spinSOp3 N),
        onSiteS_commutator_totalOnSiteS x (spinSOp1 N) (spinSOp3 N)]
  have h2 : a2 * T - T * a2 =
      onSiteS x (spinSOp2 N) *
          onSiteS y (spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N) +
        onSiteS x (spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N) *
          onSiteS y (spinSOp2 N) := by
    change onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) * T
        - T * (onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)) = _
    rw [leibniz_commutatorS]
    rw [onSiteS_commutator_totalOnSiteS y (spinSOp2 N) (spinSOp3 N),
        onSiteS_commutator_totalOnSiteS x (spinSOp2 N) (spinSOp3 N)]
  have h3 : a3 * T - T * a3 = 0 := by
    change onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) * T
        - T * (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) = 0
    rw [leibniz_commutatorS]
    rw [onSiteS_commutator_totalOnSiteS y (spinSOp3 N) (spinSOp3 N),
        onSiteS_commutator_totalOnSiteS x (spinSOp3 N) (spinSOp3 N)]
    rw [sub_self]
    simp [onSiteS_zero]
  rw [h1, h2, h3]
  -- Substitute single-site commutators
  rw [show spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N =
      -(Complex.I • spinSOp2 N) from by
    rw [show spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N =
        -(spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N) from by abel,
      spinSOp3_commutator_spinSOp1]]
  rw [spinSOp2_commutator_spinSOp3]
  rw [onSiteS_smul, onSiteS_smul]
  rw [show onSiteS x (-(Complex.I • spinSOp2 N) :
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
      -(Complex.I • onSiteS (Λ := Λ) (N := N) x (spinSOp2 N)) from by
    rw [show -(Complex.I • spinSOp2 N :
        Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-Complex.I) • spinSOp2 N from by rw [neg_smul]]
    rw [onSiteS_smul]
    rw [neg_smul]]
  rw [show onSiteS y (-(Complex.I • spinSOp2 N) :
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
      -(Complex.I • onSiteS (Λ := Λ) (N := N) y (spinSOp2 N)) from by
    rw [show -(Complex.I • spinSOp2 N :
        Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-Complex.I) • spinSOp2 N from by rw [neg_smul]]
    rw [onSiteS_smul]
    rw [neg_smul]]
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_mul_assoc]
  abel

end LatticeSystem.Quantum
