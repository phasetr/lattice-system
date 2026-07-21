/-
The single-bond commutator of a Heisenberg bond with a single-site `Ŝ^{(3)}`
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The commutator of one Heisenberg bond `Ŝ_a · Ŝ_b` with the single-site spin `Ŝ_a^{(3)}` is the spin
current `[Ŝ_a · Ŝ_b, Ŝ_a^{(3)}] = i (Ŝ_a^{(1)} Ŝ_b^{(2)} − Ŝ_a^{(2)} Ŝ_b^{(1)})` (for `a ≠ b`): only
the two transverse components of the bond fail to commute with `Ŝ_a^{(3)}`, contributing the cyclic
SU(2) factor.  This is the building block of `[Ĥ, Ŝ_z^{(3)}]` (the spin-current divergence) and the
double commutator entering the infrared / f-sum-rule bound on the staggered two-point function.
-/
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteCommutator
import LatticeSystem.Quantum.SpinS.CyclicCommutator

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Leibniz rule for the commutator with a third operator:
`[A·B, T] = A·[B, T] + [A, T]·B`. -/
private lemma leibniz_commutatorS (A B T : ManyBodyOpS Λ N) :
    A * B * T - T * (A * B) = A * (B * T - T * B) + (A * T - T * A) * B := by
  rw [mul_sub, sub_mul, mul_assoc, mul_assoc, mul_assoc]; abel

/-- The commutator of two single-site operators at **different** sites vanishes. -/
private theorem onSiteS_commutator_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) * onSiteS j B - onSiteS j B * onSiteS i A = 0 := by
  rw [(onSiteS_commute_of_ne hij A B).eq, sub_self]

/-- **Off-bond vanishing**: a Heisenberg bond `Ŝ_x · Ŝ_y` commutes with `Ŝ_z^{(3)}` when `z` lies on
neither endpoint (`z ≠ x`, `z ≠ y`), so the commutator vanishes. -/
theorem spinSDot_commutator_onSiteS_spinSOp3_eq_zero_of_ne {x y z : Λ} (hzx : z ≠ x) (hzy : z ≠ y)
    (N : ℕ) :
    spinSDot x y N * onSiteS z (spinSOp3 N) - onSiteS z (spinSOp3 N) * spinSDot x y N = 0 := by
  have h : Commute (spinSDot x y N) (onSiteS z (spinSOp3 N) : ManyBodyOpS Λ N) := by
    rw [spinSDot_def]
    have cx : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
        Commute (onSiteS x A : ManyBodyOpS Λ N) (onSiteS z (spinSOp3 N)) :=
      fun A => onSiteS_commute_of_ne (Ne.symm hzx) A (spinSOp3 N)
    have cy : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
        Commute (onSiteS y A : ManyBodyOpS Λ N) (onSiteS z (spinSOp3 N)) :=
      fun A => onSiteS_commute_of_ne (Ne.symm hzy) A (spinSOp3 N)
    exact (((cx _).mul_left (cy _)).add_left ((cx _).mul_left (cy _))).add_left
      ((cx _).mul_left (cy _))
  rw [h.eq, sub_self]

/-- **The single-bond spin current**: `[Ŝ_a · Ŝ_b, Ŝ_a^{(3)}] = i (Ŝ_a^{(1)} Ŝ_b^{(2)} −
Ŝ_a^{(2)} Ŝ_b^{(1)})` for `a ≠ b`.  Only the transverse bond components fail to commute with
`Ŝ_a^{(3)}`. -/
theorem spinSDot_commutator_onSiteS_spinSOp3 {a b : Λ} (hab : a ≠ b) (N : ℕ) :
    spinSDot a b N * onSiteS a (spinSOp3 N) - onSiteS a (spinSOp3 N) * spinSDot a b N
      = I • (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N)
          - onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N)) := by
  rw [spinSDot_def]
  set T := (onSiteS a (spinSOp3 N) : ManyBodyOpS Λ N)
  have distrib : ∀ (A B C : ManyBodyOpS Λ N),
      (A + B + C) * T - T * (A + B + C)
        = (A * T - T * A) + (B * T - T * B) + (C * T - T * C) := by
    intros A B C; rw [add_mul, add_mul, mul_add, mul_add]; abel
  rw [distrib]
  -- transverse term 1
  have h1 : onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N) * T
        - T * (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N))
      = onSiteS a (spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N) * onSiteS b (spinSOp1 N) := by
    rw [leibniz_commutatorS, onSiteS_commutator_of_ne (Ne.symm hab), mul_zero, zero_add,
      onSiteS_commutator_same]
  -- transverse term 2
  have h2 : onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N) * T
        - T * (onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N))
      = onSiteS a (spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N) * onSiteS b (spinSOp2 N) := by
    rw [leibniz_commutatorS, onSiteS_commutator_of_ne (Ne.symm hab), mul_zero, zero_add,
      onSiteS_commutator_same]
  -- longitudinal term vanishes
  have h3 : onSiteS a (spinSOp3 N) * onSiteS b (spinSOp3 N) * T
        - T * (onSiteS a (spinSOp3 N) * onSiteS b (spinSOp3 N)) = 0 := by
    rw [leibniz_commutatorS, onSiteS_commutator_of_ne (Ne.symm hab), mul_zero, zero_add,
      onSiteS_commutator_same, sub_self, onSiteS_zero, zero_mul]
  rw [h1, h2, h3, add_zero]
  -- substitute the SU(2) commutators
  rw [show spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N = -(I • spinSOp2 N) from by
      rw [show spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N
          = -(spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N) from by abel,
        spinSOp3_commutator_spinSOp1],
    spinSOp2_commutator_spinSOp3]
  rw [onSiteS_neg, onSiteS_smul, onSiteS_smul, neg_mul, smul_mul_assoc, smul_mul_assoc, smul_sub]
  abel

/-- **The single-bond spin current at the right endpoint**: `[Ŝ_a · Ŝ_b, Ŝ_b^{(3)}] =
i (Ŝ_b^{(1)} Ŝ_a^{(2)} − Ŝ_b^{(2)} Ŝ_a^{(1)})` for `a ≠ b`, the companion of
`spinSDot_commutator_onSiteS_spinSOp3` (via the symmetry `Ŝ_a · Ŝ_b = Ŝ_b · Ŝ_a`). -/
theorem spinSDot_commutator_onSiteS_spinSOp3_right {a b : Λ} (hab : a ≠ b) (N : ℕ) :
    spinSDot a b N * onSiteS b (spinSOp3 N) - onSiteS b (spinSOp3 N) * spinSDot a b N
      = I • (onSiteS b (spinSOp1 N) * onSiteS a (spinSOp2 N)
          - onSiteS b (spinSOp2 N) * onSiteS a (spinSOp1 N)) := by
  rw [spinSDot_comm a b]
  exact spinSDot_commutator_onSiteS_spinSOp3 (Ne.symm hab) N

end LatticeSystem.Quantum
