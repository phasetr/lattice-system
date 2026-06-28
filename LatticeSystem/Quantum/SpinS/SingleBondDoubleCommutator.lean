/-
The per-bond double commutator with `Ŝ^{(3)}` is the transverse bond energy
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Applying `Ŝ_a^{(3)}` once more to the single-bond spin current gives the f-sum-rule integrand: the
double commutator `[Ŝ_a^{(3)}, [Ŝ_a·Ŝ_b, Ŝ_a^{(3)}]] = −(Ŝ_a^{(1)}Ŝ_b^{(1)} + Ŝ_a^{(2)}Ŝ_b^{(2)})`
is the (negated) transverse bond energy.  Summed over the ring this is the "oscillator strength" of
the staggered mode, the numerator of the infrared / f-sum-rule bound on the staggered two-point
function, which is bounded by the bond energy (hence `O(L)`).
-/
import LatticeSystem.Quantum.SpinS.SingleBondSpinSOp3Commutator

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The per-bond double commutator is the negated transverse bond energy**:
`[Ŝ_a^{(3)}, [Ŝ_a · Ŝ_b, Ŝ_a^{(3)}]] = −(Ŝ_a^{(1)} Ŝ_b^{(1)} + Ŝ_a^{(2)} Ŝ_b^{(2)})` for `a ≠ b`. -/
theorem spinSDot_double_commutator_onSiteS_spinSOp3 {a b : Λ} (hab : a ≠ b) (N : ℕ) :
    onSiteS a (spinSOp3 N)
        * (spinSDot a b N * onSiteS a (spinSOp3 N) - onSiteS a (spinSOp3 N) * spinSDot a b N)
      - (spinSDot a b N * onSiteS a (spinSOp3 N) - onSiteS a (spinSOp3 N) * spinSDot a b N)
        * onSiteS a (spinSOp3 N)
      = -(onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N)
          + onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N)) := by
  rw [spinSDot_commutator_onSiteS_spinSOp3 hab]
  -- the cross-site commutation: Ŝ_a^{(3)} commutes with Ŝ_b^{(α)}
  have cb1 : onSiteS b (spinSOp1 N) * onSiteS a (spinSOp3 N)
      = onSiteS a (spinSOp3 N) * onSiteS b (spinSOp1 N) :=
    (onSiteS_commute_of_ne (Ne.symm hab) _ _).eq
  have cb2 : onSiteS b (spinSOp2 N) * onSiteS a (spinSOp3 N)
      = onSiteS a (spinSOp3 N) * onSiteS b (spinSOp2 N) :=
    (onSiteS_commute_of_ne (Ne.symm hab) _ _).eq
  -- [Ŝ_a^{(3)}, Ŝ_a^{(1)} Ŝ_b^{(2)}] = i (Ŝ_a^{(2)} Ŝ_b^{(2)})
  have hc1 : onSiteS a (spinSOp3 N) * (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N))
        - onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N) * onSiteS a (spinSOp3 N)
      = I • (onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N)) := by
    rw [mul_assoc, cb2, ← mul_assoc, ← mul_assoc, ← sub_mul, onSiteS_commutator_same,
      show spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N = I • spinSOp2 N from
        spinSOp3_commutator_spinSOp1 N, onSiteS_smul, smul_mul_assoc]
  -- [Ŝ_a^{(3)}, Ŝ_a^{(2)} Ŝ_b^{(1)}] = -i (Ŝ_a^{(1)} Ŝ_b^{(1)})
  have hc2 : onSiteS a (spinSOp3 N) * (onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N))
        - onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N) * onSiteS a (spinSOp3 N)
      = -(I • (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N))) := by
    rw [mul_assoc, cb1, ← mul_assoc, ← mul_assoc, ← sub_mul, onSiteS_commutator_same,
      show spinSOp3 N * spinSOp2 N - spinSOp2 N * spinSOp3 N = -(I • spinSOp1 N) from by
        rw [show spinSOp3 N * spinSOp2 N - spinSOp2 N * spinSOp3 N
            = -(spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N) from by abel,
          spinSOp2_commutator_spinSOp3], onSiteS_neg, onSiteS_smul, neg_mul, smul_mul_assoc]
  have hin : onSiteS a (spinSOp3 N)
        * (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N)
          - onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N))
      - (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N)
          - onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N)) * onSiteS a (spinSOp3 N)
      = I • (onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N))
        + I • (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N)) := by
    rw [mul_sub, sub_mul, sub_sub_sub_comm, hc1, hc2, sub_neg_eq_add]
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hin, smul_add, smul_smul, smul_smul,
    Complex.I_mul_I, neg_one_smul, neg_one_smul]
  abel

end LatticeSystem.Quantum
