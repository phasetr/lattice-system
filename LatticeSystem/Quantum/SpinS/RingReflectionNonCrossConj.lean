/-
The right-half gauge fixes the left and right bond Hamiltonians
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 28).

Summing the bond-invariance lemmas over the left and right bonds, the right-half gauge fixes both
the left bond Hamiltonian `ringLeftHamiltonian` and the reflected (right) bond Hamiltonian
`θ(ringLeftHamiltonian)`.  Only the two crossing bonds are affected; assembling the full gauge
image of the ring Hamiltonian is the next step.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondConj
import LatticeSystem.Quantum.SpinS.RingReflectionRightBondSum
import LatticeSystem.Quantum.SpinS.RingReflectionLeftBondSum

namespace LatticeSystem.Quantum

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- The right-half gauge fixes the left bond Hamiltonian. -/
theorem rightGauge_conj_ringLeftHamiltonian :
    G.rightGauge n * ringLeftHamiltonian n N * G.rightGaugeInv n = ringLeftHamiltonian n N := by
  rw [ringLeftHamiltonian_eq_leftBondSum, rightGauge_conj_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : (x : ℕ) + 1 < n
  · rw [if_pos hx]
    exact G.rightGauge_conj_spinSDot_left n (by omega)
      (by rw [ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]; omega)
  · rw [if_neg hx, mul_zero, zero_mul]

/-- The right-half gauge fixes the reflected (right) bond Hamiltonian `θ(ringLeftHamiltonian)`. -/
theorem rightGauge_conj_theta_ringLeftHamiltonian :
    G.rightGauge n * ringReflectionThetaS n N (ringLeftHamiltonian n N) * G.rightGaugeInv n
      = ringReflectionThetaS n N (ringLeftHamiltonian n N) := by
  rw [ringReflectionThetaS_ringLeftHamiltonian, rightGauge_conj_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : (x : ℕ) + 1 < n
  · rw [if_pos hx]
    refine G.rightGauge_conj_spinSDot_right n ?_ ?_
    · rw [ringReflect_val]; omega
    · rw [ringReflect_val, ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [if_neg hx, mul_zero, zero_mul]

end AxisTwoPiRotS

end LatticeSystem.Quantum
