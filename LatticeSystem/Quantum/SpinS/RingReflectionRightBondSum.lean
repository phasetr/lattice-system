/-
The reflected left bond Hamiltonian is the right bond Hamiltonian
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 19).

Applying the reflection map `θ` to the left bond Hamiltonian reflects each left bond `(x, x+1)` to a
right bond `(r x, r (x+1)) = (2n−1−x, 2n−2−x)`:
`θ(ringLeftHamiltonian) = ∑_x [if x+1 < n then Ŝ_{r x} · Ŝ_{r (x+1)} else 0]`.  This is the right
part `θ(H_L)` of the ring DLS decomposition, expressed over the reflected (right-half) bonds.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionLeftBondSum

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **The reflected left bond Hamiltonian as a right bond sum.**  `θ` maps each surviving left bond
`(x, x+1)` to the reflected right bond `(r x, r (x+1))`. -/
theorem ringReflectionThetaS_ringLeftHamiltonian (n N : ℕ) :
    ringReflectionThetaS n N (ringLeftHamiltonian n N)
      = ∑ x : Fin (2 * n), (if (x : ℕ) + 1 < n then
          spinSDot (ringReflect n x) (ringReflect n (ringBondSucc n x)) N else 0) := by
  rw [ringLeftHamiltonian_eq_leftBondSum, ringReflectionThetaS_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : (x : ℕ) + 1 < n
  · rw [if_pos hx, if_pos hx, ringReflectionThetaS_spinSDot]
  · rw [if_neg hx, if_neg hx, ringReflectionThetaS_zero]

end LatticeSystem.Quantum
