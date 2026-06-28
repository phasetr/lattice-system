/-
The right bond Hamiltonian equals the reflection of the left bond Hamiltonian
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 22).

The right bonds of the ring are exactly the reflections of the left bonds: reindexing by the
bijection `x ↦ r(x+1)` (reflection of the cyclic successor) and using the symmetry of `Ŝ_x · Ŝ_y`,
`ringRightBondSum = θ(ringLeftHamiltonian)`.  This identifies the right part of the bond split with
the `θ(H_L)` term of the DLS decomposition.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSplit
import LatticeSystem.Quantum.SpinS.RingReflectionRightBondSum

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The cyclic successor is `+1` in `Fin (2n)`. -/
theorem ringBondSucc_eq_add_one [NeZero n] (x : Fin (2 * n)) :
    ringBondSucc n x = x + 1 := by
  apply Fin.ext
  rw [ringBondSucc_val, Fin.add_def, Fin.val_one']
  have h2n : 1 < 2 * n := by have := Nat.pos_of_ne_zero (NeZero.ne n); omega
  rw [Nat.mod_eq_of_lt h2n]

/-- The cyclic successor on the ring is a bijection. -/
theorem ringBondSucc_bijective [NeZero n] : Function.Bijective (ringBondSucc (n := n)) := by
  have h : ringBondSucc n = fun x : Fin (2 * n) => x + 1 := funext ringBondSucc_eq_add_one
  rw [h]
  exact (Equiv.addRight (1 : Fin (2 * n))).bijective

/-- **The right bond Hamiltonian is the reflection of the left bond Hamiltonian.** -/
theorem ringRightBondSum_eq_theta (n N : ℕ) [NeZero n] :
    ringRightBondSum n N = ringReflectionThetaS n N (ringLeftHamiltonian n N) := by
  rw [ringRightBondSum, ringReflectionThetaS_ringLeftHamiltonian]
  refine Fintype.sum_bijective (fun x => ringReflect n (ringBondSucc n x))
    ((ringReflect_bijective n).comp ringBondSucc_bijective) _ _ (fun x => ?_)
  have hlt := x.isLt
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hr : n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n
  · obtain ⟨hge, hlt2⟩ := hr
    have hs : (ringBondSucc n x).val = (x : ℕ) + 1 := by
      rw [ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]
    -- reflection of the successor is left-supported and the bond matches `x`
    have heval : (ringReflect n (ringBondSucc n x)).val + 1 < n := by
      rw [ringReflect_val, hs]; omega
    have hrefl1 : ringReflect n (ringReflect n (ringBondSucc n x)) = ringBondSucc n x :=
      ringReflect_involutive n _
    have hrefl2 : ringReflect n (ringBondSucc n (ringReflect n (ringBondSucc n x))) = x := by
      apply Fin.ext
      rw [ringReflect_val, ringBondSucc_val, ringReflect_val, hs,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_pos ⟨hge, hlt2⟩, if_pos heval, hrefl1, hrefl2, spinSDot_comm]
  · rw [if_neg hr]
    have hne : ¬ ((ringReflect n (ringBondSucc n x)).val + 1 < n) := by
      rw [ringReflect_val, ringBondSucc_val]
      rcases Nat.lt_or_ge (x : ℕ) n with hx | hx
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · -- x ≥ n; not right means x+1 ≥ 2n, i.e. x = 2n-1
        have hx1 : (x : ℕ) = 2 * n - 1 := by omega
        rw [hx1]; rw [show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]; omega
    rw [if_neg hne]

end LatticeSystem.Quantum
