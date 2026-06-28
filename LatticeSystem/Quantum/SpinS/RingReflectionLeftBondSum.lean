/-
The left-half bond Hamiltonian of the ring as a sum over left bonds
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 18).

The left coupling `ringLeftCoupling n` keeps the nearest-neighbor coupling only on bonds with both
endpoints in the left half.  Collapsing its double sum gives the left bond form
`ringLeftHamiltonian n N = ∑_x [if x+1 < n then Ŝ_x · Ŝ_{x+1} else 0]`: only the bonds `(x, x+1)`
entirely inside `{0, …, n−1}` survive.  This is the left part of the ring DLS decomposition,
expressed over its actual bonds.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSum

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The left coupling at a genuine left bond `(x, x+1)` (`x+1 < n`) is `1`. -/
theorem ringLeftCoupling_succ_of_lt {x : Fin (2 * n)} (hx : (x : ℕ) + 1 < n) :
    ringLeftCoupling n x (ringBondSucc n x) = 1 := by
  have hmod : (x.val + 1) % (2 * n) = x.val + 1 := Nat.mod_eq_of_lt (by omega)
  rw [ringLeftCoupling, if_pos ⟨by omega, by rw [ringBondSucc_val, hmod]; omega⟩,
    ringCoupling, if_pos (ringBondSucc_val x)]

/-- Off a genuine left bond, the left coupling vanishes: `ringLeftCoupling n x y = 0` for
`y ≠ ringBondSucc n x`. -/
theorem ringLeftCoupling_eq_zero_of_ne {x y : Fin (2 * n)} (hy : y ≠ ringBondSucc n x) :
    ringLeftCoupling n x y = 0 := by
  rw [ringLeftCoupling]
  split
  · rw [ringCoupling, if_neg]
    intro hcond
    exact hy (Fin.ext (by rw [ringBondSucc_val]; exact hcond))
  · rfl

/-- If `x+1 ≥ n` then the left coupling out of `x` vanishes for every `y`. -/
theorem ringLeftCoupling_eq_zero_of_not_lt {x : Fin (2 * n)} (hx : ¬ ((x : ℕ) + 1 < n))
    (y : Fin (2 * n)) : ringLeftCoupling n x y = 0 := by
  rw [ringLeftCoupling]
  split
  · rename_i h
    obtain ⟨hxn, hyn⟩ := h
    have hmod : (x.val + 1) % (2 * n) = x.val + 1 := Nat.mod_eq_of_lt (by omega)
    rw [ringCoupling, if_neg]
    intro hcond
    rw [hmod] at hcond
    omega
  · rfl

/-- **The left-half bond Hamiltonian as a sum over left bonds.**  Only the bonds `(x, x+1)` entirely
inside the left half survive. -/
theorem ringLeftHamiltonian_eq_leftBondSum (n N : ℕ) :
    ringLeftHamiltonian n N
      = ∑ x : Fin (2 * n), (if (x : ℕ) + 1 < n then spinSDot x (ringBondSucc n x) N else 0) := by
  rw [ringLeftHamiltonian, heisenbergHamiltonianS_def]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : (x : ℕ) + 1 < n
  · rw [if_pos hx, Finset.sum_eq_single (ringBondSucc n x)]
    · rw [ringLeftCoupling_succ_of_lt hx, one_smul]
    · intro y _ hy
      rw [ringLeftCoupling_eq_zero_of_ne hy, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hx]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [ringLeftCoupling_eq_zero_of_not_lt hx y, zero_smul]

end LatticeSystem.Quantum
