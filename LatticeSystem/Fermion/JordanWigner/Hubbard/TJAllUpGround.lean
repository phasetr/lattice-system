import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingExchange
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAllUpSpinDot

/-!
# Tasaki 11.5.3: the t-J Hamiltonian annihilates the all-up state (Theorem 11.26 PR3b)

The all-up state `|↑…↑⟩` is the half-filling (`Ne = N+1`) maximal-spin configuration.  Each exchange
bond `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y` vanishes on it (`¼·1 − ¼ = 0`, by `fermionSpinDot_mulVec_allUpState`),
so
`tJExchange |↑…↑⟩ = 0`, and since the kinetic term also vanishes at half-filling (#4315/#4316):

* `tJHamiltonian_mulVec_allUpState_eq_zero` — `Ĥ_tJ |↑…↑⟩ = 0`.

So `|↑…↑⟩` is a zero-energy eigenstate; combined with positive-semidefiniteness of the exchange term
(a later step) this identifies it as a maximal-spin ground state of the half-filling ferromagnetic
Heisenberg model.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- `n̂_x |↑…↑⟩ = |↑…↑⟩`: site `x` carries exactly one (up) electron. -/
theorem fermionSiteNumber_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionSiteNumber N i).mulVec (hubbardAllUpState N) = hubbardAllUpState N := by
  rw [fermionSiteNumber, Matrix.add_mulVec, fermionUpNumber_mulVec_allUpState,
    fermionDownNumber_mulVec_allUpState, add_zero]

/-- The all-up state is the all-up sector config: `|↑…↑⟩ = basisVec (tJConfigOf (fun _ ↦ 1))`. -/
theorem hubbardAllUpState_eq_tJConfigOf (N : ℕ) :
    hubbardAllUpState N = basisVec (tJConfigOf N (fun _ => 1)) := by
  rw [hubbardAllUpState]
  congr 1

/-- The exchange term annihilates the all-up state: each bond `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y` gives
`¼ − ¼ = 0` on `|↑…↑⟩`. -/
theorem tJExchange_mulVec_allUpState_eq_zero (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] :
    (tJExchange N G).mulVec (hubbardAllUpState N) = 0 := by
  rw [tJExchange, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hadj : G.Adj x y
  · rw [if_pos hadj, Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      fermionSiteNumber_mulVec_allUpState, fermionSiteNumber_mulVec_allUpState,
      fermionSpinDot_mulVec_allUpState N x y hadj.ne, sub_self]
  · rw [if_neg hadj, Matrix.zero_mulVec]

/-- **The t-J Hamiltonian annihilates the all-up state.**  At half-filling the kinetic term vanishes
(#4315/#4316) and the exchange term vanishes on `|↑…↑⟩`, so `Ĥ_tJ |↑…↑⟩ = 0`. -/
theorem tJHamiltonian_mulVec_allUpState_eq_zero (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    (tJHamiltonian N G τ J).mulVec (hubbardAllUpState N) = 0 := by
  rw [hubbardAllUpState_eq_tJConfigOf,
    tJHamiltonian_mulVec_tJConfigOf_eq_of_full N G τ J (fun _ => 1)
      (fun _ => (by decide : (1 : Fin 3) ≠ 0)),
    ← hubbardAllUpState_eq_tJConfigOf, tJExchange_mulVec_allUpState_eq_zero, smul_zero]

end LatticeSystem.Fermion
