/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState

/-!
# Test coverage for the Néel chain state (Tasaki §2.5)
-/

namespace LatticeSystem.Tests.NeelState

open LatticeSystem.Quantum

/-! ## Configuration values at small chain lengths -/

example : neelChainConfig 1 ⟨0, by decide⟩ = (0 : Fin 2) := by
  decide
example : neelChainConfig 1 ⟨1, by decide⟩ = (1 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨0, by decide⟩ = (0 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨1, by decide⟩ = (1 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨2, by decide⟩ = (0 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨3, by decide⟩ = (1 : Fin 2) := by
  decide

/-! ## Magnetisation = 0 -/

example : magnetization (Fin (2 * 1)) (neelChainConfig 1) = 0 :=
  neelChainConfig_magnetization_zero 1
example : magnetization (Fin (2 * 2)) (neelChainConfig 2) = 0 :=
  neelChainConfig_magnetization_zero 2
example : magnetization (Fin (2 * 3)) (neelChainConfig 3) = 0 :=
  neelChainConfig_magnetization_zero 3

/-! ## Membership in the zero-magnetisation sector `H_0` -/

example : neelChainState 1 ∈ magnetizationSubspace (Fin (2 * 1)) (0 : ℂ) :=
  neelChainState_mem_magnetizationSubspace_zero 1
example : neelChainState 2 ∈ magnetizationSubspace (Fin (2 * 2)) (0 : ℂ) :=
  neelChainState_mem_magnetizationSubspace_zero 2
example : neelChainState 3 ∈ magnetizationSubspace (Fin (2 * 3)) (0 : ℂ) :=
  neelChainState_mem_magnetizationSubspace_zero 3

/-! ## H · |Φ_Néel⟩ stays in `H_0` (SU(2) invariance corollary) -/

example (K : ℕ) (J : Fin (2 * K) → Fin (2 * K) → ℂ) :
    (heisenbergHamiltonian J).mulVec (neelChainState K) ∈
      magnetizationSubspace (Fin (2 * K)) (0 : ℂ) :=
  heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero K J

example (J : Fin (2 * 2) → Fin (2 * 2) → ℂ) :
    (heisenbergHamiltonian J).mulVec (neelChainState 2) ∈
      magnetizationSubspace (Fin (2 * 2)) (0 : ℂ) :=
  heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero 2 J

/-! ## Adjacent-bond action `Ŝ_x · Ŝ_y · |Φ_Néel⟩` -/

example (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    (spinHalfDot
        (⟨i, by omega⟩ : Fin (2 * K))
        (⟨i + 1, hi⟩ : Fin (2 * K))).mulVec (neelChainState K) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig K)
            (⟨i, by omega⟩ : Fin (2 * K))
            (⟨i + 1, hi⟩ : Fin (2 * K)))
        - (1 / 4 : ℂ) • neelChainState K :=
  spinHalfDot_mulVec_neelChainState_adjacent K hi

example :
    (spinHalfDot
        (⟨0, by decide⟩ : Fin (2 * 2))
        (⟨1, by decide⟩ : Fin (2 * 2))).mulVec (neelChainState 2) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig 2)
            (⟨0, by decide⟩ : Fin (2 * 2))
            (⟨1, by decide⟩ : Fin (2 * 2)))
        - (1 / 4 : ℂ) • neelChainState 2 :=
  spinHalfDot_mulVec_neelChainState_adjacent 2 (by decide)

/-! ## Wrap-around bond `(2K + 1, 0)` action on the periodic chain -/

example (K : ℕ) :
    (spinHalfDot
        (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
        (⟨0, by omega⟩ : Fin (2 * (K + 1)))).mulVec
        (neelChainState (K + 1)) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig (K + 1))
            (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
            (⟨0, by omega⟩ : Fin (2 * (K + 1))))
        - (1 / 4 : ℂ) • neelChainState (K + 1) :=
  spinHalfDot_mulVec_neelChainState_wrap K

example :
    (spinHalfDot
        (⟨3, by decide⟩ : Fin (2 * 2))
        (⟨0, by decide⟩ : Fin (2 * 2))).mulVec (neelChainState 2) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig 2)
            (⟨3, by decide⟩ : Fin (2 * 2))
            (⟨0, by decide⟩ : Fin (2 * 2)))
        - (1 / 4 : ℂ) • neelChainState 2 :=
  spinHalfDot_mulVec_neelChainState_wrap 1

/-! ## `H_open(N=1, J) · |Φ_Néel(K=1)⟩ = -J · |↓↑⟩ + (J/2) · |Φ_Néel⟩` -/

example (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (neelChainState 1) =
      (-(J : ℂ)) • basisVec
          (basisSwap (neelChainConfig 1)
            (⟨0, by decide⟩ : Fin (2 * 1))
            (⟨1, by decide⟩ : Fin (2 * 1))) +
        ((J : ℂ) / 2) • neelChainState 1 :=
  heisenbergHamiltonian_openChainCoupling_one_mulVec_neelChainState_one J

/-! ## K = 1 bridge to `upDown` and time-reversal action -/

example : neelChainConfig 1 = upDown := neelChainConfig_one_eq_upDown

example :
    timeReversalSpinHalfMulti (neelChainState 1) =
      -basisVec (basisSwap upDown 0 1) :=
  timeReversalSpinHalfMulti_neelChainState_one

/-! ## 1D Néel time-reversal action at general `K` -/

example (K : ℕ) :
    timeReversalSpinHalfMulti (neelChainState K) =
      ((-1 : ℂ) ^ K) • basisVec (flipConfig (neelChainConfig K)) :=
  timeReversalSpinHalfMulti_neelChainState K

/-- Specialisation: at `K = 2` (4-site chain), the sign factor
`(-1)^2 = 1` makes the action sign-free. -/
example :
    timeReversalSpinHalfMulti (neelChainState 2) =
      basisVec (flipConfig (neelChainConfig 2)) := by
  rw [timeReversalSpinHalfMulti_neelChainState 2]
  simp

/-- Specialisation: at `K = 3` (6-site chain), the sign factor
`(-1)^3 = -1`. -/
example :
    timeReversalSpinHalfMulti (neelChainState 3) =
      -basisVec (flipConfig (neelChainConfig 3)) := by
  rw [timeReversalSpinHalfMulti_neelChainState 3]
  simp [show ((-1 : ℂ) ^ 3) = -1 from by norm_num]

/-! ## 2D checkerboard Néel state -/

example (K L : ℕ) :
    magnetization (Fin (2 * K) × Fin (2 * L))
        (neelSquareConfig K L) = 0 :=
  neelSquareConfig_magnetization_zero K L

example (K L : ℕ) :
    neelSquareState K L ∈
      magnetizationSubspace (Fin (2 * K) × Fin (2 * L)) (0 : ℂ) :=
  neelSquareState_mem_magnetizationSubspace_zero K L

example :
    magnetization (Fin (2 * 1) × Fin (2 * 1))
        (neelSquareConfig 1 1) = 0 :=
  neelSquareConfig_magnetization_zero 1 1

example :
    neelSquareState 2 2 ∈
      magnetizationSubspace (Fin (2 * 2) × Fin (2 * 2)) (0 : ℂ) :=
  neelSquareState_mem_magnetizationSubspace_zero 2 2

/-! ## 2D Néel per-bond actions -/

example (K L : ℕ) {i j : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) :
    (spinHalfDot
        ((⟨i, by omega⟩, ⟨j, hj⟩) :
          Fin (2 * K) × Fin (2 * L))
        ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
          Fin (2 * K) × Fin (2 * L))).mulVec
        (neelSquareState K L) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelSquareConfig K L)
            ((⟨i, by omega⟩, ⟨j, hj⟩) :
              Fin (2 * K) × Fin (2 * L))
            ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
              Fin (2 * K) × Fin (2 * L)))
        - (1 / 4 : ℂ) • neelSquareState K L :=
  spinHalfDot_mulVec_neelSquareState_horizontal_adjacent K L hi hj

example (K L : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) :
    (spinHalfDot
        ((⟨i, hi⟩, ⟨j, by omega⟩) :
          Fin (2 * K) × Fin (2 * L))
        ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
          Fin (2 * K) × Fin (2 * L))).mulVec
        (neelSquareState K L) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelSquareConfig K L)
            ((⟨i, hi⟩, ⟨j, by omega⟩) :
              Fin (2 * K) × Fin (2 * L))
            ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
              Fin (2 * K) × Fin (2 * L))) -
        (1 / 4 : ℂ) • neelSquareState K L :=
  spinHalfDot_mulVec_neelSquareState_vertical_adjacent K L hi hj

/-! ## 2D Néel state K = L = 1 time-reversal -/

example :
    timeReversalSpinHalfMulti (neelSquareState 1 1) =
      basisVec (flipConfig (neelSquareConfig 1 1)) :=
  timeReversalSpinHalfMulti_neelSquareState_one_one

/-! ## 2D Néel time-reversal at general `K, L` -/

example (K L : ℕ) :
    timeReversalSpinHalfMulti (neelSquareState K L) =
      basisVec (flipConfig (neelSquareConfig K L)) :=
  timeReversalSpinHalfMulti_neelSquareState K L

example :
    timeReversalSpinHalfMulti (neelSquareState 2 1) =
      basisVec (flipConfig (neelSquareConfig 2 1)) :=
  timeReversalSpinHalfMulti_neelSquareState 2 1

example :
    timeReversalSpinHalfMulti (neelSquareState 2 3) =
      basisVec (flipConfig (neelSquareConfig 2 3)) :=
  timeReversalSpinHalfMulti_neelSquareState 2 3

/-! ## 3D cubic Néel state -/

example (K L M : ℕ) :
    magnetization
        ((Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (neelCubicConfig K L M) = 0 :=
  neelCubicConfig_magnetization_zero K L M

example (K L M : ℕ) :
    neelCubicState K L M ∈
      magnetizationSubspace
        ((Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (0 : ℂ) :=
  neelCubicState_mem_magnetizationSubspace_zero K L M

example :
    neelCubicState 1 1 1 ∈
      magnetizationSubspace
        ((Fin (2 * 1) × Fin (2 * 1)) × Fin (2 * 1))
        (0 : ℂ) :=
  neelCubicState_mem_magnetizationSubspace_zero 1 1 1

/-! ## 3D Néel state K = L = M = 1 time-reversal -/

example :
    timeReversalSpinHalfMulti (neelCubicState 1 1 1) =
      basisVec (flipConfig (neelCubicConfig 1 1 1)) :=
  timeReversalSpinHalfMulti_neelCubicState_one_one_one

end LatticeSystem.Tests.NeelState
