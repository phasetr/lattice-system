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

/-! ## 2D Néel wrap-around bond actions -/

example (K L : ℕ) {j : ℕ} (hj : j < 2 * L) :
    (spinHalfDot
        ((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩) :
          Fin (2 * (K + 1)) × Fin (2 * L))
        ((⟨0, by omega⟩, ⟨j, hj⟩) :
          Fin (2 * (K + 1)) × Fin (2 * L))).mulVec
        (neelSquareState (K + 1) L) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelSquareConfig (K + 1) L)
            ((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩) :
              Fin (2 * (K + 1)) × Fin (2 * L))
            ((⟨0, by omega⟩, ⟨j, hj⟩) :
              Fin (2 * (K + 1)) × Fin (2 * L)))
        - (1 / 4 : ℂ) • neelSquareState (K + 1) L :=
  spinHalfDot_mulVec_neelSquareState_horizontal_wrap K L hj

example (K L : ℕ) {i : ℕ} (hi : i < 2 * K) :
    (spinHalfDot
        ((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩) :
          Fin (2 * K) × Fin (2 * (L + 1)))
        ((⟨i, hi⟩, ⟨0, by omega⟩) :
          Fin (2 * K) × Fin (2 * (L + 1)))).mulVec
        (neelSquareState K (L + 1)) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelSquareConfig K (L + 1))
            ((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩) :
              Fin (2 * K) × Fin (2 * (L + 1)))
            ((⟨i, hi⟩, ⟨0, by omega⟩) :
              Fin (2 * K) × Fin (2 * (L + 1))))
        - (1 / 4 : ℂ) • neelSquareState K (L + 1) :=
  spinHalfDot_mulVec_neelSquareState_vertical_wrap K L hi

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

/-! ## 3D Néel cubic-torus wrap-around bond actions -/

example (K L M : ℕ) {j k : ℕ}
    (hj : j < 2 * L) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
        (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState (K + 1) L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig (K + 1) L M)
            (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
            (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState (K + 1) L M :=
  spinHalfDot_mulVec_neelCubicState_x_wrap K L M hj hk

example (K L M : ℕ) {i k : ℕ}
    (hi : i < 2 * K) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
        (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))).mulVec
        (neelCubicState K (L + 1) M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K (L + 1) M)
            (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
            (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K (L + 1) M :=
  spinHalfDot_mulVec_neelCubicState_y_wrap K L M hi hk

example (K L M : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))).mulVec
        (neelCubicState K L (M + 1)) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L (M + 1))
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))) -
        (1 / 4 : ℂ) • neelCubicState K L (M + 1) :=
  spinHalfDot_mulVec_neelCubicState_z_wrap K L M hi hj

/-! ## 3D Néel state K = L = M = 1 time-reversal -/

example :
    timeReversalSpinHalfMulti (neelCubicState 1 1 1) =
      basisVec (flipConfig (neelCubicConfig 1 1 1)) :=
  timeReversalSpinHalfMulti_neelCubicState_one_one_one

/-! ## 3D Néel time-reversal at general `K, L, M` -/

example (K L M : ℕ) :
    timeReversalSpinHalfMulti (neelCubicState K L M) =
      basisVec (flipConfig (neelCubicConfig K L M)) :=
  timeReversalSpinHalfMulti_neelCubicState K L M

example :
    timeReversalSpinHalfMulti (neelCubicState 2 1 1) =
      basisVec (flipConfig (neelCubicConfig 2 1 1)) :=
  timeReversalSpinHalfMulti_neelCubicState 2 1 1

example :
    timeReversalSpinHalfMulti (neelCubicState 2 2 3) =
      basisVec (flipConfig (neelCubicConfig 2 2 3)) :=
  timeReversalSpinHalfMulti_neelCubicState 2 2 3

/-! ## Marshall sign on the parity-coloured chain -/

example (K : ℕ) :
    marshallSignChainConfig K (neelChainConfig K) = 1 :=
  marshallSignChainConfig_neelChainConfig K

example :
    marshallSignChainConfig 1 (neelChainConfig 1) = 1 :=
  marshallSignChainConfig_neelChainConfig 1

example :
    marshallSignChainConfig 2 (neelChainConfig 2) = 1 :=
  marshallSignChainConfig_neelChainConfig 2

example :
    marshallSignChainConfig 3 (neelChainConfig 3) = 1 :=
  marshallSignChainConfig_neelChainConfig 3

/-! ## Marshall sign on the 2D / 3D Néel configurations -/

example (K L : ℕ) :
    marshallSignSquareConfig K L (neelSquareConfig K L) = 1 :=
  marshallSignSquareConfig_neelSquareConfig K L

example :
    marshallSignSquareConfig 1 1 (neelSquareConfig 1 1) = 1 :=
  marshallSignSquareConfig_neelSquareConfig 1 1

example :
    marshallSignSquareConfig 2 3 (neelSquareConfig 2 3) = 1 :=
  marshallSignSquareConfig_neelSquareConfig 2 3

example (K L M : ℕ) :
    marshallSignCubicConfig K L M (neelCubicConfig K L M) = 1 :=
  marshallSignCubicConfig_neelCubicConfig K L M

example :
    marshallSignCubicConfig 1 1 1 (neelCubicConfig 1 1 1) = 1 :=
  marshallSignCubicConfig_neelCubicConfig 1 1 1

example :
    marshallSignCubicConfig 2 2 1 (neelCubicConfig 2 2 1) = 1 :=
  marshallSignCubicConfig_neelCubicConfig 2 2 1

/-! ## Graph-centric Marshall sign bridges -/

example (K : ℕ) (σ : Fin (2 * K) → Fin 2) :
    marshallSignChainConfig K σ =
      marshallSignOf
        (fun x : Fin (2 * K) => decide (x.val % 2 = 0)) σ :=
  marshallSignChainConfig_eq_marshallSignOf K σ

example (K L : ℕ) (σ : Fin (2 * K) × Fin (2 * L) → Fin 2) :
    marshallSignSquareConfig K L σ =
      marshallSignOf
        (fun p : Fin (2 * K) × Fin (2 * L) =>
          decide ((p.1.val + p.2.val) % 2 = 0)) σ :=
  marshallSignSquareConfig_eq_marshallSignOf K L σ

example (K L M : ℕ)
    (σ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) :
    marshallSignCubicConfig K L M σ =
      marshallSignOf
        (fun p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) =>
          decide ((p.1.1.val + p.1.2.val + p.2.val) % 2 = 0)) σ :=
  marshallSignCubicConfig_eq_marshallSignOf K L M σ

/-! ## Marshall sign on constant configurations -/

example (K : ℕ) :
    marshallSignChainConfig K (fun _ : Fin (2 * K) => (0 : Fin 2)) = 1 :=
  marshallSignChainConfig_const_zero K

example (K : ℕ) :
    marshallSignChainConfig K (fun _ : Fin (2 * K) => (1 : Fin 2)) =
      ((-1 : ℂ) ^ K) :=
  marshallSignChainConfig_const_one K

example :
    marshallSignChainConfig 1 (fun _ : Fin 2 => (1 : Fin 2)) = -1 := by
  rw [marshallSignChainConfig_const_one 1]; simp

example :
    marshallSignChainConfig 2 (fun _ : Fin 4 => (1 : Fin 2)) = 1 := by
  rw [marshallSignChainConfig_const_one 2]; simp

example (K L : ℕ) :
    marshallSignSquareConfig K L
        (fun _ : Fin (2 * K) × Fin (2 * L) => (0 : Fin 2)) = 1 :=
  marshallSignSquareConfig_const_zero K L

example (K L : ℕ) :
    marshallSignSquareConfig K L
        (fun _ : Fin (2 * K) × Fin (2 * L) => (1 : Fin 2)) = 1 :=
  marshallSignSquareConfig_const_one K L

example (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (fun _ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) =>
          (0 : Fin 2)) = 1 :=
  marshallSignCubicConfig_const_zero K L M

example (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (fun _ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) =>
          (1 : Fin 2)) = 1 :=
  marshallSignCubicConfig_const_one K L M

/-! ## Marshall sign under flipConfig -/

example (K : ℕ) (σ : Fin (2 * K) → Fin 2) :
    marshallSignChainConfig K (flipConfig σ) =
      ((-1 : ℂ) ^ K) * marshallSignChainConfig K σ :=
  marshallSignChainConfig_flipConfig K σ

example (K L : ℕ) (σ : Fin (2 * K) × Fin (2 * L) → Fin 2) :
    marshallSignSquareConfig K L (flipConfig σ) =
      marshallSignSquareConfig K L σ :=
  marshallSignSquareConfig_flipConfig K L σ

example (K L M : ℕ)
    (σ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) :
    marshallSignCubicConfig K L M (flipConfig σ) =
      marshallSignCubicConfig K L M σ :=
  marshallSignCubicConfig_flipConfig K L M σ

/-! ## Marshall-rotated states equal the Néel states -/

example (K : ℕ) :
    marshallChainState K (neelChainConfig K) = neelChainState K :=
  marshallChainState_neelChainConfig K

example (K L : ℕ) :
    marshallSquareState K L (neelSquareConfig K L) =
      neelSquareState K L :=
  marshallSquareState_neelSquareConfig K L

example (K L M : ℕ) :
    marshallCubicState K L M (neelCubicConfig K L M) =
      neelCubicState K L M :=
  marshallCubicState_neelCubicConfig K L M

/-! ## Marshall × time-reversal bridge -/

example (K : ℕ) :
    marshallSignChainConfig K (flipConfig (neelChainConfig K)) =
      (-1 : ℂ) ^ K :=
  marshallSignChainConfig_flipConfig_neelChainConfig K

example (K L : ℕ) :
    marshallSignSquareConfig K L (flipConfig (neelSquareConfig K L)) = 1 :=
  marshallSignSquareConfig_flipConfig_neelSquareConfig K L

example (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (flipConfig (neelCubicConfig K L M)) = 1 :=
  marshallSignCubicConfig_flipConfig_neelCubicConfig K L M

example (K : ℕ) :
    marshallChainState K (flipConfig (neelChainConfig K)) =
      timeReversalSpinHalfMulti (neelChainState K) :=
  marshallChainState_flipConfig_eq_timeReversalSpinHalfMulti K

example (K L : ℕ) :
    marshallSquareState K L (flipConfig (neelSquareConfig K L)) =
      timeReversalSpinHalfMulti (neelSquareState K L) :=
  marshallSquareState_flipConfig_eq_timeReversalSpinHalfMulti K L

example (K L M : ℕ) :
    marshallCubicState K L M (flipConfig (neelCubicConfig K L M)) =
      timeReversalSpinHalfMulti (neelCubicState K L M) :=
  marshallCubicState_flipConfig_eq_timeReversalSpinHalfMulti K L M

end LatticeSystem.Tests.NeelState
