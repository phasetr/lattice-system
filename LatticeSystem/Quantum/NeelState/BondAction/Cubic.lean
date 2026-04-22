/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition3D

/-!
# 3D cubic Néel checkerboard bond actions (Tasaki §2.5)

Per-bond `Ŝ_x · Ŝ_y` action on the 3D cubic Néel state, both
for the three nearest-neighbour bond axes (x / y / z) and for
the corresponding wrap-around (cubic torus) bonds.

(Refactor Phase 2 PR 6 — sixth step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

/-- 3D x-axis bond `((i,j,k), (i+1,j,k))`: antiparallel under
the 3D checkerboard. Same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩`
decomposition. -/
theorem spinHalfDot_mulVec_neelCubicState_x_adjacent
    (K L M : ℕ) {i j k : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState K L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L M)
            (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
            (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K L M := by
  rw [neelCubicState_eq_neelStateOf, neelCubicConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D y-axis bond `((i,j,k), (i,j+1,k))`. -/
theorem spinHalfDot_mulVec_neelCubicState_y_adjacent
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState K L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L M)
            (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
            (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K L M := by
  rw [neelCubicState_eq_neelStateOf, neelCubicConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + (j + 1) + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1) + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D z-axis bond `((i,j,k), (i,j,k+1))`. -/
theorem spinHalfDot_mulVec_neelCubicState_z_adjacent
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) (hk : k + 1 < 2 * M) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState K L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L M)
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K L M := by
  rw [neelCubicState_eq_neelStateOf, neelCubicConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + j + (k + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + j + (k + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D x-axis wrap-around bond `((2K + 1, j), k) ~ ((0, j), k)`
on the 3D Néel state over `(Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M)`.
The shift `2K + 1` is odd so the bond is antiparallel; same
`(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition. -/
theorem spinHalfDot_mulVec_neelCubicState_x_wrap
    (K L M : ℕ) {j k : ℕ} (hj : j < 2 * L) (hk : k < 2 * M) :
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
        (1 / 4 : ℂ) • neelCubicState (K + 1) L M := by
  rw [neelCubicState_eq_neelStateOf, neelCubicConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one (j + k) with hjk0 | hjk1
    · have h1 : (2 * K + 1 + j + k) % 2 ≠ 0 := by omega
      simp [h1, hjk0]
    · have h1 : (2 * K + 1 + j + k) % 2 = 0 := by omega
      simp [h1, hjk1]

/-- 3D y-axis wrap-around bond `((i, 2L + 1), k) ~ ((i, 0), k)`
on the 3D Néel state over `(Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M)`. -/
theorem spinHalfDot_mulVec_neelCubicState_y_wrap
    (K L M : ℕ) {i k : ℕ} (hi : i < 2 * K) (hk : k < 2 * M) :
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
        (1 / 4 : ℂ) • neelCubicState K (L + 1) M := by
  rw [neelCubicState_eq_neelStateOf, neelCubicConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one (i + k) with hik0 | hik1
    · have h1 : (i + (2 * L + 1) + k) % 2 ≠ 0 := by omega
      simp [h1, hik0]
    · have h1 : (i + (2 * L + 1) + k) % 2 = 0 := by omega
      simp [h1, hik1]

/-- 3D z-axis wrap-around bond `((i, j), 2M + 1) ~ ((i, j), 0)`
on the 3D Néel state over `(Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1))`. -/
theorem spinHalfDot_mulVec_neelCubicState_z_wrap
    (K L M : ℕ) {i j : ℕ} (hi : i < 2 * K) (hj : j < 2 * L) :
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
        (1 / 4 : ℂ) • neelCubicState K L (M + 1) := by
  rw [neelCubicState_eq_neelStateOf, neelCubicConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one (i + j) with hij0 | hij1
    · have h1 : (i + j + (2 * M + 1)) % 2 ≠ 0 := by omega
      simp [h1, hij0]
    · have h1 : (i + j + (2 * M + 1)) % 2 = 0 := by omega
      simp [h1, hij1]

end LatticeSystem.Quantum
