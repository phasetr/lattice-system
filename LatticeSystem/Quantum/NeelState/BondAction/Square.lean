/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition2D

/-!
# 2D Néel checkerboard bond actions (Tasaki §2.5)

Per-bond `Ŝ_x · Ŝ_y` action on the 2D Néel state, both for
nearest-neighbour (horizontal / vertical) bonds and for the
wrap-around bonds on the 2D torus.

(Refactor Phase 2 PR 5 — fifth step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

/-- Tasaki §2.5 eq. (2.5.3) per-bond action for the **horizontal**
nearest-neighbour bond `((i, j), (i+1, j))` of the 2D
checkerboard Néel state. The two endpoints have opposite parities
(`(i + j)` vs `(i + 1 + j)` differ by 1), so the bond is
antiparallel and the action is

  `Ŝ_(i,j) · Ŝ_(i+1,j) · |Φ_Néel⟩
    = (1/2) · |swap_{(i,j),(i+1,j)} Φ_Néel⟩
        - (1/4) · |Φ_Néel⟩`. -/
theorem spinHalfDot_mulVec_neelSquareState_horizontal_adjacent
    (K L : ℕ) {i j : ℕ}
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
        - (1 / 4 : ℂ) • neelSquareState K L := by
  rw [neelSquareState_eq_neelStateOf, neelSquareConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · -- Opposite parities: (i + j) vs (i + 1 + j) differ by 1
    by_cases hp : (i + j) % 2 = 0
    · have hp1 : ((i + 1) + j) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j) % 2 = 0 := by omega
      simp [hp, hp1]

/-- Vertical-bond analogue: `((i, j), (i, j+1))` is also
antiparallel with the same `(1/2) swap - (1/4) Néel` decomposition. -/
theorem spinHalfDot_mulVec_neelSquareState_vertical_adjacent
    (K L : ℕ) {i j : ℕ}
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
              Fin (2 * K) × Fin (2 * L)))
        - (1 / 4 : ℂ) • neelSquareState K L := by
  rw [neelSquareState_eq_neelStateOf, neelSquareConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · by_cases hp : (i + j) % 2 = 0
    · have hp1 : (i + (j + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 2D horizontal wrap-around bond `((2K + 1, j), (0, j))` on the
2D Néel state over `Fin (2 * (K + 1)) × Fin (2 * L)`. Parities of
`2K + 1` and `0` differ (odd vs even), so the bond is antiparallel:

  `Ŝ_(2K+1, j) · Ŝ_(0, j) · |Φ_Néel⟩
    = (1/2) · |swap_{(2K+1,j),(0,j)} Φ_Néel⟩ - (1/4) · |Φ_Néel⟩`.

Together with `_horizontal_adjacent` / `_vertical_adjacent` and
`_vertical_wrap`, covers every bond of the 2D torus Néel state. -/
theorem spinHalfDot_mulVec_neelSquareState_horizontal_wrap
    (K L : ℕ) {j : ℕ} (hj : j < 2 * L) :
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
        - (1 / 4 : ℂ) • neelSquareState (K + 1) L := by
  rw [neelSquareState_eq_neelStateOf, neelSquareConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
    · have h1 : (2 * K + 1 + j) % 2 ≠ 0 := by omega
      simp [h1, hj0]
    · have h4 : (2 * K + 1 + j) % 2 = 0 := by omega
      simp [h4, hj1]

/-- 2D vertical wrap-around bond `((i, 2L + 1), (i, 0))` on the
2D Néel state over `Fin (2 * K) × Fin (2 * (L + 1))`. Same
antiparallel decomposition as the horizontal wrap. -/
theorem spinHalfDot_mulVec_neelSquareState_vertical_wrap
    (K L : ℕ) {i : ℕ} (hi : i < 2 * K) :
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
        - (1 / 4 : ℂ) • neelSquareState K (L + 1) := by
  rw [neelSquareState_eq_neelStateOf, neelSquareConfig_eq_neelConfigOf]
  apply spinHalfDot_mulVec_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one i with hi0 | hi1
    · have h1 : (i + (2 * L + 1)) % 2 ≠ 0 := by omega
      simp [h1, hi0]
    · have h1 : (i + (2 * L + 1)) % 2 = 0 := by omega
      simp [h1, hi1]

end LatticeSystem.Quantum
