/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition
import LatticeSystem.Quantum.NeelState.Definition2D
import LatticeSystem.Quantum.NeelState.Definition3D
import LatticeSystem.Quantum.NeelState.BondAction.Chain
import LatticeSystem.Quantum.NeelState.BondAction.Square
import LatticeSystem.Quantum.NeelState.BondAction.Cubic
import LatticeSystem.Quantum.NeelState.TimeReversal
import LatticeSystem.Quantum.NeelState.MarshallSign
import LatticeSystem.Quantum.MagnetizationSubspace
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.TimeReversalMulti

/-!
# Néel state on a bipartite even chain (Tasaki §2.5)

Façade module re-exporting the Néel state machinery. Currently
imports the chain `Definition` (Phase 2 PR 1) plus the in-progress
2D / 3D / TimeReversal / MarshallSign / InnerProduct / Energy
sections still residing in this file (Phase 2 follow-up PRs will
extract those into separate files under `NeelState/`).

The chain definitions live in `NeelState/Definition.lean`:
* `neelChainConfig`, `neelChainState`,
* `neelChainConfig_magnetization_zero`,
* `neelChainState_mem_magnetizationSubspace_zero`,
* `heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero`.

(Refactor Phase 2 PR 1, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum


/-! ## Néel state norm² = 1 (orthonormality of the basis vectors) -/

/-- 1D Néel chain state norm² = 1: `∑ τ, |Φ_Néel(τ)|² = 1`. Direct
consequence of `basisVec_inner` (orthonormality of basis vectors)
since `neelChainState K = basisVec (neelChainConfig K)`. -/
theorem neelChainState_norm_squared (K : ℕ) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ * neelChainState K τ = 1 := by
  unfold neelChainState
  rw [basisVec_inner]
  simp

/-- 2D Néel state norm² = 1. -/
theorem neelSquareState_norm_squared (K L : ℕ) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ * neelSquareState K L τ = 1 := by
  unfold neelSquareState
  rw [basisVec_inner]
  simp

/-- 3D cubic Néel state norm² = 1. -/
theorem neelCubicState_norm_squared (K L M : ℕ) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ * neelCubicState K L M τ = 1 := by
  unfold neelCubicState
  rw [basisVec_inner]
  simp

/-! ## Néel-state inner product against the swapped basis vector -/

/-- Orthogonality: the 1D Néel state is orthogonal to the swapped
basis vector at any adjacent (antiparallel) bond. Direct
consequence of `basisVec_inner` + `basisSwap_ne_self`
(swap of antiparallel pair changes the configuration). -/
theorem neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          basisVec (basisSwap (neelChainConfig K)
            (⟨i, by omega⟩ : Fin (2 * K)) ⟨i + 1, hi⟩) τ = 0 := by
  unfold neelChainState
  rw [basisVec_inner]
  rw [if_neg]
  apply basisSwap_ne_self
  · intro h
    have := congrArg Fin.val h
    simp at this
  · unfold neelChainConfig
    by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

/-! ## Per-bond expectation `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = -1/4`

Combining the per-bond action (#23x: `spinHalfDot_mulVec_neelChain
State_adjacent`) with the orthogonality `⟨Φ_Néel, basisVec(swap)⟩
= 0` gives the bond expectation `-1/4` (Tasaki §2.5 (2.5.4)
ingredient). -/

/-- 1D Néel chain: per-adjacent-bond expectation of `Ŝ_x · Ŝ_y`
equals `-1/4`. -/
theorem neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((spinHalfDot
              (⟨i, by omega⟩ : Fin (2 * K))
              (⟨i + 1, hi⟩ : Fin (2 * K))).mulVec
            (neelChainState K)) τ = -(1 / 4 : ℂ) := by
  have h := spinHalfDot_mulVec_neelChainState_adjacent K hi
  simp_rw [h]
  simp_rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [show ∀ τ : Fin (2 * K) → Fin 2,
      neelChainState K τ * ((1 / 2 : ℂ) * basisVec
        (basisSwap (neelChainConfig K)
          (⟨i, by omega⟩ : Fin (2 * K))
          (⟨i + 1, hi⟩ : Fin (2 * K))) τ)
        = (1 / 2 : ℂ) *
          (neelChainState K τ *
            basisVec (basisSwap (neelChainConfig K)
              (⟨i, by omega⟩ : Fin (2 * K))
              (⟨i + 1, hi⟩ : Fin (2 * K))) τ) from fun τ => by ring]
  simp_rw [show ∀ τ : Fin (2 * K) → Fin 2,
      neelChainState K τ * ((1 / 4 : ℂ) * neelChainState K τ)
        = (1 / 4 : ℂ) *
          (neelChainState K τ * neelChainState K τ) from
      fun τ => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero K hi,
    neelChainState_norm_squared]
  ring

/-- 1D Néel chain: per-wrap-bond expectation
`⟨Φ_Néel(K+1), Ŝ_⟨2K+1⟩ · Ŝ_⟨0⟩ · Φ_Néel(K+1)⟩ = -1/4`. -/
theorem neelChainState_inner_spinHalfDot_wrap_eq_neg_one_quarter
    (K : ℕ) :
    ∑ τ : Fin (2 * (K + 1)) → Fin 2,
        neelChainState (K + 1) τ *
          ((spinHalfDot
              (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
              (⟨0, by omega⟩ : Fin (2 * (K + 1)))).mulVec
            (neelChainState (K + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelChainState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · unfold neelChainConfig
    have h1 : (2 * K + 1) % 2 = 1 := by omega
    simp [h1]

/-- 2D Néel: horizontal adjacent bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_horizontal_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((spinHalfDot
              ((⟨i, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L))
              ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L))).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    by_cases hp : (i + j) % 2 = 0
    · have hp1 : ((i + 1) + j) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 2D Néel: vertical adjacent bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_vertical_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((spinHalfDot
              ((⟨i, hi⟩, ⟨j, by omega⟩) :
                Fin (2 * K) × Fin (2 * L))
              ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
                Fin (2 * K) × Fin (2 * L))).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    by_cases hp : (i + j) % 2 = 0
    · have hp1 : (i + (j + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 2D Néel: horizontal wrap bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_horizontal_wrap_eq_neg_one_quarter
    (K L : ℕ) {j : ℕ} (hj : j < 2 * L) :
    ∑ τ : Fin (2 * (K + 1)) × Fin (2 * L) → Fin 2,
        neelSquareState (K + 1) L τ *
          ((spinHalfDot
              ((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L))
              ((⟨0, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L))).mulVec
            (neelSquareState (K + 1) L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
    · have h1 : (2 * K + 1 + j) % 2 ≠ 0 := by omega
      simp [h1, hj0]
    · have h4 : (2 * K + 1 + j) % 2 = 0 := by omega
      simp [h4, hj1]

/-- 2D Néel: vertical wrap bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_vertical_wrap_eq_neg_one_quarter
    (K L : ℕ) {i : ℕ} (hi : i < 2 * K) :
    ∑ τ : Fin (2 * K) × Fin (2 * (L + 1)) → Fin 2,
        neelSquareState K (L + 1) τ *
          ((spinHalfDot
              ((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1)))
              ((⟨i, hi⟩, ⟨0, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1)))).mulVec
            (neelSquareState K (L + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one i with hi0 | hi1
    · have h1 : (i + (2 * L + 1)) % 2 ≠ 0 := by omega
      simp [h1, hi0]
    · have h1 : (i + (2 * L + 1)) % 2 = 0 := by omega
      simp [h1, hi1]

/-- 3D Néel: x-axis adjacent bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_x_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((spinHalfDot
              (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
              (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D Néel: y-axis adjacent bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_y_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
              (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + (j + 1) + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1) + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D Néel: z-axis adjacent bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_z_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) (hk : k + 1 < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + j + (k + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + j + (k + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D Néel: x-axis wrap bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_x_wrap_eq_neg_one_quarter
    (K L M : ℕ) {j k : ℕ}
    (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState (K + 1) L M τ *
          ((spinHalfDot
              (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
              (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState (K + 1) L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (j + k) with hjk0 | hjk1
    · have h1 : (2 * K + 1 + j + k) % 2 ≠ 0 := by omega
      simp [h1, hjk0]
    · have h1 : (2 * K + 1 + j + k) % 2 = 0 := by omega
      simp [h1, hjk1]

/-- 3D Néel: y-axis wrap bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_y_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i k : ℕ}
    (hi : i < 2 * K) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M) → Fin 2,
        neelCubicState K (L + 1) M τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
              (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))).mulVec
            (neelCubicState K (L + 1) M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (i + k) with hik0 | hik1
    · have h1 : (i + (2 * L + 1) + k) % 2 ≠ 0 := by omega
      simp [h1, hik0]
    · have h1 : (i + (2 * L + 1) + k) % 2 = 0 := by omega
      simp [h1, hik1]

/-! ## S^z S^z spin-spin correlation on the Néel state -/

/-- 1D Néel chain: per-adjacent-bond `Ŝ^(3)_x · Ŝ^(3)_y`
correlation:

  `⟨Φ_Néel, Ŝ^(3)_x · Ŝ^(3)_y · Φ_Néel⟩ = -1/4`

(diagonal `Ŝ^z·Ŝ^z` correlator at antiparallel bond). -/
theorem neelChainState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_adjacent_eq_neg_one_quarter
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((onSite (⟨i, by omega⟩ : Fin (2 * K)) spinHalfOp3 *
              onSite (⟨i + 1, hi⟩ : Fin (2 * K))
                spinHalfOp3).mulVec
            (neelChainState K)) τ = -(1 / 4 : ℂ) := by
  unfold neelChainState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelChainConfig spinHalfSign
  by_cases hp : i % 2 = 0
  · have hp1 : (i + 1) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + 1) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 1D Néel chain wrap-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation =
`-1/4`. -/
theorem neelChainState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_wrap_eq_neg_one_quarter
    (K : ℕ) :
    ∑ τ : Fin (2 * (K + 1)) → Fin 2,
        neelChainState (K + 1) τ *
          ((onSite (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
                spinHalfOp3 *
              onSite (⟨0, by omega⟩ : Fin (2 * (K + 1)))
                spinHalfOp3).mulVec
            (neelChainState (K + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelChainState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelChainConfig spinHalfSign
  have h1 : (2 * K + 1) % 2 = 1 := by omega
  simp [h1]; ring

/-- 2D Néel: horizontal adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_horizontal_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((onSite ((⟨i, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3 *
              onSite ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  by_cases hp : (i + j) % 2 = 0
  · have hp1 : ((i + 1) + j) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : ((i + 1) + j) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 2D Néel: vertical adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_vertical_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((onSite ((⟨i, hi⟩, ⟨j, by omega⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3 *
              onSite ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  by_cases hp : (i + j) % 2 = 0
  · have hp1 : (i + (j + 1)) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + (j + 1)) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 2D Néel: horizontal wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_horizontal_wrap_eq_neg_one_quarter
    (K L : ℕ) {j : ℕ} (hj : j < 2 * L) :
    ∑ τ : Fin (2 * (K + 1)) × Fin (2 * L) → Fin 2,
        neelSquareState (K + 1) L τ *
          ((onSite ((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L)) spinHalfOp3 *
              onSite ((⟨0, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L)) spinHalfOp3).mulVec
            (neelSquareState (K + 1) L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
  · have h1 : (2 * K + 1 + j) % 2 ≠ 0 := by omega
    simp [h1, hj0]; ring
  · have h4 : (2 * K + 1 + j) % 2 = 0 := by omega
    simp [h4, hj1]; ring

/-- 2D Néel: vertical wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_vertical_wrap_eq_neg_one_quarter
    (K L : ℕ) {i : ℕ} (hi : i < 2 * K) :
    ∑ τ : Fin (2 * K) × Fin (2 * (L + 1)) → Fin 2,
        neelSquareState K (L + 1) τ *
          ((onSite ((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1))) spinHalfOp3 *
              onSite ((⟨i, hi⟩, ⟨0, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1))) spinHalfOp3).mulVec
            (neelSquareState K (L + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one i with hi0 | hi1
  · have h1 : (i + (2 * L + 1)) % 2 ≠ 0 := by omega
    simp [h1, hi0]; ring
  · have h1 : (i + (2 * L + 1)) % 2 = 0 := by omega
    simp [h1, hi1]; ring

/-- 3D Néel: x adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_x_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((onSite (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 3D Néel: y adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_y_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((onSite (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : (i + (j + 1) + k) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + (j + 1) + k) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 3D Néel: z adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_z_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) (hk : k + 1 < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : (i + j + (k + 1)) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + j + (k + 1)) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 3D Néel: x wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_x_wrap_eq_neg_one_quarter
    (K L M : ℕ) {j k : ℕ}
    (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState (K + 1) L M τ *
          ((onSite (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState (K + 1) L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one (j + k) with hjk0 | hjk1
  · have h1 : (2 * K + 1 + j + k) % 2 ≠ 0 := by omega
    simp [h1, hjk0]; ring
  · have h1 : (2 * K + 1 + j + k) % 2 = 0 := by omega
    simp [h1, hjk1]; ring

/-- 3D Néel: y wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_y_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i k : ℕ}
    (hi : i < 2 * K) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M) → Fin 2,
        neelCubicState K (L + 1) M τ *
          ((onSite (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K (L + 1) M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one (i + k) with hik0 | hik1
  · have h1 : (i + (2 * L + 1) + k) % 2 ≠ 0 := by omega
    simp [h1, hik0]; ring
  · have h1 : (i + (2 * L + 1) + k) % 2 = 0 := by omega
    simp [h1, hik1]; ring

/-- 3D Néel: z wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_z_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)) → Fin 2,
        neelCubicState K L (M + 1) τ *
          ((onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
                spinHalfOp3).mulVec
            (neelCubicState K L (M + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one (i + j) with hij0 | hij1
  · have h1 : (i + j + (2 * M + 1)) % 2 ≠ 0 := by omega
    simp [h1, hij0]; ring
  · have h1 : (i + j + (2 * M + 1)) % 2 = 0 := by omega
    simp [h1, hij1]; ring

/-! ## Off-diagonal correlator (Ŝ^x · Ŝ^x + Ŝ^y · Ŝ^y) on Néel -/

/-- 1D Néel chain: per-adjacent-bond off-diagonal correlator
`(Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y)` vanishes:

  `⟨Φ_Néel, (Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y) · Φ_Néel⟩ = 0`.

Direct from the generic
`inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel`. The
off-diagonal part is entirely supported on swap states. -/
theorem neelChainState_inner_off_diagonal_correlator_adjacent_eq_zero
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((spinHalfDot
              (⟨i, by omega⟩ : Fin (2 * K))
              (⟨i + 1, hi⟩ : Fin (2 * K)) -
              (onSite (⟨i, by omega⟩ : Fin (2 * K))
                  spinHalfOp3 *
                onSite (⟨i + 1, hi⟩ : Fin (2 * K))
                  spinHalfOp3) :
              ManyBodyOp (Fin (2 * K))).mulVec
            (neelChainState K)) τ = 0 := by
  unfold neelChainState
  apply inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · unfold neelChainConfig
    by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

/-! ## Parallel-bond expectation `+1/4` on the Néel chain -/

/-- 1D Néel chain: same-sublattice (parallel) `Ŝ_x · Ŝ_y`
expectation:

  `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = +1/4`

for any pair `x ≠ y` with the same parity (`x.val % 2 = y.val % 2`).
For example, `(0, 2)` (both even, both `↑`) or `(1, 3)` (both
odd, both `↓`). Direct from the generic
`inner_basisVec_spinHalfDot_basisVec_parallel`. -/
theorem neelChainState_inner_spinHalfDot_parallel_eq_one_quarter
    (K : ℕ) {x y : Fin (2 * K)} (hxy : x ≠ y)
    (h_par : x.val % 2 = y.val % 2) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((spinHalfDot x y).mulVec (neelChainState K)) τ =
      (1 / 4 : ℂ) := by
  unfold neelChainState
  apply inner_basisVec_spinHalfDot_basisVec_parallel hxy
  unfold neelChainConfig
  by_cases hp : x.val % 2 = 0
  · have hp1 : y.val % 2 = 0 := h_par ▸ hp
    simp [hp, hp1]
  · have hp1 : y.val % 2 ≠ 0 := h_par ▸ hp
    simp [hp, hp1]

/-! ## Heisenberg energy expectation on the Néel state -/

/-- 1D Néel chain at `K = 1` (2-site open chain): the Heisenberg
energy expectation equals `J/2`:

  `⟨Φ_Néel(K=1), H_open(N=1, J) · Φ_Néel(K=1)⟩ = J/2`.

Combines `openChainHeisenbergHamiltonian_two_site_eq`
(`H = -2J · spinHalfDot 0 1`) with the per-bond expectation
`-1/4` from `neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter`,
giving `-2J · (-1/4) = J/2` (positive for `J > 0`, consistent with
the convention `H = -2J Σ S·S` where `J > 0` is ferromagnetic and
the Néel state is a high-energy variational ansatz). -/
theorem neelChainState_energy_expectation_K1 (J : ℝ) :
    ∑ τ : Fin 2 → Fin 2,
        neelChainState 1 τ *
          ((heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
            (neelChainState 1)) τ = (J / 2 : ℂ) := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  -- ∑ τ, v τ * ((-2J) • (M.mulVec v)) τ = (-2J) · ∑ τ, v τ * (M.mulVec v) τ
  simp_rw [Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ τ : Fin 2 → Fin 2,
      neelChainState 1 τ *
        ((-(2 * J) : ℂ) *
          (Matrix.mulVec (spinHalfDot (0 : Fin 2) 1)
            (neelChainState 1)) τ) =
      (-(2 * J) : ℂ) *
        (neelChainState 1 τ *
          (Matrix.mulVec (spinHalfDot (0 : Fin 2) 1)
            (neelChainState 1)) τ) from
      fun τ => by ring]
  rw [← Finset.mul_sum]
  -- Apply the per-bond expectation = -1/4 (with i = 0)
  have h : ∑ τ : Fin (2 * 1) → Fin 2, neelChainState 1 τ *
      ((spinHalfDot (⟨0, by decide⟩ : Fin (2 * 1))
          (⟨0 + 1, by decide⟩ : Fin (2 * 1))).mulVec
        (neelChainState 1)) τ = -(1 / 4 : ℂ) :=
    neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter 1
      (by decide)
  -- Identify (⟨0, _⟩ : Fin (2 * 1)) with (0 : Fin 2)
  -- Both reduce to the same Fin 2 element
  show (-(2 * J) : ℂ) *
      (∑ τ : Fin 2 → Fin 2, neelChainState 1 τ *
        (Matrix.mulVec (spinHalfDot (0 : Fin 2) (1 : Fin 2))
          (neelChainState 1)) τ) =
    (J / 2 : ℂ)
  have hzero : (⟨0, by decide⟩ : Fin (2 * 1)) = (0 : Fin 2) := rfl
  have hone : (⟨0 + 1, by decide⟩ : Fin (2 * 1)) = (1 : Fin 2) := rfl
  rw [hzero, hone] at h
  rw [h]
  push_cast
  ring

/-- 3D Néel: z-axis wrap bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_z_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)) → Fin 2,
        neelCubicState K L (M + 1) τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))).mulVec
            (neelCubicState K L (M + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (i + j) with hij0 | hij1
    · have h1 : (i + j + (2 * M + 1)) % 2 ≠ 0 := by omega
      simp [h1, hij0]
    · have h1 : (i + j + (2 * M + 1)) % 2 = 0 := by omega
      simp [h1, hij1]

end LatticeSystem.Quantum
