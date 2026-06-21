import LatticeSystem.Quantum.NeelState.Definition
import LatticeSystem.Quantum.NeelState.Definition2D
import LatticeSystem.Quantum.NeelState.Definition3D
import LatticeSystem.Quantum.NeelState.BondAction.Chain
import LatticeSystem.Quantum.NeelState.BondAction.Square
import LatticeSystem.Quantum.NeelState.BondAction.Cubic

/-!
# Inner-product family on the Néel state (Tasaki §2.5 (2.5.4))

Norm² = 1, per-bond `Ŝ_x · Ŝ_y` expectation `-1/4`, per-bond
`Ŝ^(3)_x · Ŝ^(3)_y` correlation `-1/4`, off-diagonal correlator
vanishing, and parallel-bond `+1/4`. All derived from
`basisVec_inner` orthonormality + the per-bond actions.

(Refactor Phase 2 PR 9 — final NeelState extraction series step
1/2, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

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
  rw [neelChainState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

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
  rw [neelChainState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · have h1 : (2 * K + 1) % 2 = 1 := by omega
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
  rw [neelSquareState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · by_cases hp : (i + j) % 2 = 0
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
  rw [neelSquareState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · by_cases hp : (i + j) % 2 = 0
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
  rw [neelSquareState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
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
  rw [neelSquareState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · rcases Nat.mod_two_eq_zero_or_one i with hi0 | hi1
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
  rw [neelCubicState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
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
  rw [neelCubicState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
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
  rw [neelCubicState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · by_cases hp : (i + j + k) % 2 = 0
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
  rw [neelCubicState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
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
  rw [neelCubicState_eq_neelStateOf]
  apply inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel
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

/-! ## S^z S^z spin-spin correlation on the Néel state -/


end LatticeSystem.Quantum
