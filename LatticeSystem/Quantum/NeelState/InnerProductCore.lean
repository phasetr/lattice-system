import LatticeSystem.Quantum.NeelState.Definition
import LatticeSystem.Quantum.NeelState.Definition2D
import LatticeSystem.Quantum.NeelState.Definition3D
import LatticeSystem.Quantum.NeelState.BondAction.Chain
import LatticeSystem.Quantum.NeelState.BondAction.Square
import LatticeSystem.Quantum.NeelState.BondAction.Cubic

/-!
# Inner-product family on the Néel state (Tasaki §2.5 (2.5.4))

Norm² = 1 and the per-bond `Ŝ_x · Ŝ_y` expectation `-1/4`, both
derived from `basisVec_inner` orthonormality (through the Néel
state's orthogonality to the swapped basis vector) + the per-bond
actions.

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

end LatticeSystem.Quantum
