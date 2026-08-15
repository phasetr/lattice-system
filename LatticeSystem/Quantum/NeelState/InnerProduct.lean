import LatticeSystem.Quantum.NeelState.InnerProductCore

/-!
# Neel inner-product capstone

Continues InnerProductCore with diagonal SzSz and off-diagonal correlator.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- 1D Néel chain: per-adjacent-bond `Ŝ^(3)_x · Ŝ^(3)_y`
correlation:

  `⟨Φ_Néel, Ŝ^(3)_x · Ŝ^(3)_y · Φ_Néel⟩ = -1/4`

(diagonal `Ŝ^z·Ŝ^z` correlator at antiparallel bond). -/
theorem neelChainState_inner_szsz_adjacent_eq_neg_one_quarter
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((onSite (⟨i, by omega⟩ : Fin (2 * K)) spinHalfOp3 *
              onSite (⟨i + 1, hi⟩ : Fin (2 * K))
                spinHalfOp3).mulVec
            (neelChainState K)) τ = -(1 / 4 : ℂ) := by
  rw [neelChainState_eq_neelStateOf]
  apply inner_neelStateOf_szsz_neelStateOf_antiparallel
  by_cases hp : i % 2 = 0
  · have hp1 : (i + 1) % 2 ≠ 0 := by omega
    simp [hp, hp1]
  · have hp1 : (i + 1) % 2 = 0 := by omega
    simp [hp, hp1]

/-- 1D Néel chain wrap-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation =
`-1/4`. -/
theorem neelChainState_inner_szsz_wrap_eq_neg_one_quarter
    (K : ℕ) :
    ∑ τ : Fin (2 * (K + 1)) → Fin 2,
        neelChainState (K + 1) τ *
          ((onSite (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
                spinHalfOp3 *
              onSite (⟨0, by omega⟩ : Fin (2 * (K + 1)))
                spinHalfOp3).mulVec
            (neelChainState (K + 1))) τ = -(1 / 4 : ℂ) := by
  rw [neelChainState_eq_neelStateOf]
  apply inner_neelStateOf_szsz_neelStateOf_antiparallel
  have h1 : (2 * K + 1) % 2 = 1 := by omega
  simp [h1]

/-- 3D Néel: x adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_szsz_x_adjacent_eq_neg_one_quarter
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
  rw [neelCubicState_eq_neelStateOf]
  apply inner_neelStateOf_szsz_neelStateOf_antiparallel
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
    simp [hp, hp1]
  · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
    simp [hp, hp1]

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


end LatticeSystem.Quantum
