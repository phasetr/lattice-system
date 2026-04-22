/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition

/-!
# Néel chain bond actions (Tasaki §2.5)

Per-bond `Ŝ_x · Ŝ_y` action on the chain Néel state, both for
adjacent bonds and the wrap-around bond on the periodic chain.
Plus the `K = 1` open-chain Heisenberg Hamiltonian on the Néel
state.

(Refactor Phase 2 PR 2 — second step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

/-- Tasaki §2.5 eq. (2.5.3), p. 37 (concrete chain instance):
on every adjacent bond `(i, i+1)` of the chain `Fin (2 * K)`, the
two-site spin inner product `Ŝ_x · Ŝ_y` acts on the Néel state by

  `Ŝ_x · Ŝ_y · |Φ_Néel⟩
    = (1/2) |swap_{x, y} Φ_Néel⟩ - (1/4) |Φ_Néel⟩`,

since adjacent indices have opposite parities and hence opposite
Néel spins (antiparallel case). One-line corollary of the generic
`spinHalfDot_mulVec_basisVec_antiparallel` (Tasaki §2.2 (2.2.19),
antiparallel) instantiated at `σ = neelChainConfig K` and the
parity-derived `σ x ≠ σ y` certificate. -/
theorem spinHalfDot_mulVec_neelChainState_adjacent
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    (spinHalfDot
        (⟨i, by omega⟩ : Fin (2 * K))
        (⟨i + 1, hi⟩ : Fin (2 * K))).mulVec (neelChainState K) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig K)
            (⟨i, by omega⟩ : Fin (2 * K))
            (⟨i + 1, hi⟩ : Fin (2 * K)))
        - (1 / 4 : ℂ) • neelChainState K := by
  unfold neelChainState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · -- σ_Néel ⟨i⟩ ≠ σ_Néel ⟨i + 1⟩: opposite parities
    unfold neelChainConfig
    simp only
    by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

/-- Two-site Néel computation (`K = 1`): the open-chain
Heisenberg Hamiltonian `H_open(N=1, J)` acts on the Néel state
`|Φ_Néel⟩ = |↑↓⟩` by

  `H · |Φ_Néel⟩ = -J · |↓↑⟩ + (J/2) · |Φ_Néel⟩`,

which decomposes the bond `(0, 1)` action via the antiparallel
formula. This is the explicit `K = 1` instance of the bond-by-bond
calculation `spinHalfDot_mulVec_neelChainState_adjacent` lifted
through `H_open(N=1, J) = -2J · spinHalfDot 0 1`. The
non-eigenstate character of the Néel state is plain: the
right-hand side has two distinct basis components. -/
theorem heisenbergHamiltonian_openChainCoupling_one_mulVec_neelChainState_one
    (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (neelChainState 1) =
      (-(J : ℂ)) • basisVec
          (basisSwap (neelChainConfig 1)
            (⟨0, by decide⟩ : Fin (2 * 1))
            (⟨1, by decide⟩ : Fin (2 * 1))) +
        ((J : ℂ) / 2) • neelChainState 1 := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  have h := spinHalfDot_mulVec_neelChainState_adjacent 1 (i := 0)
    (by decide)
  -- Replace (0 : Fin 2) by ⟨0, _⟩ and (1 : Fin 2) by ⟨1, _⟩ in the goal.
  show (-(2 * (J : ℂ))) •
      (spinHalfDot (⟨0, by decide⟩ : Fin (2 * 1))
        (⟨1, by decide⟩ : Fin (2 * 1))).mulVec (neelChainState 1) =
    (-(J : ℂ)) • basisVec
        (basisSwap (neelChainConfig 1)
          (⟨0, by decide⟩ : Fin (2 * 1))
          (⟨1, by decide⟩ : Fin (2 * 1))) +
      ((J : ℂ) / 2) • neelChainState 1
  rw [h]
  module

/-- Companion of `spinHalfDot_mulVec_neelChainState_adjacent` for
the **wrap-around** bond `(2K - 1, 0)` of the periodic chain
`cycleGraph (2 * (K + 1))`. For `K ≥ 0` (so chain length
`2 * (K + 1) ≥ 2`), the indices `2*K + 1` and `0` carry opposite
parities, so the bond is again antiparallel:

  `Ŝ_⟨2K+1⟩ · Ŝ_⟨0⟩ · |Φ_Néel⟩
    = (1/2) · |swap_{2K+1, 0} Φ_Néel⟩ - (1/4) · |Φ_Néel⟩`.

Together with `spinHalfDot_mulVec_neelChainState_adjacent` this
covers every bond of the periodic chain `cycleGraph (2*(K+1))`. -/
theorem spinHalfDot_mulVec_neelChainState_wrap (K : ℕ) :
    (spinHalfDot
        (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
        (⟨0, by omega⟩ : Fin (2 * (K + 1)))).mulVec
        (neelChainState (K + 1)) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig (K + 1))
            (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
            (⟨0, by omega⟩ : Fin (2 * (K + 1))))
        - (1 / 4 : ℂ) • neelChainState (K + 1) := by
  unfold neelChainState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · -- σ_Néel ⟨2K+1⟩ = 1, σ_Néel ⟨0⟩ = 0 (opposite parities)
    unfold neelChainConfig
    simp only
    have h1 : (2 * K + 1) % 2 = 1 := by omega
    simp [h1]

end LatticeSystem.Quantum
