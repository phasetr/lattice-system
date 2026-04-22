/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.InnerProduct

/-!
# Heisenberg energy expectation on the Néel state

Per Tasaki §2.5 (2.5.4) ingredients: the K=1 open-chain
Heisenberg energy expectation `⟨Φ_Néel, H · Φ_Néel⟩ = J/2`.

(Refactor Phase 2 PR 9 — final NeelState extraction series step
2/2, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

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
  change (-(2 * J) : ℂ) *
      (∑ τ : Fin 2 → Fin 2, neelChainState 1 τ *
        (Matrix.mulVec (spinHalfDot (0 : Fin 2) (1 : Fin 2))
          (neelChainState 1)) τ) =
    (J / 2 : ℂ)
  have hzero : (⟨0, by decide⟩ : Fin (2 * 1)) = (0 : Fin 2) := rfl
  have hone : (⟨0 + 1, by decide⟩ : Fin (2 * 1)) = (1 : Fin 2) := rfl
  rw [hzero, hone] at h
  rw [h]
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
