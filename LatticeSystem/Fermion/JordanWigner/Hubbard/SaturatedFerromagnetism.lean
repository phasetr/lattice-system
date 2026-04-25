/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState

/-!
# Hubbard saturated ferromagnetism: Definition 11.1 (Tasaki §11.1.1)

This file defines the total-spin Casimir `(Ŝ_tot)²`, the predicate for saturated
ferromagnetism (Definition 11.1), and proves basic structural results for the all-up
state that underlie Proposition 11.2.

| Lean name | Statement |
|---|---|
| `fermionTotalSpinSquared` | Casimir `(Ŝ_tot)² = Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z + 1)` |
| `fermionTotalUpNumber_mulVec_allUpState` | `N_↑ · \|↑…↑⟩ = (N+1) • \|↑…↑⟩` |
| `fermionTotalDownNumber_mulVec_allUpState` | `N_↓ · \|↑…↑⟩ = 0` |
| `fermionTotalSpinZ_mulVec_allUpState` | `Ŝ^z_tot · \|↑…↑⟩ = ((N+1)/2) • \|↑…↑⟩` |
| `fermionTotalSpinPlus_mulVec_allUpState` | `Ŝ⁺_tot · \|↑…↑⟩ = 0` |
| `fermionTotalSpinSquared_mulVec_allUpState` | `(Ŝ_tot)² · \|↑…↑⟩ = S_max(S_max+1) • \|↑…↑⟩` |
| `fermionTotalSpinSquared_commute_hubbardHamiltonian` | `[(Ŝ_tot)², H] = 0` |
| `isSaturatedFerromagnet` | Definition 11.1: every ground state has `(Ŝ_tot)² = S_max(S_max+1)` |

Reference: H. Tasaki, §11.1.1, pp. 372–374.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Total-spin Casimir -/

/-- The total-spin Casimir `(Ŝ_tot)² = Ŝ⁻_tot Ŝ⁺_tot + Ŝ^z_tot(Ŝ^z_tot + 1)`.

From `[Ŝ⁺, Ŝ⁻] = 2Ŝ_z` one derives `Ŝ² = Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z + 1)`, which
gives `Ŝ²|S, M⟩ = S(S+1)|S, M⟩` for the highest-weight state with `Ŝ⁺|S,S⟩ = 0`.

Reference: Tasaki §11.1.1, p. 372. -/
noncomputable def fermionTotalSpinSquared (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionTotalSpinMinus N * fermionTotalSpinPlus N +
    fermionTotalSpinZ N * (fermionTotalSpinZ N + 1)

/-! ## Total number actions on the all-up state -/

/-- `N_↑ = Σ_i n_{i,↑}` counts all `N+1` up-spin electrons:
`N_↑ · |↑…↑⟩ = (N+1 : ℂ) • |↑…↑⟩`. -/
theorem fermionTotalUpNumber_mulVec_allUpState (N : ℕ) :
    (fermionTotalUpNumber N).mulVec (hubbardAllUpState N) =
      ((N + 1 : ℕ) : ℂ) • hubbardAllUpState N := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  simp only [fermionUpNumber_mulVec_allUpState]
  rw [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]

/-- `N_↓ = Σ_i n_{i,↓}` annihilates the all-up state:
`N_↓ · |↑…↑⟩ = 0`. -/
theorem fermionTotalDownNumber_mulVec_allUpState (N : ℕ) :
    (fermionTotalDownNumber N).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  exact fermionDownNumber_mulVec_allUpState N i

/-! ## Spin component actions on the all-up state -/

/-- `Ŝ^z_tot = (1/2)(N_↑ − N_↓)` has eigenvalue `(N+1)/2` on the all-up state.

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinZ_mulVec_allUpState (N : ℕ) :
    (fermionTotalSpinZ N).mulVec (hubbardAllUpState N) =
      (((N + 1 : ℕ) : ℂ) / 2) • hubbardAllUpState N := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    fermionTotalUpNumber_mulVec_allUpState, fermionTotalDownNumber_mulVec_allUpState,
    sub_zero, smul_smul,
    show (1 / 2 : ℂ) * ((N + 1 : ℕ) : ℂ) = (((N + 1 : ℕ) : ℂ) / 2) from by push_cast; ring]

/-- `Ŝ⁺_tot = Σ_i c†_{i,↑} c_{i,↓}` annihilates the all-up state:
`Ŝ⁺_tot · |↑…↑⟩ = 0` (highest-weight state: no down electrons to raise).

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinPlus_mulVec_allUpState (N : ℕ) :
    (fermionTotalSpinPlus N).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionTotalSpinPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Matrix.mulVec_mulVec,
    fermionDownAnnihilation_mulVec_allUpState, Matrix.mulVec_zero]

/-! ## Casimir eigenvalue on the all-up state -/

set_option maxHeartbeats 400000 in
-- The repeated Ŝ_z mulVec rewrites over the Casimir expansion exceed the default limit.
/-- `(Ŝ_tot)²` acts on the all-up state with eigenvalue `S_max(S_max+1)` where
`S_max = (N+1)/2`: `(Ŝ_tot)² · |↑…↑⟩ = ((N+1)/2 · ((N+1)/2 + 1)) • |↑…↑⟩`.

Uses `Ŝ⁺|allUp⟩ = 0` and `Ŝ_z|allUp⟩ = ((N+1)/2)|allUp⟩`.

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinSquared_mulVec_allUpState (N : ℕ) :
    (fermionTotalSpinSquared N).mulVec (hubbardAllUpState N) =
      (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) •
        hubbardAllUpState N := by
  unfold fermionTotalSpinSquared
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalSpinPlus_mulVec_allUpState, Matrix.mulVec_zero, zero_add]
  -- goal: (Ŝ_z * (Ŝ_z + 1)) *ᵥ allUp = S_max(S_max+1) • allUp
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    fermionTotalSpinZ_mulVec_allUpState]
  -- goal: Ŝ_z *ᵥ (S_max • allUp + allUp) = S_max(S_max+1) • allUp
  rw [Matrix.mulVec_add, Matrix.mulVec_smul,
    fermionTotalSpinZ_mulVec_allUpState,
    smul_smul, ← add_smul]
  congr 1
  ring

/-! ## Casimir commutes with the Hamiltonian -/

/-- `(Ŝ_tot)²` commutes with the Hubbard Hamiltonian:
`[(Ŝ_tot)², H] = 0`.

Follows from `[Ŝ⁺, H] = [Ŝ⁻, H] = [Ŝ_z, H] = 0` (SU(2) invariance, proved in
SpinSymmetry.lean). The Hermiticity conditions `hJ`, `hU` are needed for
the `Ŝ⁻` commutator.

Reference: Tasaki §9.3.3, p. 333; §11.1.1, p. 372. -/
theorem fermionTotalSpinSquared_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    Commute (fermionTotalSpinSquared N) (hubbardHamiltonian N t U) := by
  unfold fermionTotalSpinSquared
  apply Commute.add_left
  · -- [Ŝ⁻Ŝ⁺, H] = 0
    exact (fermionTotalSpinMinus_commute_hubbardHamiltonian N t U
        (hJ := hJ) (hU := hU)).mul_left
      (fermionTotalSpinPlus_commute_hubbardHamiltonian N t U)
  · -- [Ŝ_z(Ŝ_z + 1), H] = 0
    have h_z := fermionTotalSpinZ_commute_hubbardHamiltonian N t U
    exact h_z.mul_left (h_z.add_left (Commute.one_left _))

/-! ## Definition 11.1: saturated ferromagnetism -/

/-- **Definition 11.1** (Tasaki §11.1.1, p. 372): the Hubbard model exhibits
*saturated ferromagnetism* if there exists a ground-state energy `E₀` such that
every `H`-eigenvector with eigenvalue `E₀` is also a `(Ŝ_tot)²`-eigenvector
with eigenvalue `S_max(S_max + 1) = (N+1)/2 · ((N+1)/2 + 1)`.

The "minimum eigenvalue" condition is implicit in `E₀` being the true ground-state
energy; a separate predicate can impose `E₀ = min_spec (hubbardHamiltonian N t U)`. -/
def isSaturatedFerromagnet
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) : Prop :=
  ∃ E₀ : ℂ,
    ∀ v : (Fin (2 * N + 2) → Fin 2) → ℂ,
      v ≠ 0 →
      (hubbardHamiltonian N t U).mulVec v = E₀ • v →
        (fermionTotalSpinSquared N).mulVec v =
          (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v

end LatticeSystem.Fermion
