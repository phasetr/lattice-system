import LatticeSystem.Fermion.JordanWigner.Hubbard.AllDownState
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Hubbard total-number / spin operators on the all-down state

Mirror of `SaturatedFerromagnetism.lean`'s
`fermionTotalUpNumber_mulVec_allUpState` and friends, for the
spin-down sector defined in `AllDownState.lean`.

| Lean name | Statement |
|---|---|
| `fermionTotalDownNumber_mulVec_allDownState` | `N_↓ · |↓..⟩ = (N+1) • |↓..⟩` |
| `fermionTotalUpNumber_mulVec_allDownState` | `N_↑ · |↓..⟩ = 0` |
| `fermionTotalSpinZ_mulVec_allDownState` | `Ŝ^z_tot · |↓..⟩ = -(N+1)/2 • |↓..⟩` (lowest weight) |
| `fermionTotalSpinMinus_mulVec_allDownState` | `Ŝ^-_tot · |↓..⟩ = 0` (lowest-weight state) |

The all-down state is the lowest-weight state of the global SU(2)
spin algebra: `Ŝ^z_tot` eigenvalue `-(N+1)/2` (most negative)
and `Ŝ^-_tot` annihilates it.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Total number actions on the all-down state -/

/-- `N_↓ = Σ_i n_{i,↓}` counts all `N+1` down-spin electrons:
`N_↓ · |↓..⟩ = (N+1 : ℂ) • |↓..⟩`. -/
theorem fermionTotalDownNumber_mulVec_allDownState (N : ℕ) :
    (fermionTotalDownNumber N).mulVec (hubbardAllDownState N) =
      ((N + 1 : ℕ) : ℂ) • hubbardAllDownState N := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  simp only [fermionDownNumber_mulVec_allDownState]
  rw [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]

/-- `N_↑ = Σ_i n_{i,↑}` annihilates the all-down state:
`N_↑ · |↓..⟩ = 0`. -/
theorem fermionTotalUpNumber_mulVec_allDownState (N : ℕ) :
    (fermionTotalUpNumber N).mulVec (hubbardAllDownState N) = 0 := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  exact fermionUpNumber_mulVec_allDownState N i

/-! ## Spin component actions on the all-down state -/

/-- `Ŝ^z_tot = (1/2)(N_↑ − N_↓)` has eigenvalue `-(N+1)/2` on the
all-down state (lowest-weight state of global SU(2)). -/
theorem fermionTotalSpinZ_mulVec_allDownState (N : ℕ) :
    (fermionTotalSpinZ N).mulVec (hubbardAllDownState N) =
      (-((N + 1 : ℕ) : ℂ) / 2) • hubbardAllDownState N := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    fermionTotalUpNumber_mulVec_allDownState,
    fermionTotalDownNumber_mulVec_allDownState,
    zero_sub, smul_neg, smul_smul,
    show (1 / 2 : ℂ) * ((N + 1 : ℕ) : ℂ) =
      ((N + 1 : ℕ) : ℂ) / 2 from by ring,
    show -((((N + 1 : ℕ) : ℂ) / 2) • hubbardAllDownState N) =
      (-((N + 1 : ℕ) : ℂ) / 2) • hubbardAllDownState N from by
      rw [← neg_smul, neg_div]]

/-- `Ŝ^-_tot = Σ_i c†_{i,↓} c_{i,↑}` annihilates the all-down state:
`Ŝ^-_tot · |↓..⟩ = 0` (lowest-weight: no up electrons to lower).
-/
theorem fermionTotalSpinMinus_mulVec_allDownState (N : ℕ) :
    (fermionTotalSpinMinus N).mulVec (hubbardAllDownState N) = 0 := by
  unfold fermionTotalSpinMinus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Matrix.mulVec_mulVec,
    fermionUpAnnihilation_mulVec_allDownState, Matrix.mulVec_zero]

end LatticeSystem.Fermion
