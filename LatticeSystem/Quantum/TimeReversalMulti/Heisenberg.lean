/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TimeReversalMulti
import LatticeSystem.Quantum.TimeReversalMulti.SpinOpEquivariance
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.HeisenbergLattice

/-!
# Time-reversal invariance of bilinear `Ŝ_x · Ŝ_y` and chain
Heisenberg Hamiltonians (Tasaki §2.3)

Builds the time-reversal invariance of the Heisenberg model on
top of the per-axis spin-operator equivariance lemmas.

(Refactor Phase 2 PR 20 — first TimeReversalMulti extraction,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Time-reversal invariance of bilinear `Ŝ_x · Ŝ_y` (Tasaki §2.3)

Composing the per-α Ŝ^(α) equivariance for both `x` and `y`
yields *invariance* (not anti-invariance) of the bilinear
`Ŝ_x · Ŝ_y` under multi-spin time reversal: two `-1` factors
cancel.

This is the operator-level analogue of Tasaki's observation that
the Heisenberg Hamiltonian is time-reversal invariant. -/

/-- Per-axis composition: applying `Θ̂_tot` to the bilinear
`(onSite x Ŝ^(1)) · (onSite y Ŝ^(1))` acting on `v` is the same as
applying the bilinear product to `Θ̂_tot v` directly — the two
equivariance `-1` factors cancel. -/
private theorem timeReversalSpinHalfMulti_onSite_spinHalfOp1_mul_onSite_mulVec
    (x y : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((onSite x spinHalfOp1 * onSite y spinHalfOp1).mulVec v) =
      (onSite x spinHalfOp1 * onSite y spinHalfOp1).mulVec
        (timeReversalSpinHalfMulti v) := by
  rw [show (onSite x spinHalfOp1 * onSite y spinHalfOp1).mulVec v =
        (onSite x spinHalfOp1).mulVec
          ((onSite y spinHalfOp1).mulVec v) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [show (onSite x spinHalfOp1 * onSite y spinHalfOp1).mulVec
          (timeReversalSpinHalfMulti v) =
        (onSite x spinHalfOp1).mulVec
          ((onSite y spinHalfOp1).mulVec
            (timeReversalSpinHalfMulti v)) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [timeReversalSpinHalfMulti_onSite_spinHalfOp1_mulVec,
    timeReversalSpinHalfMulti_onSite_spinHalfOp1_mulVec,
    Matrix.neg_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_neg, neg_neg]

/-- Per-axis composition for `Ŝ^(2)`. -/
private theorem timeReversalSpinHalfMulti_onSite_spinHalfOp2_mul_onSite_mulVec
    (x y : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((onSite x spinHalfOp2 * onSite y spinHalfOp2).mulVec v) =
      (onSite x spinHalfOp2 * onSite y spinHalfOp2).mulVec
        (timeReversalSpinHalfMulti v) := by
  rw [show (onSite x spinHalfOp2 * onSite y spinHalfOp2).mulVec v =
        (onSite x spinHalfOp2).mulVec
          ((onSite y spinHalfOp2).mulVec v) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [show (onSite x spinHalfOp2 * onSite y spinHalfOp2).mulVec
          (timeReversalSpinHalfMulti v) =
        (onSite x spinHalfOp2).mulVec
          ((onSite y spinHalfOp2).mulVec
            (timeReversalSpinHalfMulti v)) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [timeReversalSpinHalfMulti_onSite_spinHalfOp2_mulVec,
    timeReversalSpinHalfMulti_onSite_spinHalfOp2_mulVec,
    Matrix.neg_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_neg, neg_neg]

/-- Per-axis composition for `Ŝ^(3)`. -/
private theorem timeReversalSpinHalfMulti_onSite_spinHalfOp3_mul_onSite_mulVec
    (x y : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((onSite x spinHalfOp3 * onSite y spinHalfOp3).mulVec v) =
      (onSite x spinHalfOp3 * onSite y spinHalfOp3).mulVec
        (timeReversalSpinHalfMulti v) := by
  rw [show (onSite x spinHalfOp3 * onSite y spinHalfOp3).mulVec v =
        (onSite x spinHalfOp3).mulVec
          ((onSite y spinHalfOp3).mulVec v) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [show (onSite x spinHalfOp3 * onSite y spinHalfOp3).mulVec
          (timeReversalSpinHalfMulti v) =
        (onSite x spinHalfOp3).mulVec
          ((onSite y spinHalfOp3).mulVec
            (timeReversalSpinHalfMulti v)) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [timeReversalSpinHalfMulti_onSite_spinHalfOp3_mulVec,
    timeReversalSpinHalfMulti_onSite_spinHalfOp3_mulVec,
    Matrix.neg_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_neg, neg_neg]

/-- `Θ̂_tot` distributes over a finite sum of states. -/
private theorem timeReversalSpinHalfMulti_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (∑ i ∈ s, f i) =
      ∑ i ∈ s, timeReversalSpinHalfMulti (f i) := by
  induction s using Finset.induction with
  | empty =>
    funext τ
    simp [timeReversalSpinHalfMulti_apply]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, timeReversalSpinHalfMulti_add, ih,
      Finset.sum_insert ha]

/-- **Time-reversal invariance of `Ŝ_x · Ŝ_y`** (Tasaki §2.3):
the bilinear two-site spin inner product is invariant under
`Θ̂_tot`,

  `Θ̂_tot ((Ŝ_x · Ŝ_y) v) = (Ŝ_x · Ŝ_y) (Θ̂_tot v)`.

Sums the per-axis bilinear invariances over `α = 1, 2, 3`. -/
theorem timeReversalSpinHalfMulti_spinHalfDot_mulVec
    (x y : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((spinHalfDot x y).mulVec v) =
      (spinHalfDot x y).mulVec (timeReversalSpinHalfMulti v) := by
  unfold spinHalfDot
  rw [Matrix.add_mulVec, Matrix.add_mulVec,
    timeReversalSpinHalfMulti_add, timeReversalSpinHalfMulti_add,
    timeReversalSpinHalfMulti_onSite_spinHalfOp1_mul_onSite_mulVec,
    timeReversalSpinHalfMulti_onSite_spinHalfOp2_mul_onSite_mulVec,
    timeReversalSpinHalfMulti_onSite_spinHalfOp3_mul_onSite_mulVec,
    ← Matrix.add_mulVec, ← Matrix.add_mulVec]

/-- Helper: `(heisenbergHamiltonian J).mulVec v` expands as a
double sum of `J(x,y) • (spinHalfDot x y).mulVec v` terms. -/
private theorem heisenbergHamiltonian_mulVec_expand
    (J : Λ → Λ → ℂ) (v : (Λ → Fin 2) → ℂ) :
    (heisenbergHamiltonian J).mulVec v =
      ∑ x : Λ, ∑ y : Λ, J x y • (spinHalfDot x y).mulVec v := by
  unfold heisenbergHamiltonian
  rw [Matrix.sum_mulVec]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.sum_mulVec]
  apply Finset.sum_congr rfl
  intro y _
  rw [Matrix.smul_mulVec]

/-- **Time-reversal invariance of the Heisenberg Hamiltonian**
(Tasaki §2.3): if every coupling entry `J(x, y)` is real
(`conj (J x y) = J x y`), then `Θ̂_tot` commutes with `H`.

Combines: `Ŝ_x · Ŝ_y` invariance under `Θ̂_tot` (per-bond),
antilinearity of `Θ̂_tot` (each scalar `J(x,y)` survives because
`conj(J(x,y)) = J(x,y)` for real `J`), and additivity of
`Θ̂_tot` (distribute over the double sum). -/
theorem timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec
    (J : Λ → Λ → ℂ) (hJ : ∀ x y, starRingEnd ℂ (J x y) = J x y)
    (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian J).mulVec v) =
      (heisenbergHamiltonian J).mulVec
        (timeReversalSpinHalfMulti v) := by
  rw [heisenbergHamiltonian_mulVec_expand,
    heisenbergHamiltonian_mulVec_expand,
    timeReversalSpinHalfMulti_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [timeReversalSpinHalfMulti_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [timeReversalSpinHalfMulti_smul, hJ x y,
    timeReversalSpinHalfMulti_spinHalfDot_mulVec]

/-! ## Concrete time-reversal invariance: chain Heisenberg

Specialisations of the Hamiltonian-level invariance to the
concrete chain Hamiltonians used throughout the library. -/

/-- Time-reversal invariance of the open-chain Heisenberg
Hamiltonian (real coupling `J : ℝ`). -/
theorem timeReversalSpinHalfMulti_openChainHeisenberg_mulVec
    (N : ℕ) (J : ℝ) (v : (Fin (N + 1) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (openChainCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (openChainCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec
    (openChainCoupling N J) (openChainCoupling_conj N J) v

/-- Time-reversal invariance of the periodic-chain Heisenberg
Hamiltonian (real coupling `J : ℝ`). -/
theorem timeReversalSpinHalfMulti_periodicChainHeisenberg_mulVec
    (N : ℕ) (J : ℝ) (v : (Fin (N + 2) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (periodicChainCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (periodicChainCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec
    (periodicChainCoupling N J) (periodicChainCoupling_conj N J) v

/-- Time-reversal invariance of the 2D open-boundary square-lattice
Heisenberg Hamiltonian (real coupling `J : ℝ`). -/
theorem timeReversalSpinHalfMulti_squareLatticeHeisenberg_mulVec
    (N : ℕ) (J : ℝ)
    (v : (Fin (N + 1) × Fin (N + 1) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (squareLatticeCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (squareLatticeCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec
    (squareLatticeCoupling N J) (squareLatticeCoupling_conj N J) v

/-- Time-reversal invariance of the 2D torus Heisenberg Hamiltonian. -/
theorem timeReversalSpinHalfMulti_squareTorusHeisenberg_mulVec
    (N : ℕ) (J : ℝ)
    (v : (Fin (N + 2) × Fin (N + 2) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (squareTorusCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (squareTorusCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec
    (squareTorusCoupling N J) (squareTorusCoupling_conj N J) v

/-- Time-reversal invariance of the 3D cubic-lattice Heisenberg
Hamiltonian. -/
theorem timeReversalSpinHalfMulti_cubicLatticeHeisenberg_mulVec
    (N : ℕ) (J : ℝ)
    (v : ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (cubicLatticeCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (cubicLatticeCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec
    (cubicLatticeCoupling N J) (cubicLatticeCoupling_conj N J) v

/-! ## Time-reversal action on two-site Néel / singlet states

The two-site basis state `|↑↓⟩` flips to `-|↓↑⟩` under `Θ̂_tot`
(one of the two sites contributes a `-1` from `pauliY_sign`).
The spin-singlet `|↑↓⟩ - |↓↑⟩`, being SU(2)-invariant in the
`S = 0` representation, is **time-reversal invariant**. -/

/-- `Θ̂_tot |↑↓⟩ = -|↓↑⟩` on `Fin 2`. -/
theorem timeReversalSpinHalfMulti_basisVec_upDown :
    timeReversalSpinHalfMulti (basisVec upDown : (Fin 2 → Fin 2) → ℂ) =
      -basisVec (basisSwap upDown 0 1) := by
  rw [timeReversalSpinHalfMulti_basisVec]
  -- ∏_{x : Fin 2} ε(flip upDown x) = ε(1) * ε(0) = -1 * 1 = -1
  -- flipConfig upDown = basisSwap upDown 0 1 (both swap the two sites)
  have hprod : (∏ x : Fin 2, timeReversalSign (flipConfig upDown x))
      = (-1 : ℂ) := by
    rw [Fin.prod_univ_two]
    simp [flipConfig, upDown]
  have hflip : flipConfig (upDown : Fin 2 → Fin 2) = basisSwap upDown 0 1 := by
    funext i
    fin_cases i <;> simp [flipConfig, upDown, basisSwap]
  rw [hprod, hflip]
  simp [neg_one_smul]

/-- `Θ̂_tot |↓↑⟩ = -|↑↓⟩` on `Fin 2`. -/
theorem timeReversalSpinHalfMulti_basisVec_basisSwap_upDown :
    timeReversalSpinHalfMulti
        (basisVec (basisSwap upDown 0 1) : (Fin 2 → Fin 2) → ℂ) =
      -basisVec upDown := by
  rw [timeReversalSpinHalfMulti_basisVec]
  have hprod : (∏ x : Fin 2,
        timeReversalSign (flipConfig (basisSwap upDown 0 1) x))
      = (-1 : ℂ) := by
    rw [Fin.prod_univ_two]
    simp [flipConfig, basisSwap_upDown]
  have hflip : flipConfig (basisSwap upDown 0 1 : Fin 2 → Fin 2) = upDown := by
    funext i
    fin_cases i <;> simp [flipConfig, basisSwap_upDown, upDown]
  rw [hprod, hflip]
  simp [neg_one_smul]

/-- **The two-site spin singlet `|↑↓⟩ - |↓↑⟩` is time-reversal
invariant** (Tasaki §2.3 corollary): being the SU(2)-invariant
`S = 0` representation, it survives `Θ̂_tot` unchanged.

Proof: `Θ̂_tot` is antilinear, so for the difference of two
basis vectors `Θ̂_tot(v - w) = conj(1) Θ̂_tot v - conj(1) Θ̂_tot w`.
The previous two lemmas give `Θ̂_tot |↑↓⟩ = -|↓↑⟩` and
`Θ̂_tot |↓↑⟩ = -|↑↓⟩`, so the difference becomes
`-|↓↑⟩ - (-|↑↓⟩) = |↑↓⟩ - |↓↑⟩`. -/
theorem timeReversalSpinHalfMulti_singlet :
    timeReversalSpinHalfMulti
        ((basisVec upDown - basisVec (basisSwap upDown 0 1)) :
          (Fin 2 → Fin 2) → ℂ) =
      basisVec upDown - basisVec (basisSwap upDown 0 1) := by
  rw [show ((basisVec upDown - basisVec (basisSwap upDown 0 1)) :
          (Fin 2 → Fin 2) → ℂ)
        = basisVec upDown +
          ((-1 : ℂ) • basisVec (basisSwap upDown 0 1)) from by
      rw [neg_one_smul, sub_eq_add_neg]]
  rw [timeReversalSpinHalfMulti_add,
    timeReversalSpinHalfMulti_basisVec_upDown,
    timeReversalSpinHalfMulti_smul,
    timeReversalSpinHalfMulti_basisVec_basisSwap_upDown]
  simp [neg_one_smul, sub_eq_add_neg]
  ring_nf

/-- The triplet `m = 0` state `|↑↓⟩ + |↓↑⟩` flips sign under
`Θ̂_tot`:

  `Θ̂_tot (|↑↓⟩ + |↓↑⟩) = -(|↑↓⟩ + |↓↑⟩)`.

This is consistent with the singlet (S = 0) being even under
`Θ̂_tot` and the m=0 component of the triplet (S = 1) being odd
— the two basis vectors `|↑↓⟩, |↓↑⟩` each map to `-` of the
other, and the symmetric combination picks up the resulting `-1`
sign. -/
theorem timeReversalSpinHalfMulti_triplet_zero :
    timeReversalSpinHalfMulti
        ((basisVec upDown + basisVec (basisSwap upDown 0 1)) :
          (Fin 2 → Fin 2) → ℂ) =
      -(basisVec upDown + basisVec (basisSwap upDown 0 1)) := by
  rw [timeReversalSpinHalfMulti_add,
    timeReversalSpinHalfMulti_basisVec_upDown,
    timeReversalSpinHalfMulti_basisVec_basisSwap_upDown]
  abel


end LatticeSystem.Quantum
