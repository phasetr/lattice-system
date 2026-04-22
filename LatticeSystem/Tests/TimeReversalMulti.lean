/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TimeReversalMulti
import LatticeSystem.Quantum.TimeReversalMulti.Heisenberg

/-!
# Test coverage for the multi-spin time-reversal map (Tasaki §2.3)
-/

namespace LatticeSystem.Tests.TimeReversalMulti

open LatticeSystem.Quantum

/-! ## `flipConfig` -/

example (σ : Fin 3 → Fin 2) (x : Fin 3) :
    flipConfig σ x = 1 - σ x := rfl

example (σ : Fin 3 → Fin 2) :
    flipConfig (flipConfig σ) = σ :=
  flipConfig_involutive σ

/-! ## `timeReversalSign` -/

example : timeReversalSign (0 : Fin 2) = 1 := timeReversalSign_zero
example : timeReversalSign (1 : Fin 2) = -1 := timeReversalSign_one

example (s : Fin 2) :
    timeReversalSign s * timeReversalSign (1 - s) = -1 :=
  timeReversalSign_mul_flip s

/-! ## Multi-spin Kramers degeneracy `Θ̂_tot² = (-1)^|Λ| · 1̂` -/

example (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) =
      ((-1 : ℂ) ^ (Fintype.card (Fin 3))) • v :=
  timeReversalSpinHalfMulti_sq v

example (v : (Fin 4 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) =
      ((-1 : ℂ) ^ (Fintype.card (Fin 4))) • v :=
  timeReversalSpinHalfMulti_sq v

/-- Specialisation: at `|Λ| = 3` (odd), `Θ̂_tot² = -1̂`. -/
example (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) = -v := by
  rw [timeReversalSpinHalfMulti_sq]
  simp [Fintype.card_fin, show ((-1 : ℂ) ^ 3) = -1 from by norm_num]

/-- Specialisation: at `|Λ| = 4` (even), `Θ̂_tot² = +1̂`. -/
example (v : (Fin 4 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) = v := by
  rw [timeReversalSpinHalfMulti_sq]
  simp [Fintype.card_fin, show ((-1 : ℂ) ^ 4) = 1 from by norm_num]

/-! ## `Θ̂_tot` action on basis states -/

example (σ : Fin 3 → Fin 2) :
    timeReversalSpinHalfMulti (basisVec σ) =
      (∏ x : Fin 3, timeReversalSign (flipConfig σ x)) •
        basisVec (flipConfig σ) :=
  timeReversalSpinHalfMulti_basisVec σ

/-! ## Multi-site σ^z sign-flip equivariance -/

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliZ).mulVec v) =
      (-(onSite x pauliZ)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_pauliZ_mulVec x v

/-! ## `siteFlipAt` helpers -/

example (τ : Fin 3 → Fin 2) (x : Fin 3) :
    siteFlipAt τ x x = 1 - τ x := siteFlipAt_self τ x

example (τ : Fin 3 → Fin 2) {x y : Fin 3} (h : y ≠ x) :
    siteFlipAt τ x y = τ y := siteFlipAt_of_ne τ h

example (τ : Fin 3 → Fin 2) (x : Fin 3) :
    flipConfig (siteFlipAt τ x) = siteFlipAt (flipConfig τ) x :=
  flipConfig_siteFlipAt_comm τ x

example (τ : Fin 3 → Fin 2) (x : Fin 3) :
    siteFlipAt (siteFlipAt τ x) x = τ := siteFlipAt_involutive τ x

/-! ## `(onSite x σ^x).mulVec (basisVec σ) = basisVec (siteFlipAt σ x)` -/

example (x : Fin 3) (σ : Fin 3 → Fin 2) :
    ((onSite x pauliX).mulVec (basisVec σ) : (Fin 3 → Fin 2) → ℂ) =
      basisVec (siteFlipAt σ x) :=
  onSite_pauliX_mulVec_basisVec x σ

/-- General `(onSite x σ^x).mulVec v` evaluated at `τ` equals
`v (siteFlipAt τ x)` (linear extension to arbitrary states). -/
example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) (τ : Fin 3 → Fin 2) :
    ((onSite x pauliX).mulVec v) τ = v (siteFlipAt τ x) :=
  onSite_pauliX_mulVec_apply x v τ

/-! ## σ^x sign-product flip and equivariance -/

example (τ : Fin 3 → Fin 2) (x : Fin 3) :
    (∏ y : Fin 3, timeReversalSign ((siteFlipAt τ x) y)) =
      -(∏ y : Fin 3, timeReversalSign (τ y)) :=
  timeReversalSign_prod_siteFlipAt τ x

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliX).mulVec v) =
      (-(onSite x pauliX)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_pauliX_mulVec x v

/-! ## σ^y multi-site sign-flip equivariance -/

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliY).mulVec v) =
      (-(onSite x pauliY)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_pauliY_mulVec x v

/-! ## Θ̂_tot additivity / antilinearity -/

example (v w : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (v + w) =
      timeReversalSpinHalfMulti v + timeReversalSpinHalfMulti w :=
  timeReversalSpinHalfMulti_add v w

example (c : ℂ) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (c • v) =
      (starRingEnd ℂ c) • timeReversalSpinHalfMulti v :=
  timeReversalSpinHalfMulti_smul c v

example (r : ℝ) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((r : ℂ) • v) =
      (r : ℂ) • timeReversalSpinHalfMulti v :=
  timeReversalSpinHalfMulti_real_smul r v

/-! ## Spin-1/2 op equivariance (Tasaki §2.3 (2.3.14)) -/

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x spinHalfOp1).mulVec v) =
      (-(onSite x spinHalfOp1)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_spinHalfOp1_mulVec x v

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x spinHalfOp2).mulVec v) =
      (-(onSite x spinHalfOp2)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_spinHalfOp2_mulVec x v

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x spinHalfOp3).mulVec v) =
      (-(onSite x spinHalfOp3)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_spinHalfOp3_mulVec x v

/-! ## Time-reversal invariance of `Ŝ_x · Ŝ_y` -/

example (x y : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((spinHalfDot x y).mulVec v) =
      (spinHalfDot x y).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_spinHalfDot_mulVec x y v

/-! ## Time-reversal invariance of the Heisenberg Hamiltonian -/

example (J : Fin 3 → Fin 3 → ℂ) (hJ : ∀ x y, starRingEnd ℂ (J x y) = J x y)
    (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((heisenbergHamiltonian J).mulVec v) =
      (heisenbergHamiltonian J).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec J hJ v

/-! ## Chain Heisenberg time-reversal invariance -/

example (N : ℕ) (J : ℝ) (v : (Fin (N + 1) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (openChainCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (openChainCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_openChainHeisenberg_mulVec N J v

example (N : ℕ) (J : ℝ) (v : (Fin (N + 2) → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((heisenbergHamiltonian (periodicChainCoupling N J)).mulVec v) =
      (heisenbergHamiltonian (periodicChainCoupling N J)).mulVec
        (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_periodicChainHeisenberg_mulVec N J v

/-! ## Two-site Néel / singlet time reversal -/

example :
    timeReversalSpinHalfMulti (basisVec upDown : (Fin 2 → Fin 2) → ℂ) =
      -basisVec (basisSwap upDown 0 1) :=
  timeReversalSpinHalfMulti_basisVec_upDown

example :
    timeReversalSpinHalfMulti
        (basisVec (basisSwap upDown 0 1) : (Fin 2 → Fin 2) → ℂ) =
      -basisVec upDown :=
  timeReversalSpinHalfMulti_basisVec_basisSwap_upDown

example :
    timeReversalSpinHalfMulti
        ((basisVec upDown - basisVec (basisSwap upDown 0 1)) :
          (Fin 2 → Fin 2) → ℂ) =
      basisVec upDown - basisVec (basisSwap upDown 0 1) :=
  timeReversalSpinHalfMulti_singlet

example :
    timeReversalSpinHalfMulti
        ((basisVec upDown + basisVec (basisSwap upDown 0 1)) :
          (Fin 2 → Fin 2) → ℂ) =
      -(basisVec upDown + basisVec (basisSwap upDown 0 1)) :=
  timeReversalSpinHalfMulti_triplet_zero

/-! ## A. decide-based universal: `flipConfig` / `siteFlipAt`
properties on small `Fin n` (Phase 1 PR 5 strengthening, refactor
plan v4 §2.1 method A) -/

/-- `flipConfig` is involutive (universally on `Fin 2 → Fin 2`,
all 4 configurations). -/
example : ∀ σ : Fin 2 → Fin 2, flipConfig (flipConfig σ) = σ := by
  intro σ; exact flipConfig_involutive σ

/-- `siteFlipAt` is involutive (universally on `Fin 2 → Fin 2`,
all 4 configurations × 2 sites = 8 cases). -/
example :
    ∀ σ : Fin 2 → Fin 2, ∀ x : Fin 2,
        siteFlipAt (siteFlipAt σ x) x = σ := by
  intro σ x; exact siteFlipAt_involutive σ x

/-! ## C. bridge identity (Phase 1 PR 5 strengthening, refactor
plan v4 §2.1 method C) -/

/-- `flipConfig σ x = 1 - σ x` reaffirmed as a bridge between the
function form and the per-site arithmetic form. -/
example (σ : Fin 3 → Fin 2) (x : Fin 3) :
    flipConfig σ x = 1 - σ x := rfl

/-! ## G. small exhaustive on `Fin 2 → Fin 2` (Phase 1 PR 5
strengthening, refactor plan v4 §2.1 method G) -/

/-- `siteFlipAt` self-vs-other agreement on `Fin 2`: at the flipped
site value differs (`= 1 - σ x`); elsewhere unchanged. -/
example :
    ∀ τ : Fin 3 → Fin 2, ∀ x : Fin 3,
        siteFlipAt τ x x = 1 - τ x := by
  intro τ x; exact siteFlipAt_self τ x

example (τ : Fin 3 → Fin 2) {x y : Fin 3} (h : y ≠ x) :
    siteFlipAt τ x y = τ y := siteFlipAt_of_ne τ h

end LatticeSystem.Tests.TimeReversalMulti
