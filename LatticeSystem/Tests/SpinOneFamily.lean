/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinOne
import LatticeSystem.Quantum.SpinOneBasis
import LatticeSystem.Quantum.SpinOneDecomp

/-!
# Test coverage for the SpinOne cluster

A+C+G+D coverage for `Quantum/SpinOne{,Basis,Decomp}.lean` (per
refactor plan v4 §9 mapping table; refactor Phase 1 PR 11, #281).
-/

namespace LatticeSystem.Tests.SpinOneFamily

open LatticeSystem.Quantum

/-! ## D. signature shims for `spinOneOp{1,2,3}` Hermiticity -/

example : spinOneOp1.IsHermitian := spinOneOp1_isHermitian
example : spinOneOp2.IsHermitian := spinOneOp2_isHermitian
example : spinOneOp3.IsHermitian := spinOneOp3_isHermitian

/-! ## D. Casimir `Σ (Ŝ^(α))² = S(S+1)·1 = 2·1` for `S = 1` -/

example :
    spinOneOp1 * spinOneOp1 + spinOneOp2 * spinOneOp2 +
        spinOneOp3 * spinOneOp3 = (2 : ℂ) • 1 :=
  spinOne_total_spin_squared

/-! ## D. Commutator algebra `[Ŝ^(α), Ŝ^(β)] = i·Ŝ^(γ)` (cyclic) -/

example :
    spinOneOp1 * spinOneOp2 - spinOneOp2 * spinOneOp1 =
      Complex.I • spinOneOp3 :=
  spinOneOp1_commutator_spinOneOp2

example :
    spinOneOp2 * spinOneOp3 - spinOneOp3 * spinOneOp2 =
      Complex.I • spinOneOp1 :=
  spinOneOp2_commutator_spinOneOp3

example :
    spinOneOp3 * spinOneOp1 - spinOneOp1 * spinOneOp3 =
      Complex.I • spinOneOp2 :=
  spinOneOp3_commutator_spinOneOp1

/-! ## A + B. spin-1 basis vectors on `Fin 3` -/

example : spinOnePlus = ![1, 0, 0] := rfl
example : spinOneZero = ![0, 1, 0] := rfl

/-- `spinOneOp3` is diagonal with eigenvalues `(1, 0, -1)`. -/
example :
    spinOneOp3 = !![1, 0, 0; 0, 0, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end LatticeSystem.Tests.SpinOneFamily
