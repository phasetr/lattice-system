import LatticeSystem.Quantum.SpinOne
import LatticeSystem.Quantum.SpinOneBasis
import LatticeSystem.Quantum.SpinOneDecomp

/-!
# Test coverage for the SpinOne cluster

A+C+G+D coverage for `Quantum/SpinOne{,Basis,Decomp}.lean` (per
refactor plan v4 §9 mapping table; refactor Phase 1 PR 11, #281).

## Spin-1 rotation public-surface pins (#5241)

The `## Spin-1 rotation family` section below pins all 30 public
rotation-family declarations of `SpinOneBasis.lean` (21 literal
π-rotation declarations + 9 closed-form θ-rotation declarations):
6 literal-value/shape pins for the 3 `spinOnePiRot{1,2,3}` matrix
defs and the 3 `spinOneRot{1,2,3}` θ-family defs, plus 24 application
pins for every remaining public theorem in that inventory. These are
**base-green characterization pins against the current (pre-refactor)
implementation, not Red tests**: they are expected to pass today and
are required to keep passing, unchanged, after the private-core
factoring lands in commit 2. Mutation evidence (that the pins are
load-bearing, i.e. would actually fail under a faulty refactor) is
recorded separately, disposable and uncommitted, per issue #5241.
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

/-! ## Spin-1 rotation family (#5241): 30 public rotation-family pins

Base-green characterization pins (not Red), copied byte-verbatim from
the current `SpinOneBasis.lean` bodies/statements. 6 literal-value/shape
pins (3 `spinOnePiRot{1,2,3}` defs + 3 `spinOneRot{1,2,3}` θ-family
defs) + 24 application pins (every remaining public theorem: π-family
`_eq`/`_sq`/`_comm_*`/`_mulVec_*`, θ-family `_zero`/`_pi`) = 30. -/

-- Literal-value pins: the 3 π-rotation matrix defs.

example : spinOnePiRot1 = !![0, 0, -1; 0, -1, 0; -1, 0, 0] := rfl

example : spinOnePiRot2 = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := rfl

example : spinOnePiRot3 = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl

-- Literal-shape pins: the 3 θ-rotation closed-form defs (load-bearing).

example : ∀ θ : ℝ, spinOneRot3 θ =
    1 - (Complex.I * (Real.sin θ : ℂ)) • spinOneOp3 -
      ((1 : ℂ) - (Real.cos θ : ℂ)) • (spinOneOp3 * spinOneOp3) :=
  fun _ => rfl

example : ∀ θ : ℝ, spinOneRot1 θ =
    1 - (Complex.I * (Real.sin θ : ℂ)) • spinOneOp1 -
      ((1 : ℂ) - (Real.cos θ : ℂ)) • (spinOneOp1 * spinOneOp1) :=
  fun _ => rfl

example : ∀ θ : ℝ, spinOneRot2 θ =
    1 - (Complex.I * (Real.sin θ : ℂ)) • spinOneOp2 -
      ((1 : ℂ) - (Real.cos θ : ℂ)) • (spinOneOp2 * spinOneOp2) :=
  fun _ => rfl

-- Application pins: π-family `_eq` (`û_α = 1 - 2·(Ŝ^α)²`).

example :
    (spinOnePiRot3 : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - (2 : ℂ) • (spinOneOp3 * spinOneOp3) :=
  spinOnePiRot3_eq

example :
    (spinOnePiRot1 : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - (2 : ℂ) • (spinOneOp1 * spinOneOp1) :=
  spinOnePiRot1_eq

example :
    (spinOnePiRot2 : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - (2 : ℂ) • (spinOneOp2 * spinOneOp2) :=
  spinOnePiRot2_eq

-- Application pins: π-family squares `(û_α)² = 1`.

example : spinOnePiRot1 * spinOnePiRot1 = 1 := spinOnePiRot1_sq
example : spinOnePiRot2 * spinOnePiRot2 = 1 := spinOnePiRot2_sq
example : spinOnePiRot3 * spinOnePiRot3 = 1 := spinOnePiRot3_sq

-- Application pins: π-family commutation `û_α · û_β = û_β · û_α`.

example :
    spinOnePiRot1 * spinOnePiRot2 = spinOnePiRot2 * spinOnePiRot1 :=
  spinOnePiRot1_comm_spinOnePiRot2

example :
    spinOnePiRot2 * spinOnePiRot3 = spinOnePiRot3 * spinOnePiRot2 :=
  spinOnePiRot2_comm_spinOnePiRot3

example :
    spinOnePiRot3 * spinOnePiRot1 = spinOnePiRot1 * spinOnePiRot3 :=
  spinOnePiRot3_comm_spinOnePiRot1

-- Application pins: π-family action on the basis states (Tasaki Problem 2.1.g).

example :
    spinOnePiRot3.mulVec spinOnePlus = -1 • spinOnePlus :=
  spinOnePiRot3_mulVec_spinOnePlus

example :
    spinOnePiRot3.mulVec spinOneZero = spinOneZero :=
  spinOnePiRot3_mulVec_spinOneZero

example :
    spinOnePiRot3.mulVec spinOneMinus = -1 • spinOneMinus :=
  spinOnePiRot3_mulVec_spinOneMinus

example :
    spinOnePiRot2.mulVec spinOnePlus = spinOneMinus :=
  spinOnePiRot2_mulVec_spinOnePlus

example :
    spinOnePiRot2.mulVec spinOneZero = -1 • spinOneZero :=
  spinOnePiRot2_mulVec_spinOneZero

example :
    spinOnePiRot2.mulVec spinOneMinus = spinOnePlus :=
  spinOnePiRot2_mulVec_spinOneMinus

example :
    spinOnePiRot1.mulVec spinOnePlus = -1 • spinOneMinus :=
  spinOnePiRot1_mulVec_spinOnePlus

example :
    spinOnePiRot1.mulVec spinOneZero = -1 • spinOneZero :=
  spinOnePiRot1_mulVec_spinOneZero

example :
    spinOnePiRot1.mulVec spinOneMinus = -1 • spinOnePlus :=
  spinOnePiRot1_mulVec_spinOneMinus

-- Application pins: θ-family boundary values (`Û^(α)_0 = 1`, `Û^(α)_π = û_α`).

example : spinOneRot3 0 = 1 := spinOneRot3_zero
example : spinOneRot3 Real.pi = spinOnePiRot3 := spinOneRot3_pi
example : spinOneRot1 0 = 1 := spinOneRot1_zero
example : spinOneRot2 0 = 1 := spinOneRot2_zero
example : spinOneRot1 Real.pi = spinOnePiRot1 := spinOneRot1_pi
example : spinOneRot2 Real.pi = spinOnePiRot2 := spinOneRot2_pi

end LatticeSystem.Tests.SpinOneFamily
