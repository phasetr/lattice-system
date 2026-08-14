import LatticeSystem.Quantum.Rotation3D

/-!
# Test coverage for Quantum/Rotation3D

A+B+D coverage for `rot3D{1,2,3}Pi` (per refactor plan v4 §9 mapping
table; refactor Phase 1 PR 13, #281).

Extended (refactor #5187, R1b commit 1) with a full public-surface
characterization: application pins for all 15 public theorems, plus 6
literal-matrix characterization examples copied verbatim from the
current production definitions. These pins are base-green
characterization tests (they hold against the pre-refactor
implementation) and are not "Red" in the TDD sense; regression
protection for the upcoming private-core refactor is instead obtained
from controlled mutations applied (and discarded) against the
implementation head.
-/

namespace LatticeSystem.Tests.Rotation3D

open LatticeSystem.Quantum

/-! ## D. `(R^(α)_π)² = 1` for the 3D π-rotations -/

example : rot3D1Pi * rot3D1Pi = 1 := rot3D1Pi_sq
example : rot3D2Pi * rot3D2Pi = 1 := rot3D2Pi_sq
example : rot3D3Pi * rot3D3Pi = 1 := rot3D3Pi_sq

/-! ## Products of distinct-axis π-rotations -/

example : rot3D1Pi * rot3D2Pi = rot3D3Pi := rot3D1Pi_mul_rot3D2Pi
example : rot3D2Pi * rot3D3Pi = rot3D1Pi := rot3D2Pi_mul_rot3D3Pi
example : rot3D3Pi * rot3D1Pi = rot3D2Pi := rot3D3Pi_mul_rot3D1Pi

/-! ## Commutativity of distinct-axis π-rotations -/

example : rot3D1Pi * rot3D2Pi = rot3D2Pi * rot3D1Pi := rot3D1Pi_comm_rot3D2Pi
example : rot3D2Pi * rot3D3Pi = rot3D3Pi * rot3D2Pi := rot3D2Pi_comm_rot3D3Pi
example : rot3D3Pi * rot3D1Pi = rot3D1Pi * rot3D3Pi := rot3D3Pi_comm_rot3D1Pi

/-! ## General-θ rotations at θ = 0 -/

example : rot3D3 0 = 1 := rot3D3_zero
example : rot3D1 0 = 1 := rot3D1_zero
example : rot3D2 0 = 1 := rot3D2_zero

/-! ## General-θ rotations at θ = π agree with the explicit π-rotations -/

example : rot3D3 Real.pi = rot3D3Pi := rot3D3_pi
example : rot3D1 Real.pi = rot3D1Pi := rot3D1_pi
example : rot3D2 Real.pi = rot3D2Pi := rot3D2_pi

/-! ## Literal-matrix characterization of the π-rotations

These pin the exact entries of `rot3D{1,2,3}Pi`, copied verbatim from
the current production definitions, so that a future refactor that
silently permutes rows/columns or flips a sign is caught even though
`rot3D{1,2,3}Pi_sq` alone would not detect it.
-/

example : rot3D1Pi = !![1, 0, 0;
                         0, -1, 0;
                         0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : rot3D2Pi = !![-1, 0, 0;
                         0, 1, 0;
                         0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : rot3D3Pi = !![-1, 0, 0;
                         0, -1, 0;
                         0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Literal-matrix characterization of the general-θ rotations

These pin the exact entries of `rot3D{1,2,3} θ` for arbitrary `θ`,
copied verbatim from the current production definitions.
-/

example : ∀ θ : ℝ, rot3D1 θ = !![1, 0, 0;
                                  0, Real.cos θ, -Real.sin θ;
                                  0, Real.sin θ, Real.cos θ] := by
  intro θ
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : ∀ θ : ℝ, rot3D2 θ = !![Real.cos θ, 0, Real.sin θ;
                                  0, 1, 0;
                                  -Real.sin θ, 0, Real.cos θ] := by
  intro θ
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : ∀ θ : ℝ, rot3D3 θ = !![Real.cos θ, -Real.sin θ, 0;
                                  Real.sin θ, Real.cos θ, 0;
                                  0, 0, 1] := by
  intro θ
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end LatticeSystem.Tests.Rotation3D
