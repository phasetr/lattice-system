import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Spin-`S` rotation about axis 1

(PR #3895, Issue #3739): the matrix `exp(-iθ Ŝ¹)` for general spin `S = N/2`,
parametrised by the angle `θ : ℝ`. At `θ = π/2` this is the axis-swap unitary
needed to instantiate `AxisSwapUnitaryS N` for general N — the only blocker
identified by PR #3889 (`General-N truly unconditional capstone`) for the
truly-unconditional Tasaki §2.5 Theorem 2.4 ≤ 2 closure at general spin.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace

/-- **Spin-`S` rotation about axis 1**, `exp(-iθ Ŝ¹)`. -/
noncomputable def spinSRot1 (N : ℕ) (θ : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  exp (-(((θ : ℂ) * Complex.I)) • spinSOp1 N)

/-- **At `θ = 0`, `exp(0) = 1`**. -/
theorem spinSRot1_zero (N : ℕ) : spinSRot1 N 0 = 1 := by
  unfold spinSRot1
  simp [exp_zero]

end LatticeSystem.Quantum
