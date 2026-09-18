module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic

/-!
# Partial-trace vocabulary

Partial traces needed to state the two registered finite-dimensional claims.
-/

@[expose] public section

open scoped BigOperators

namespace LatticeSystem

/-- Partial trace over the right matrix index. -/
def partialTraceRight {Left Right : Type*} [Fintype Right]
    (A : Matrix (Left × Right) (Left × Right) ℂ) : Matrix Left Left ℂ :=
  fun i j ↦ ∑ k, A (i, k) (j, k)

/-- Partial trace over the left matrix index. -/
def partialTraceLeft {Left Right : Type*} [Fintype Left]
    (A : Matrix (Left × Right) (Left × Right) ℂ) : Matrix Right Right ℂ :=
  fun i j ↦ ∑ k, A (k, i) (k, j)

end LatticeSystem
