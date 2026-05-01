/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.LadderStates

/-!
# Test coverage for spin-`S` ladder action on basis vectors
(Tasaki §2.1 P1d''' β-16)
-/

namespace LatticeSystem.Tests.SpinSLadderStates

open LatticeSystem.Quantum

/-- `Ŝ^+ · |k⟩ = √(k(N − k + 1)) · |k − 1⟩` for `k ≥ 1`. -/
example (N : ℕ) (k : Fin (N + 1)) (h : 0 < k.val) :
    (spinSOpPlus N).mulVec (Pi.single k 1) =
      ((Real.sqrt (((k.val : ℝ)) * ((N : ℝ) - (k.val : ℝ) + 1)) : ℝ) : ℂ) •
        (Pi.single ⟨k.val - 1, by have := k.isLt; omega⟩ 1 :
          Fin (N + 1) → ℂ) :=
  spinSOpPlus_mulVec_basis N k h

/-- `Ŝ^- · |k⟩ = √((N − k)(k + 1)) · |k + 1⟩` for `k.val + 1 ≤ N`. -/
example (N : ℕ) (k : Fin (N + 1)) (h : k.val + 1 < N + 1) :
    (spinSOpMinus N).mulVec (Pi.single k 1) =
      ((Real.sqrt (((N : ℝ) - (k.val : ℝ)) * ((k.val : ℝ) + 1)) : ℝ) : ℂ) •
        (Pi.single ⟨k.val + 1, h⟩ 1 : Fin (N + 1) → ℂ) :=
  spinSOpMinus_mulVec_basis N k h

end LatticeSystem.Tests.SpinSLadderStates
