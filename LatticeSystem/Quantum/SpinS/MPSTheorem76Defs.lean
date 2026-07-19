import LatticeSystem.Quantum.SpinS.MPSTheorem75Defs

/-!
# Matrix product state definitions for Tasaki Theorem 7.6

This file defines exact equality of every periodic matrix product state trace coefficient, including
the empty word. It is the concrete equality hypothesis used in Tasaki Theorem 7.6.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.6, eq. (7.2.43), p. 203.
-/

namespace LatticeSystem.Quantum

variable {D N : ℕ}

/-- Two MPS matrix families generate the same periodic state when all their trace coefficients
agree, including at length zero. This is the equality hypothesis in Tasaki eq. (7.2.43). -/
def GeneratesSameMPS (A B : MPSMatrices D N) : Prop :=
  ∀ (L : ℕ) (ss : Fin L → Fin (N + 1)),
    Matrix.trace (orderedProd A (List.ofFn ss)) =
      Matrix.trace (orderedProd B (List.ofFn ss))

end LatticeSystem.Quantum
