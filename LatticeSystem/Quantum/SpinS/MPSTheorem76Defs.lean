import LatticeSystem.Quantum.SpinS.MPSTheorem75Defs

/-!
# Matrix product state definitions for Tasaki Theorem 7.6

This file defines exact equality of every periodic matrix product state trace coefficient, including
the empty word. It is the concrete equality hypothesis used in Tasaki Theorem 7.6, together with its
relaxation to all sufficiently long chains, which is the form the theorem is actually proved in.

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

/-- Two MPS matrix families generate the same periodic state on all sufficiently long chains when
their trace coefficients agree at every length beyond some threshold.  Short chains are excluded on
purpose: the coefficients of a length below the spanning length can vanish identically (as they do
for the traceless spin-`1` Pauli family at length one), in which case they carry no information at
all.  This is the hypothesis Tasaki Theorem 7.6 is actually proved from. -/
def GeneratesSameMPSEventually (A B : MPSMatrices D N) : Prop :=
  ∃ ℓ₀ : ℕ, ∀ (L : ℕ), ℓ₀ ≤ L → ∀ ss : Fin L → Fin (N + 1),
    Matrix.trace (orderedProd A (List.ofFn ss)) =
      Matrix.trace (orderedProd B (List.ofFn ss))

/-- Exact equality of all trace coefficients is the relaxed hypothesis at threshold zero. -/
theorem GeneratesSameMPS.eventually {A B : MPSMatrices D N} (h : GeneratesSameMPS A B) :
    GeneratesSameMPSEventually A B :=
  ⟨0, fun L _ ss => h L ss⟩

end LatticeSystem.Quantum
