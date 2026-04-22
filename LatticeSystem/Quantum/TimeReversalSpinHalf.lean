/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.SpinHalfRotation

/-!
# Time-reversal map for a single `S = 1/2` spin (Tasaki §2.3)

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
§2.3 (pp. 26–29) introduces the **time-reversal map**
`Θ̂ := û_2 · K̂` on a single quantum spin, where
`û_2 = exp(-iπ Ŝ^(2))` is the π rotation about the `2`-axis and
`K̂` is the antilinear complex-conjugation map of (2.3.4).

For `S = 1/2`, Tasaki eq. (2.3.6) gives the explicit formula

  `Θ̂((a, b)ᵀ) = (-b*, a*)ᵀ`,

i.e. `Θ̂(a |ψ^↑⟩ + b |ψ^↓⟩) = -b* |ψ^↑⟩ + a* |ψ^↓⟩`. In particular
`Θ̂ |ψ^↑⟩ = |ψ^↓⟩` and `Θ̂ |ψ^↓⟩ = -|ψ^↑⟩`. The map is antilinear
(linear under addition, conjugate-linear in scalars). At
`S = 1/2` (a half-odd-integer spin) Tasaki eq. (2.3.8) /
discussion below (2.3.9) gives the **Kramers degeneracy** identity

  `Θ̂² = -1̂`.

This module formalises the single-spin case; many-body /
sublattice-graded extensions (Tasaki §2.3 multi-spin discussion)
will follow as separate modules.

The map is implemented as a plain `Fin 2 → ℂ` function (rather
than a `Matrix` action) precisely because antilinear maps cannot
be matrices in the conventional sense — they fail
`A.mulVec (c • v) = c • A.mulVec v` for non-real `c`. The
antilinear scalar law is recorded explicitly as
`timeReversalSpinHalf_smul`.
-/

namespace LatticeSystem.Quantum

open Complex

/-- Time-reversal map for a single `S = 1/2` spin
(Tasaki §2.3 eq. (2.3.6), `S = 1/2`):

  `Θ̂(v) = (- conj(v 1), conj(v 0))`.

This is the antilinear unitary `û_2 · K̂` of Tasaki §2.3, where
`û_2` is the π rotation about the `2`-axis and `K̂` is complex
conjugation. -/
def timeReversalSpinHalf (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![- starRingEnd ℂ (v 1), starRingEnd ℂ (v 0)]

/-- The first component of `Θ̂(v)` is `-conj(v 1)`. -/
@[simp] theorem timeReversalSpinHalf_zero (v : Fin 2 → ℂ) :
    timeReversalSpinHalf v 0 = - starRingEnd ℂ (v 1) := rfl

/-- The second component of `Θ̂(v)` is `conj(v 0)`. -/
@[simp] theorem timeReversalSpinHalf_one (v : Fin 2 → ℂ) :
    timeReversalSpinHalf v 1 = starRingEnd ℂ (v 0) := rfl

/-- `Θ̂ |ψ^↑⟩ = |ψ^↓⟩` (Tasaki §2.3 eq. (2.3.5)/(2.3.6) at
`σ = 1/2`). -/
theorem timeReversalSpinHalf_spinHalfUp :
    timeReversalSpinHalf spinHalfUp = spinHalfDown := by
  funext i
  fin_cases i <;> simp [timeReversalSpinHalf, spinHalfUp, spinHalfDown]

/-- `Θ̂ |ψ^↓⟩ = -|ψ^↑⟩` (Tasaki §2.3 eq. (2.3.5)/(2.3.6) at
`σ = -1/2`). -/
theorem timeReversalSpinHalf_spinHalfDown :
    timeReversalSpinHalf spinHalfDown = -spinHalfUp := by
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, spinHalfUp, spinHalfDown]

/-- Additivity of `Θ̂`: `Θ̂(v + w) = Θ̂(v) + Θ̂(w)`. -/
theorem timeReversalSpinHalf_add (v w : Fin 2 → ℂ) :
    timeReversalSpinHalf (v + w) =
      timeReversalSpinHalf v + timeReversalSpinHalf w := by
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, Pi.add_apply, add_comm]

/-- **Antilinearity** of `Θ̂` in the scalar:
`Θ̂(c • v) = (conj c) • Θ̂(v)`. This identity is the essence of
the antilinearity warning of Tasaki §2.3 — `Θ̂` is *not* a linear
operator and hence cannot be represented by a complex matrix. -/
theorem timeReversalSpinHalf_smul (c : ℂ) (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (c • v) =
      (starRingEnd ℂ c) • timeReversalSpinHalf v := by
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, Pi.smul_apply, smul_eq_mul]

/-- **Kramers degeneracy at `S = 1/2`** (Tasaki §2.3 eq. (2.3.8),
discussion below for half-odd-integer spin):

  `Θ̂² = -1̂`,

i.e. `Θ̂(Θ̂(v)) = -v` for every `v : Fin 2 → ℂ`. The double
conjugation `conj ∘ conj = id` collapses, leaving an overall sign
`-1` from the explicit `(-conj(v 1), conj(v 0))` formula. -/
theorem timeReversalSpinHalf_sq (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (timeReversalSpinHalf v) = -v := by
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, Pi.neg_apply]

end LatticeSystem.Quantum
