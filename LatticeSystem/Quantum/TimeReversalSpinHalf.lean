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

/-! ## Time-reversal flips the spin: `Θ̂ Ŝ Θ̂⁻¹ = -Ŝ`

Tasaki §2.3 eq. (2.3.14) (single spin): the antilinear time
reversal `Θ̂` flips the sign of every spin component,
`Θ̂ Ŝ^(α) Θ̂⁻¹ = -Ŝ^(α)` for `α = 1, 2, 3`. Equivalently, the
equivariance form

  `Θ̂ (Ŝ^(α) v) = (-Ŝ^(α)) (Θ̂ v)`

holds for every state `v : Fin 2 → ℂ`. We record the equivariance
form (the matrix-action form is more useful in this Matrix-based
framework than the `Θ̂⁻¹ Â Θ̂` form). -/

/-- `Θ̂` flips the sign of `Ŝ^(1)`:
`Θ̂ (Ŝ^(1) · v) = (-Ŝ^(1)) · (Θ̂ v)` for every `v : Fin 2 → ℂ`. -/
theorem timeReversalSpinHalf_spinHalfOp1_mulVec (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (spinHalfOp1.mulVec v) =
      (-spinHalfOp1).mulVec (timeReversalSpinHalf v) := by
  rw [Matrix.neg_mulVec]
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, spinHalfOp1, pauliX, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Complex.conj_ofNat] <;> ring

/-- `Θ̂` flips the sign of `Ŝ^(2)`:
`Θ̂ (Ŝ^(2) · v) = (-Ŝ^(2)) · (Θ̂ v)`. -/
theorem timeReversalSpinHalf_spinHalfOp2_mulVec (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (spinHalfOp2.mulVec v) =
      (-spinHalfOp2).mulVec (timeReversalSpinHalf v) := by
  rw [Matrix.neg_mulVec]
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, spinHalfOp2, pauliY, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Complex.conj_ofNat] <;> ring

/-- `Θ̂` flips the sign of `Ŝ^(3)`:
`Θ̂ (Ŝ^(3) · v) = (-Ŝ^(3)) · (Θ̂ v)`. -/
theorem timeReversalSpinHalf_spinHalfOp3_mulVec (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (spinHalfOp3.mulVec v) =
      (-spinHalfOp3).mulVec (timeReversalSpinHalf v) := by
  rw [Matrix.neg_mulVec]
  funext i
  fin_cases i <;>
    simp [timeReversalSpinHalf, spinHalfOp3, pauliZ, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Complex.conj_ofNat] <;> ring

/-! ## Decomposition `Θ̂ = û_2 · K̂` (Tasaki §2.3 definition)

Tasaki §2.3 (p. 26) defines `Θ̂ := û_2 · K̂` where
`û_2 = exp(-iπ Ŝ^(2))` is the π rotation about the `2`-axis and
`K̂` is the antilinear complex-conjugation map of (2.3.4). We
record `K̂` and prove both the involutive property and the
factorisation identity. -/

/-- Complex conjugation `K̂` on a single-spin state vector
(Tasaki §2.3 eq. (2.3.4) at `S = 1/2`): `K̂(v) i := conj(v i)`. -/
def complexConjugationSpinHalf (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => starRingEnd ℂ (v i)

@[simp] theorem complexConjugationSpinHalf_apply
    (v : Fin 2 → ℂ) (i : Fin 2) :
    complexConjugationSpinHalf v i = starRingEnd ℂ (v i) := rfl

/-- `K̂` is involutive: `K̂(K̂ v) = v` for every state `v`. -/
theorem complexConjugationSpinHalf_sq (v : Fin 2 → ℂ) :
    complexConjugationSpinHalf (complexConjugationSpinHalf v) = v := by
  funext i
  simp [complexConjugationSpinHalf]

/-- `K̂` is additive: `K̂(v + w) = K̂(v) + K̂(w)`. -/
theorem complexConjugationSpinHalf_add (v w : Fin 2 → ℂ) :
    complexConjugationSpinHalf (v + w) =
      complexConjugationSpinHalf v + complexConjugationSpinHalf w := by
  funext i
  simp [complexConjugationSpinHalf, Pi.add_apply]

/-- `K̂` is antilinear in the scalar: `K̂(c • v) = (conj c) • K̂(v)`. -/
theorem complexConjugationSpinHalf_smul (c : ℂ) (v : Fin 2 → ℂ) :
    complexConjugationSpinHalf (c • v) =
      (starRingEnd ℂ c) • complexConjugationSpinHalf v := by
  funext i
  simp [complexConjugationSpinHalf, Pi.smul_apply, smul_eq_mul]

/-- Tasaki §2.3 definition: the time-reversal map factors as
`Θ̂ = û_2 · K̂` where `û_2 = spinHalfRot2 π` is the π rotation
about the `2`-axis. -/
theorem timeReversalSpinHalf_eq_spinHalfRot2_pi_mulVec
    (v : Fin 2 → ℂ) :
    timeReversalSpinHalf v =
      (spinHalfRot2 Real.pi).mulVec
        (complexConjugationSpinHalf v) := by
  funext i
  have hI2 : (Complex.I)^2 = -1 := Complex.I_sq
  fin_cases i <;>
    (simp [timeReversalSpinHalf, complexConjugationSpinHalf,
       spinHalfRot2_pi, spinHalfOp2, pauliY, Matrix.mulVec,
       dotProduct, Fin.sum_univ_two];
     ring_nf;
     rw [hI2];
     ring)

end LatticeSystem.Quantum
