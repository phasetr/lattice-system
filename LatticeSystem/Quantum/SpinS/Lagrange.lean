/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.DiagProj

/-!
# Spin-`S` eigenvalue equation `Ŝ^{(3)} · P_k = λ_k · P_k`
(Tasaki §2.1 P1d''' β-5)

The diagonal projector `P_k = spinSDiagProj N k` is an eigenvector
of `Ŝ^{(3)}` with eigenvalue `λ_k = (N : ℂ)/2 − k.val`:

  `Ŝ^{(3)} · P_k = λ_k · P_k`,    `P_k · Ŝ^{(3)} = λ_k · P_k`.

Both `Ŝ^{(3)}` and `P_k` are diagonal so they commute.  These
equations express the operator-level statement that the standard
basis `{|k⟩}_{k : Fin (N + 1)}` diagonalises `Ŝ^{(3)}` with the
prescribed eigenvalues, and they are an immediate consequence of
the diagonal-product formula `diagonal d₁ * diagonal d₂ = diagonal (d₁ * d₂)`.

This eigenvalue equation is one ingredient toward the full Lagrange
interpolation polynomial form

  `(∏_{j ≠ k} (λ_k − λ_j)) • P_k = ∏_{j ≠ k} (Ŝ^{(3)} − λ_j • 1)`,

which expresses each `P_k` as a polynomial in `Ŝ^{(3)}` and is the
core of Tasaki Problem 2.1.a.  The full Lagrange formula is
deferred to a follow-up PR — its formalisation requires either
a `Polynomial.aeval`-based formulation (since `Matrix _ _ ℂ` is
not a `CommMonoid` but the relevant matrices commute) or an
explicit recursion over a list-ordered version of the product.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `Ŝ^{(3)}` acts on the diagonal projector `P_k` by the eigenvalue
`λ_k = (N : ℂ)/2 − k`:

`Ŝ^{(3)} · P_k = λ_k · P_k`. -/
theorem spinSOp3_mul_diagProj (N : ℕ) (k : Fin (N + 1)) :
    spinSOp3 N * spinSDiagProj N k =
      (((N : ℂ) / 2 - (k.val : ℂ)) • spinSDiagProj N k) := by
  unfold spinSOp3 spinSDiagProj
  rw [Matrix.diagonal_mul_diagonal]
  ext i j'
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j'
  · subst hij
    by_cases h : i = k
    · subst h; simp
    · simp [if_neg h]
  · simp [if_neg hij]

/-- The right-multiplication version: `P_k · Ŝ^{(3)} = λ_k · P_k`. -/
theorem diagProj_mul_spinSOp3 (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k * spinSOp3 N =
      (((N : ℂ) / 2 - (k.val : ℂ)) • spinSDiagProj N k) := by
  unfold spinSOp3 spinSDiagProj
  rw [Matrix.diagonal_mul_diagonal]
  ext i j'
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j'
  · subst hij
    by_cases h : i = k
    · subst h; simp
    · simp [if_neg h]
  · simp [if_neg hij]

/-- Commutativity: `Ŝ^{(3)}` and `P_k` commute (both diagonal). -/
theorem spinSOp3_commute_diagProj (N : ℕ) (k : Fin (N + 1)) :
    Commute (spinSOp3 N) (spinSDiagProj N k) := by
  rw [Commute, SemiconjBy, spinSOp3_mul_diagProj, diagProj_mul_spinSOp3]

end LatticeSystem.Quantum
