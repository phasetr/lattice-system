import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial evaluation at a diagonal matrix
(Tasaki §2.1 P1d''' β-24)

A foundational lemma: if `D = Matrix.diagonal v`, then for any polynomial
`p`, the algebra-evaluation `Polynomial.aeval D p` is the diagonal matrix
whose `(i,i)` entry is `p.eval (v i)`. In symbols,

  `aeval (diagonal v) p = diagonal (fun i => p.eval (v i))`.

This is the key step that lets us pull a Lagrange-interpolation polynomial
through the spin operator `Ŝ^{(3)} = diagonal (λ_·)` to recover the
diagonal projectors `P_k` (β-25+).

The proof uses `Polynomial.induction_on'` and reduces to the monomial
case; multiplication is closed via `Matrix.diagonal_mul_diagonal` and
the coefficient is handled via `Matrix.diagonal_smul`.

Tracked in #458.
-/

namespace LatticeSystem.Quantum

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommSemiring R]

/-- `Polynomial.aeval` at a diagonal matrix is diagonal with entries
    `p.eval (v i)` on the diagonal. -/
theorem aeval_diagonal (v : n → R) (p : R[X]) :
    aeval (Matrix.diagonal v) p =
      Matrix.diagonal (fun i : n => p.eval (v i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext i j
      by_cases h : i = j
      · subst h
        simp [Matrix.add_apply, Matrix.diagonal_apply_eq, Polynomial.eval_add]
      · simp [Matrix.add_apply, Matrix.diagonal_apply_ne _ h]
  | monomial k a =>
      rw [Polynomial.aeval_monomial,
          Matrix.algebraMap_eq_diagonal,
          Matrix.diagonal_pow,
          Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        rw [Pi.algebraMap_apply, Pi.pow_apply, Polynomial.eval_monomial]
        rfl
      · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

end LatticeSystem.Quantum
