/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.AllUnitsAdjoin

/-!
# Spanning theorem for the spin-`S` operators
(Tasaki §2.1 P1d''' β-32)

The **main theorem** (Tasaki Problem 2.1.a, p. 15, solution S.1 p. 493)
in its `Algebra.adjoin` form:

  `Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}
     = (⊤ : Subalgebra ℂ (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))`.

Equivalently, every operator on the `(2S+1)`-dimensional spin-`S`
Hilbert space `ℂ^{N+1}` is a polynomial in `{1̂, Ŝ^{(α)}}`.

Proof: every matrix unit `E_{i, j} = single i j 1` is in the adjoin
(β-31). Multiplying by the scalar `M_{i,j}` keeps it in the adjoin
(subalgebras are `ℂ`-linear). The entry-wise decomposition
`M = ∑_{i, j} M_{i,j} · E_{i, j}` (`Matrix.matrix_eq_sum_single`)
expresses every matrix as a sum of such elements, so every matrix
is in the adjoin.

Tracked in #458.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15), solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Every matrix is in `Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
theorem matrix_mem_adjoin (N : ℕ) (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    M ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  rw [Matrix.matrix_eq_sum_single M]
  refine Subalgebra.sum_mem _ ?_
  intro i _
  refine Subalgebra.sum_mem _ ?_
  intro j _
  -- Goal: single i j (M i j) ∈ adjoin
  rw [show Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : ℂ) from by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact Subalgebra.smul_mem _ (matrix_single_mem_adjoin i j) _

/-- **Spanning theorem** (Tasaki Problem 2.1.a):
the spin operators `{Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}` generate the whole
matrix algebra `M_{N+1}(ℂ)` as a unital `ℂ`-subalgebra. -/
theorem spinS_adjoin_eq_top (N : ℕ) :
    Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) = ⊤ :=
  Algebra.eq_top_iff.mpr (matrix_mem_adjoin N)

end LatticeSystem.Quantum
