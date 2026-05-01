/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Operators

/-!
# Cartan relations for the generic spin-`S` operators
(Tasaki §2.1 P1d''' β-2)

We prove the **Cartan relations**

  `[Ŝ^{(3)}, Ŝ^+] = Ŝ^+`,
  `[Ŝ^{(3)}, Ŝ^-] = -Ŝ^-`,

for the spin-`S` operators on `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ`.

These two relations express that `Ŝ^±` shifts the magnetic quantum
number by `±1` (eigenvectors of `ad(Ŝ^{(3)})` with eigenvalues
`±1`).  The third Cartan relation `[Ŝ^+, Ŝ^-] = 2 Ŝ^{(3)}` requires
a more involved matrix-product computation and is the subject of a
follow-up PR.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.1).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Diagonal entries of `Ŝ^{(3)}` as a named function -/

/-- The eigenvalue of `Ŝ^{(3)}` at index `k`. -/
private noncomputable def spinSOp3Diag (N : ℕ) (k : Fin (N + 1)) : ℂ :=
  (N : ℂ) / 2 - (k.val : ℂ)

/-- `Ŝ^{(3)}` is the diagonal matrix with entries `spinSOp3Diag`. -/
private theorem spinSOp3_eq_diagonal (N : ℕ) :
    spinSOp3 N = Matrix.diagonal (spinSOp3Diag N) := rfl

/-! ## Cartan relation `[Ŝ^{(3)}, Ŝ^+] = Ŝ^+` -/

/-- The Cartan relation `[Ŝ^{(3)}, Ŝ^+] = Ŝ^+`: the raising operator
shifts the magnetic quantum number by `+1`. -/
theorem spinSOp3_commutator_spinSOpPlus (N : ℕ) :
    spinSOp3 N * spinSOpPlus N - spinSOpPlus N * spinSOp3 N = spinSOpPlus N := by
  ext i j
  rw [Matrix.sub_apply, spinSOp3_eq_diagonal]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold spinSOp3Diag
  by_cases h : i.val + 1 = j.val
  · have hj : (j.val : ℂ) = (i.val : ℂ) + 1 := by exact_mod_cast h.symm
    rw [hj]; ring
  · rw [spinSOpPlus_apply_other N h]; ring

/-! ## Cartan relation `[Ŝ^{(3)}, Ŝ^-] = -Ŝ^-` -/

/-- The Cartan relation `[Ŝ^{(3)}, Ŝ^-] = -Ŝ^-`: the lowering
operator shifts the magnetic quantum number by `-1`. -/
theorem spinSOp3_commutator_spinSOpMinus (N : ℕ) :
    spinSOp3 N * spinSOpMinus N - spinSOpMinus N * spinSOp3 N =
      -spinSOpMinus N := by
  ext i j
  rw [Matrix.sub_apply, spinSOp3_eq_diagonal]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold spinSOp3Diag
  simp only [Matrix.neg_apply]
  by_cases h : j.val + 1 = i.val
  · have hi : (i.val : ℂ) = (j.val : ℂ) + 1 := by exact_mod_cast h.symm
    rw [hi]; ring
  · rw [spinSOpMinus_apply_other N h]; ring

end LatticeSystem.Quantum
