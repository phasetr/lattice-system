import LatticeSystem.Quantum.SpinS.PlusMinusDiag
import LatticeSystem.Quantum.SpinS.MinusPlusDiag

/-!
# Third Cartan relation `[Ŝ^+, Ŝ^-] = 2 · Ŝ^{(3)}` for spin-`S`
(Tasaki §2.1 P1d''' β-19)

The third standard Cartan relation completes the SU(2) commutator
algebra:

  `[Ŝ^+, Ŝ^-] = Ŝ^+ · Ŝ^- − Ŝ^- · Ŝ^+ = 2 · Ŝ^{(3)}`.

The proof combines β-12 (`Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))`) and
β-13 (`Ŝ^- · Ŝ^+ = diag(i (N − i + 1))`):

  `(i + 1)(N − i) − i (N − i + 1) = N − 2i = 2 (N/2 − i)`,

matching the diagonal of `2 · Ŝ^{(3)}`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.1).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- The third Cartan relation: `[Ŝ^+, Ŝ^-] = 2 · Ŝ^{(3)}`. -/
theorem spinSOpPlus_commutator_spinSOpMinus (N : ℕ) :
    spinSOpPlus N * spinSOpMinus N - spinSOpMinus N * spinSOpPlus N =
      (2 : ℂ) • spinSOp3 N := by
  rw [spinSOpPlus_mul_spinSOpMinus_eq_diagonal,
      spinSOpMinus_mul_spinSOpPlus_eq_diagonal]
  unfold spinSOp3
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    simp only [smul_eq_mul]
    ring
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
        Matrix.diagonal_apply_ne _ h]
    simp

end LatticeSystem.Quantum
