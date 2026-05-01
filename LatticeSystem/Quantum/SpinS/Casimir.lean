import LatticeSystem.Quantum.SpinS.Op3Square
import LatticeSystem.Quantum.SpinS.PlusMinusDiag
import LatticeSystem.Quantum.SpinS.MinusPlusDiag

/-!
# Casimir identity `(Ŝ)² = (N(N+2)/4) · 1` for spin-`S`
(Tasaki §2.1 P1d''' β-14)

The total spin-squared (Casimir) operator is a constant multiple of
the identity matrix:

  `(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1`,

equivalent to `S(S+1) · 1` for `S = N/2`.  This is the standard
quantum-mechanical statement that the irreducible spin-`S`
representation has Casimir eigenvalue `S(S+1)`, and the **scalar**
nature of `(Ŝ)²` reflects Schur's lemma.

The proof combines:

* `(Ŝ^{(1)})² + (Ŝ^{(2)})² = (1/2) · (Ŝ^+ · Ŝ^- + Ŝ^- · Ŝ^+)`
  (via `Ŝ^{(1,2)} = (Ŝ^+ ± Ŝ^-)/(2/2i)` algebra),
* `Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))` (β-12),
* `Ŝ^- · Ŝ^+ = diag(i (N − i + 1))` (β-13),
* `(Ŝ^{(3)})² = diag((N/2 − i)²)` (β-11).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `(Ŝ^{(1)})² + (Ŝ^{(2)})² = (1/2) · (Ŝ^+ · Ŝ^- + Ŝ^- · Ŝ^+)`. -/
theorem spinSOp1_sq_add_spinSOp2_sq (N : ℕ) :
    spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N =
      (1/2 : ℂ) • (spinSOpPlus N * spinSOpMinus N +
        spinSOpMinus N * spinSOpPlus N) := by
  unfold spinSOp1 spinSOp2
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (1/2 : ℂ) * (1/2 : ℂ) = 1/4 from by norm_num]
  rw [show (1 / (2 * I) : ℂ) * (1 / (2 * I) : ℂ) = -(1/4 : ℂ) from by
    have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
    have h2I_sq : (2 * I : ℂ) * (2 * I) = -4 := by
      rw [show (2 * I : ℂ) * (2 * I) = 4 * (I * I) from by ring, hI]; ring
    rw [show (1 / (2 * I) : ℂ) * (1 / (2 * I)) = 1 / ((2 * I) * (2 * I)) from by ring]
    rw [h2I_sq]
    norm_num]
  -- Goal: (1/4) • ((Ŝ^+ + Ŝ^-) * (Ŝ^+ + Ŝ^-)) + (-(1/4)) • ((Ŝ^+ - Ŝ^-) * (Ŝ^+ - Ŝ^-))
  --     = (1/2) • (Ŝ^+ Ŝ^- + Ŝ^- Ŝ^+)
  rw [show (spinSOpPlus N + spinSOpMinus N) * (spinSOpPlus N + spinSOpMinus N) =
        spinSOpPlus N * spinSOpPlus N + spinSOpPlus N * spinSOpMinus N +
        spinSOpMinus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N from by
    rw [add_mul, mul_add, mul_add]; abel]
  rw [show (spinSOpPlus N - spinSOpMinus N) * (spinSOpPlus N - spinSOpMinus N) =
        spinSOpPlus N * spinSOpPlus N - spinSOpPlus N * spinSOpMinus N -
        spinSOpMinus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N from by
    rw [sub_mul, mul_sub, mul_sub]; abel]
  module

/-- **Casimir identity**: `(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1`. -/
theorem spinSOp_total_squared (N : ℕ) :
    spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := by
  rw [spinSOp1_sq_add_spinSOp2_sq, spinSOp3_sq_eq_diagonal,
      spinSOpPlus_mul_spinSOpMinus_eq_diagonal,
      spinSOpMinus_mul_spinSOpPlus_eq_diagonal]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq]
    simp only [smul_eq_mul]
    ring
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
        Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    simp

end LatticeSystem.Quantum
