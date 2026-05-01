import LatticeSystem.Quantum.SpinS.Casimir

/-!
# Casimir invariance `[Ŝ^{(α)}, (Ŝ)²] = 0` for spin-`S`
(Tasaki §2.1 P1d''' β-18)

The Casimir `(Ŝ)² = (N(N+2)/4) · 1` is a scalar matrix, so it
commutes with every operator — in particular with each spin
generator `Ŝ^{(α)}`:

  `Commute (Ŝ^{(α)}) (Ŝ)²`,    `α ∈ {1, 2, 3}`.

This is the operator-level statement that the spin-`S` representation
is irreducible (`Ŝ^{(α)}` cannot mix Casimir eigenspaces).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Helper: any matrix commutes with a scalar multiple of the
identity matrix. -/
private theorem commute_smul_one (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (c : ℂ) :
    Commute A (c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  unfold Commute SemiconjBy
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- `Ŝ^{(1)}` commutes with the Casimir `(Ŝ)²`. -/
theorem spinSOp1_commute_total_squared (N : ℕ) :
    Commute (spinSOp1 N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) := by
  rw [spinSOp_total_squared]
  exact commute_smul_one (spinSOp1 N) _

/-- `Ŝ^{(2)}` commutes with the Casimir `(Ŝ)²`. -/
theorem spinSOp2_commute_total_squared (N : ℕ) :
    Commute (spinSOp2 N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) := by
  rw [spinSOp_total_squared]
  exact commute_smul_one (spinSOp2 N) _

/-- `Ŝ^{(3)}` commutes with the Casimir `(Ŝ)²`. -/
theorem spinSOp3_commute_total_squared (N : ℕ) :
    Commute (spinSOp3 N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) := by
  rw [spinSOp_total_squared]
  exact commute_smul_one (spinSOp3 N) _

/-- The raising operator `Ŝ^+` commutes with the Casimir. -/
theorem spinSOpPlus_commute_total_squared (N : ℕ) :
    Commute (spinSOpPlus N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) := by
  rw [spinSOp_total_squared]
  exact commute_smul_one (spinSOpPlus N) _

/-- The lowering operator `Ŝ^-` commutes with the Casimir. -/
theorem spinSOpMinus_commute_total_squared (N : ℕ) :
    Commute (spinSOpMinus N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) := by
  rw [spinSOp_total_squared]
  exact commute_smul_one (spinSOpMinus N) _

end LatticeSystem.Quantum
