import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Spin-`S` total spin squared `(Ŝ_tot)²`
(Tasaki §2.5 Phase B-β β-3p)

The quantum-mechanical Casimir invariant of the `su(2)` algebra
acting on the multi-site spin-`S` Hilbert space:

  `(Ŝ_tot)² := Σ_{α=1,2,3} (Ŝ_tot^{(α)})²`.

Direct generalisation of `totalSpinHalfSquared` to arbitrary spin.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- Total spin-`S` squared. -/
noncomputable def totalSpinSSquared : ManyBodyOpS Λ N :=
  totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
    totalSpinSOp2 Λ N * totalSpinSOp2 Λ N +
    totalSpinSOp3 Λ N * totalSpinSOp3 Λ N

/-- `(Ŝ_tot)²` is Hermitian. -/
theorem totalSpinSSquared_isHermitian :
    (totalSpinSSquared Λ N).IsHermitian := by
  unfold totalSpinSSquared
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinSOp1_isHermitian Λ N)]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinSOp2_isHermitian Λ N)]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, (totalSpinSOp3_isHermitian Λ N)]

end LatticeSystem.Quantum
