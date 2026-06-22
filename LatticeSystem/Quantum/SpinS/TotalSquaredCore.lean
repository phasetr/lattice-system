import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.MultiSiteCommutator

/-!
# Total spin squared: SU(2) cyclic commutators (foundation)

Foundational layer extracted from `TotalSquared.lean` for build speed.  This file collects the
total-spin SU(2) cyclic commutators in named form.

The Casimir invariance `[(Ŝ_tot)², Ŝ_tot^{(α)}] = 0`, the magnetization-subspace membership, and the
Casimir as a sum of two-site dot products are kept in the capstone module `TotalSquared.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- Total spin-`S` squared. -/
noncomputable def totalSpinSSquared : ManyBodyOpS Λ N :=
  totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
    totalSpinSOp2 Λ N * totalSpinSOp2 Λ N +
    totalSpinSOp3 Λ N * totalSpinSOp3 Λ N

/-- Definitional unfolding. -/
theorem totalSpinSSquared_def :
    totalSpinSSquared Λ N =
      totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
        totalSpinSOp2 Λ N * totalSpinSOp2 Λ N +
        totalSpinSOp3 Λ N * totalSpinSOp3 Λ N := rfl

/-- Re-expression of `totalSpinSSquared` as a finite sum of squares
of total operators (matching the definition with `^2` instead of
`mul` self). -/
theorem totalSpinSSquared_eq_pow_sum :
    totalSpinSSquared Λ N =
      totalSpinSOp1 Λ N ^ 2 + totalSpinSOp2 Λ N ^ 2 + totalSpinSOp3 Λ N ^ 2 := by
  unfold totalSpinSSquared
  simp only [pow_two]

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

/-! ## Total-spin SU(2) cyclic commutators in named form -/

/-- `[Ŝ_tot^{(1)}, Ŝ_tot^{(2)}] = i · Ŝ_tot^{(3)}` (named-operator form). -/
theorem totalSpinSOp1_commutator_totalSpinSOp2_named :
    (totalSpinSOp1 Λ N * totalSpinSOp2 Λ N
        - totalSpinSOp2 Λ N * totalSpinSOp1 Λ N : ManyBodyOpS Λ N) =
      Complex.I • totalSpinSOp3 Λ N := by
  unfold totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  exact totalSpinSOp1_commutator_totalSpinSOp2 (Λ := Λ) N

/-- `[Ŝ_tot^{(2)}, Ŝ_tot^{(3)}] = i · Ŝ_tot^{(1)}` (named-operator form). -/
theorem totalSpinSOp2_commutator_totalSpinSOp3_named :
    (totalSpinSOp2 Λ N * totalSpinSOp3 Λ N
        - totalSpinSOp3 Λ N * totalSpinSOp2 Λ N : ManyBodyOpS Λ N) =
      Complex.I • totalSpinSOp1 Λ N := by
  unfold totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  exact totalSpinSOp2_commutator_totalSpinSOp3 (Λ := Λ) N

/-- `[Ŝ_tot^{(3)}, Ŝ_tot^{(1)}] = i · Ŝ_tot^{(2)}` (named-operator form). -/
theorem totalSpinSOp3_commutator_totalSpinSOp1_named :
    (totalSpinSOp3 Λ N * totalSpinSOp1 Λ N
        - totalSpinSOp1 Λ N * totalSpinSOp3 Λ N : ManyBodyOpS Λ N) =
      Complex.I • totalSpinSOp2 Λ N := by
  unfold totalSpinSOp1 totalSpinSOp2 totalSpinSOp3
  exact totalSpinSOp3_commutator_totalSpinSOp1 (Λ := Λ) N

end LatticeSystem.Quantum
