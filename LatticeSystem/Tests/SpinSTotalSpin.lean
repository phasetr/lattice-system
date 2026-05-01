import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Test coverage for the multi-site total spin-`S` operators
(Tasaki §2.5 Phase B-β β-3i)
-/

namespace LatticeSystem.Tests.SpinSTotalSpin

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `Ŝ_tot^(1)` is Hermitian. -/
example (N : ℕ) : (totalSpinSOp1 Λ N).IsHermitian := totalSpinSOp1_isHermitian Λ N

/-- `Ŝ_tot^(2)` is Hermitian. -/
example (N : ℕ) : (totalSpinSOp2 Λ N).IsHermitian := totalSpinSOp2_isHermitian Λ N

/-- `Ŝ_tot^(3)` is Hermitian. -/
example (N : ℕ) : (totalSpinSOp3 Λ N).IsHermitian := totalSpinSOp3_isHermitian Λ N

/-- `Ŝ_tot^+ = Ŝ_tot^(1) + i · Ŝ_tot^(2)`. -/
example (N : ℕ) :
    (totalSpinSOpPlus Λ N : ManyBodyOpS Λ N) =
      totalSpinSOp1 Λ N + Complex.I • totalSpinSOp2 Λ N :=
  totalSpinSOpPlus_eq_add Λ N

/-- `Ŝ_tot^- = Ŝ_tot^(1) − i · Ŝ_tot^(2)`. -/
example (N : ℕ) :
    (totalSpinSOpMinus Λ N : ManyBodyOpS Λ N) =
      totalSpinSOp1 Λ N - Complex.I • totalSpinSOp2 Λ N :=
  totalSpinSOpMinus_eq_sub Λ N

/-- `(Ŝ_tot^+)† = Ŝ_tot^-`. -/
example (N : ℕ) :
    (totalSpinSOpPlus Λ N).conjTranspose = totalSpinSOpMinus Λ N :=
  totalSpinSOpPlus_conjTranspose Λ N

/-- `(Ŝ_tot^-)† = Ŝ_tot^+`. -/
example (N : ℕ) :
    (totalSpinSOpMinus Λ N).conjTranspose = totalSpinSOpPlus Λ N :=
  totalSpinSOpMinus_conjTranspose Λ N

end LatticeSystem.Tests.SpinSTotalSpin
