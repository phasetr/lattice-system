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

end LatticeSystem.Tests.SpinSTotalSpin
