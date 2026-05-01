import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Test coverage for spin-`S` total spin squared
(Tasaki §2.5 Phase B-β β-3p)
-/

namespace LatticeSystem.Tests.SpinSTotalSquared

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `(Ŝ_tot)²` is Hermitian. -/
example (N : ℕ) : (totalSpinSSquared Λ N).IsHermitian :=
  totalSpinSSquared_isHermitian Λ N

end LatticeSystem.Tests.SpinSTotalSquared
