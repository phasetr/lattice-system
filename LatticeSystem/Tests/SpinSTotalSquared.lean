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

/-- Casimir invariance, axis 3. -/
example (N : ℕ) :
    totalSpinSSquared Λ N * totalSpinSOp3 Λ N
        - totalSpinSOp3 Λ N * totalSpinSSquared Λ N = 0 :=
  totalSpinSSquared_commutator_totalSpinSOp3 Λ N

/-- Casimir invariance, axis 1. -/
example (N : ℕ) :
    totalSpinSSquared Λ N * totalSpinSOp1 Λ N
        - totalSpinSOp1 Λ N * totalSpinSSquared Λ N = 0 :=
  totalSpinSSquared_commutator_totalSpinSOp1 Λ N

/-- Casimir invariance, axis 2. -/
example (N : ℕ) :
    totalSpinSSquared Λ N * totalSpinSOp2 Λ N
        - totalSpinSOp2 Λ N * totalSpinSSquared Λ N = 0 :=
  totalSpinSSquared_commutator_totalSpinSOp2 Λ N

/-- Casimir as a sum: `(Ŝ_tot)² = ∑_{x, y} Ŝ_x · Ŝ_y`. -/
example (N : ℕ) :
    (totalSpinSSquared Λ N : ManyBodyOpS Λ N) =
      ∑ x : Λ, ∑ y : Λ, spinSDot x y N :=
  totalSpinSSquared_eq_sum_spinSDot Λ N

end LatticeSystem.Tests.SpinSTotalSquared
