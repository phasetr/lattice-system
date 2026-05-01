import LatticeSystem.Quantum.SpinS.SpanningTheorem

/-!
# Test coverage for the spin-`S` spanning theorem
(Tasaki §2.1 P1d''' β-32)
-/

namespace LatticeSystem.Tests.SpinSSpanningTheorem

open LatticeSystem.Quantum

/-- Every matrix is in the adjoin of the spin operators. -/
example (N : ℕ) (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    M ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  matrix_mem_adjoin N M

/-- The adjoin of the spin operators is the whole matrix algebra. -/
example (N : ℕ) :
    Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) = ⊤ :=
  spinS_adjoin_eq_top N

end LatticeSystem.Tests.SpinSSpanningTheorem
