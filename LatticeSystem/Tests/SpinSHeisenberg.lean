import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Test coverage for the spin-`S` Heisenberg Hamiltonian
(Tasaki §2.5 Phase B-β β-3h)
-/

namespace LatticeSystem.Tests.SpinSHeisenberg

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Hermiticity for real coupling. -/
example {J : Λ → Λ → ℂ} (hreal : ∀ x y, star (J x y) = J x y) (N : ℕ) :
    (heisenbergHamiltonianS (Λ := Λ) J N).IsHermitian :=
  heisenbergHamiltonianS_isHermitian_of_real hreal N

end LatticeSystem.Tests.SpinSHeisenberg
