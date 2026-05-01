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

/-- SU(2) invariance, axis 1. -/
example (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp1 Λ N -
        totalSpinSOp1 Λ N * heisenbergHamiltonianS J N = 0 :=
  heisenbergHamiltonianS_commutator_totalSpinSOp1 J N

/-- SU(2) invariance, axis 2. -/
example (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp2 Λ N -
        totalSpinSOp2 Λ N * heisenbergHamiltonianS J N = 0 :=
  heisenbergHamiltonianS_commutator_totalSpinSOp2 J N

/-- SU(2) invariance, axis 3. -/
example (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * heisenbergHamiltonianS J N = 0 :=
  heisenbergHamiltonianS_commutator_totalSpinSOp3 J N

/-- Casimir-level SU(2) invariance: `Commute Ĥ_J (Ŝ_tot)²`. -/
example (J : Λ → Λ → ℂ) (N : ℕ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSSquared Λ N) :=
  heisenbergHamiltonianS_commute_totalSpinSSquared J N

end LatticeSystem.Tests.SpinSHeisenberg
