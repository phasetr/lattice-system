import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir

/-!
# Test coverage for the spin-`S` toy Hamiltonian / cross-sublattice Casimir bridge
(Tasaki §2.5 eqs. (2.5.10)–(2.5.11))
-/

namespace LatticeSystem.Tests.SpinSToyHamiltonianCasimir

open LatticeSystem.Quantum

/-- `Ĥ_toy_S = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A`: the bipartite bond sum splits
into the two oriented cross-sublattice contributions. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    heisenbergToyHamiltonianS A N =
      sublatticeSpinSDot N A (fun x => ! A x) +
        sublatticeSpinSDot N (fun x => ! A x) A :=
  heisenbergToyHamiltonianS_eq_sublatticeSpinSDot_sum N A

/-- `Ŝ_A · Ŝ_¬A = Ŝ_¬A · Ŝ_A`: the cross-sublattice dot product is
symmetric across the bipartition. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSDot N A (fun x => ! A x) =
      sublatticeSpinSDot N (fun x => ! A x) A :=
  sublatticeSpinSDot_complement_comm N A

/-- `Ĥ_toy_S = 2 • Ŝ_A · Ŝ_¬A`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    heisenbergToyHamiltonianS A N =
      (2 : ℂ) • sublatticeSpinSDot N A (fun x => ! A x) :=
  heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot N A

/-- Casimir identity: `(Ŝ_tot)² = (Ŝ_A)² + 2 • (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    totalSpinSSquared (Fin 2) N =
      sublatticeSpinSquaredS N A
      + (2 : ℂ) • sublatticeSpinSDot N A (fun x => ! A x)
      + sublatticeSpinSquaredS N (fun x => ! A x) :=
  totalSpinSSquared_eq_sublattice_casimir N A

/-- Tasaki §2.5 (2.5.11) closed form:
`Ĥ_toy_S = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    heisenbergToyHamiltonianS A N =
      totalSpinSSquared (Fin 2) N
        - sublatticeSpinSquaredS N A
        - sublatticeSpinSquaredS N (fun x => ! A x) :=
  heisenbergToyHamiltonianS_eq_casimir_diff N A

/-- The toy Hamiltonian commutes with the total spin Casimir. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (heisenbergToyHamiltonianS A N) (totalSpinSSquared (Fin 2) N) :=
  heisenbergToyHamiltonianS_commute_totalSpinSSquared N A

/-- `Commute Ĥ_toy_S (Ŝ_A)²`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (heisenbergToyHamiltonianS A N) (sublatticeSpinSquaredS N A) :=
  heisenbergToyHamiltonianS_commute_sublatticeSpinSquaredS N A

/-- `Commute Ĥ_toy_S (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (heisenbergToyHamiltonianS A N)
            (sublatticeSpinSquaredS N (fun x => ! A x)) :=
  heisenbergToyHamiltonianS_commute_sublatticeSpinSquaredS_complement N A

/-- The all-up state is an eigenvector of the toy Hamiltonian. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    ∃ c : ℂ, (heisenbergToyHamiltonianS A N).mulVec
        (allAlignedStateS (Fin 2) N (0 : Fin (N + 1))) =
      c • allAlignedStateS (Fin 2) N (0 : Fin (N + 1)) :=
  ⟨_, heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero N A⟩

/-- The all-down state is an eigenvector of the toy Hamiltonian. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    ∃ c : ℂ, (heisenbergToyHamiltonianS A N).mulVec
        (allAlignedStateS (Fin 2) N (Fin.last N)) =
      c • allAlignedStateS (Fin 2) N (Fin.last N) :=
  ⟨_, heisenbergToyHamiltonianS_mulVec_allAlignedStateS_last N A⟩

/-- Simplified eigenvalue on the all-up state:
`Ĥ_toy_S · |σ_⊤⟩ = (|A|·|¬A|·N²/2) · |σ_⊤⟩`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (heisenbergToyHamiltonianS A N).mulVec
        (allAlignedStateS (Fin 2) N (0 : Fin (N + 1))) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Fin 2 => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) •
        allAlignedStateS (Fin 2) N (0 : Fin (N + 1)) :=
  heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero_simplified N A

/-- Simplified eigenvalue on the all-down state:
`Ĥ_toy_S · |σ_⊥⟩ = (|A|·|¬A|·N²/2) · |σ_⊥⟩`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (heisenbergToyHamiltonianS A N).mulVec
        (allAlignedStateS (Fin 2) N (Fin.last N)) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Fin 2 => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) •
        allAlignedStateS (Fin 2) N (Fin.last N) :=
  heisenbergToyHamiltonianS_mulVec_allAlignedStateS_last_simplified N A

end LatticeSystem.Tests.SpinSToyHamiltonianCasimir
