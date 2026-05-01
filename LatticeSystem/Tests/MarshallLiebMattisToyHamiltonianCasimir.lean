/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonianCasimir

/-!
# Test coverage for the toy Hamiltonian / cross-sublattice spin dot bridge
-/

namespace LatticeSystem.Tests.MarshallLiebMattisToyHamiltonianCasimir

open LatticeSystem.Quantum

/-- `Ĥ_toy = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A`. -/
example (A : Fin 2 → Bool) :
    heisenbergToyHamiltonian A =
      sublatticeSpinDot A (fun x => ! A x) +
        sublatticeSpinDot (fun x => ! A x) A :=
  heisenbergToyHamiltonian_eq_sublatticeSpinDot_sum A

/-- `Ŝ_A · Ŝ_¬A = Ŝ_¬A · Ŝ_A`. -/
example (A : Fin 2 → Bool) :
    sublatticeSpinDot A (fun x => ! A x) =
      sublatticeSpinDot (fun x => ! A x) A :=
  sublatticeSpinDot_complement_comm A

/-- `Ĥ_toy = 2 • Ŝ_A · Ŝ_¬A`. -/
example (A : Fin 2 → Bool) :
    heisenbergToyHamiltonian A =
      (2 : ℂ) • sublatticeSpinDot A (fun x => ! A x) :=
  heisenbergToyHamiltonian_eq_two_sublatticeSpinDot A

/-- Casimir identity: `(Ŝ_tot)² = (Ŝ_A)² + 2 • (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) :
    totalSpinHalfSquared (Fin 2) =
      sublatticeSpinHalfSquared A
      + (2 : ℂ) • sublatticeSpinDot A (fun x => ! A x)
      + sublatticeSpinHalfSquared (fun x => ! A x) :=
  totalSpinHalfSquared_eq_sublattice_casimir A

/-- Tasaki §2.5 (2.5.11) closed form: `Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) :
    heisenbergToyHamiltonian A =
      totalSpinHalfSquared (Fin 2)
        - sublatticeSpinHalfSquared A
        - sublatticeSpinHalfSquared (fun x => ! A x) :=
  heisenbergToyHamiltonian_eq_casimir_diff A

/-- The toy Hamiltonian commutes with the total spin Casimir. -/
example (A : Fin 2 → Bool) :
    Commute (heisenbergToyHamiltonian A) (totalSpinHalfSquared (Fin 2)) :=
  heisenbergToyHamiltonian_commute_totalSpinHalfSquared A

end LatticeSystem.Tests.MarshallLiebMattisToyHamiltonianCasimir
