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

end LatticeSystem.Tests.MarshallLiebMattisToyHamiltonianCasimir
