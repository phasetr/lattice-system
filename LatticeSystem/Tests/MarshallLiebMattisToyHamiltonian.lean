/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian

/-!
# Test coverage for the MLM toy Hamiltonian
-/

namespace LatticeSystem.Tests.MarshallLiebMattisToyHamiltonian

open LatticeSystem.Quantum

/-- The toy Hamiltonian is Hermitian. -/
example (A : Fin 2 → Bool) :
    (heisenbergToyHamiltonian (Λ := Fin 2) A).IsHermitian :=
  heisenbergToyHamiltonian_isHermitian A

/-- Bipartite coupling is symmetric. -/
example (A : Fin 2 → Bool) (x y : Fin 2) :
    bipartiteCoupling A x y = bipartiteCoupling A y x :=
  bipartiteCoupling_symm A x y

/-- Bipartite coupling vanishes on intra-sublattice pairs. -/
example (A : Fin 2 → Bool) {x y : Fin 2} (h : A x = A y) :
    bipartiteCoupling A x y = 0 :=
  bipartiteCoupling_eq_zero_of_same_sublattice A h

/-- Bipartite coupling is positive on inter-sublattice pairs. -/
example (A : Fin 2 → Bool) {x y : Fin 2} (h : A x ≠ A y) :
    0 < (bipartiteCoupling A x y).re :=
  bipartiteCoupling_pos_of_diff_sublattice A h

end LatticeSystem.Tests.MarshallLiebMattisToyHamiltonian
