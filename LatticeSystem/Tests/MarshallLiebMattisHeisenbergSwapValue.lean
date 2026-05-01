/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.HeisenbergSwapValue

/-!
# Test coverage for Heisenberg matrix entry on swap configurations
-/

namespace LatticeSystem.Tests.MarshallLiebMattisHeisenbergSwapValue

open LatticeSystem.Quantum

/-- The Heisenberg matrix entry value on swap-related configurations
on `Fin 2`. -/
example (J : Fin 2 → Fin 2 → ℂ) {σ : Fin 2 → Fin 2} (h : σ 0 ≠ σ 1) :
    (heisenbergHamiltonian J) σ (basisSwap σ 0 1) =
      (J 0 1 + J 1 0) / 2 :=
  heisenbergHamiltonian_apply_basisSwap J (by decide : (0 : Fin 2) ≠ 1) h

end LatticeSystem.Tests.MarshallLiebMattisHeisenbergSwapValue
