/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Test coverage for sublattice Casimir eigenvalues on the Néel state
-/

namespace LatticeSystem.Tests.MarshallLiebMattisSublatticeCasimirNeel

open LatticeSystem.Quantum

/-- `(Ŝ_A)² · |Φ_Néel(A)⟩ = (|A|·(|A|+2)/4) · |Φ_Néel(A)⟩`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Fin 2 => A x = true)).card + 2) / 4) •
        neelStateOf A :=
  sublatticeSpinHalfSquared_mulVec_neelStateOf A

/-- `(Ŝ_¬A)² · |Φ_Néel(A)⟩ = (|¬A|·(|¬A|+2)/4) · |Φ_Néel(A)⟩`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinHalfSquared (fun x => ! A x)).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Fin 2 => (! A x) = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Fin 2 => (! A x) = true)).card + 2) / 4) •
        neelStateOf A :=
  sublatticeSpinHalfSquared_complement_mulVec_neelStateOf A

end LatticeSystem.Tests.MarshallLiebMattisSublatticeCasimirNeel
