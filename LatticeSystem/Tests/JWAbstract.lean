/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JWAbstract

/-!
# Test coverage for abstract Jordan-Wigner

Regression tests for the JW abstraction (PRs #197-#201).
-/

namespace LatticeSystem.Tests.JWAbstract

open LatticeSystem.Fermion LatticeSystem.Quantum Matrix

/-! ## jwStringAbstract-Fin bridge (rfl) -/

example (N : ℕ) (i : Fin (N + 1)) :
    jwStringAbstract i = jwString N i := rfl

example (N : ℕ) (i : Fin (N + 1)) :
    fermionAnnihilationAbstract i = fermionMultiAnnihilation N i := rfl

example (N : ℕ) (i : Fin (N + 1)) :
    fermionCreationAbstract i = fermionMultiCreation N i := rfl

example (N : ℕ) (i : Fin (N + 1)) :
    fermionNumberAbstract i = fermionMultiNumber N i := rfl

/-! ## Basic theorems in the abstract framework -/

example (i : Fin 3) : (jwStringAbstract i).IsHermitian :=
  jwStringAbstract_isHermitian i

example (i : Fin 3) : jwStringAbstract i * jwStringAbstract i = 1 :=
  jwStringAbstract_sq i

example (i : Fin 3) :
    (fermionAnnihilationAbstract i)ᴴ = fermionCreationAbstract i :=
  fermionAnnihilationAbstract_conjTranspose i

example (i : Fin 3) :
    fermionAnnihilationAbstract i * fermionAnnihilationAbstract i = 0 :=
  fermionAnnihilationAbstract_sq i

example (i : Fin 3) :
    fermionCreationAbstract i * fermionCreationAbstract i = 0 :=
  fermionCreationAbstract_sq i

example (i : Fin 3) :
    fermionAnnihilationAbstract i * fermionCreationAbstract i
      + fermionCreationAbstract i * fermionAnnihilationAbstract i = 1 :=
  fermionMultiAnticommAbstract_self i

example (i : Fin 3) :
    fermionNumberAbstract i * fermionNumberAbstract i
      = fermionNumberAbstract i :=
  fermionNumberAbstract_sq i

end LatticeSystem.Tests.JWAbstract
