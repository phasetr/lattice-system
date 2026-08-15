import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelCore

/-!
# Test coverage for the spin-`S` sublattice Casimir eigenvalues on the Néel state
(Tasaki §2.5 eqs. (2.5.2)–(2.5.11))
-/

namespace LatticeSystem.Tests.SpinSSublatticeCasimirNeel

open LatticeSystem.Quantum

/-- `(Ŝ_A)² · |Φ_Néel(A, N)⟩ = ((|A|·N/2)·(|A|·N/2 + 1)) · |Φ_Néel(A, N)⟩`:
the Néel state is an eigenvector of the `A`-sublattice Casimir at the
maximum-spin eigenvalue. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N A).mulVec (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        neelStateOfS A N :=
  sublatticeSpinSquaredS_mulVec_neelStateOfS A N

/-- `(Ŝ_¬A)² · |Φ_Néel(A, N)⟩ = ((|¬A|·N/2)·(|¬A|·N/2 + 1)) · |Φ_Néel(A, N)⟩`:
the same state is simultaneously an eigenvector of the complementary
sublattice Casimir at its maximum-spin eigenvalue. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Fin 2 => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Fin 2 => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        neelStateOfS A N :=
  sublatticeSpinSquaredS_complement_mulVec_neelStateOfS A N

end LatticeSystem.Tests.SpinSSublatticeCasimirNeel
