import LatticeSystem.Quantum.SpinS.PredictedGSEqJointCasimirEigenspaceSaturated
import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqCasimirEigenspaceSaturated

/-!
# Joint Casimir eigenspace = `(Ŝ_tot)²` eigenspace at saturated

PR #2925 gave `bipartiteToyGroundStateSubspacePredicted A N
   = jointSublatticeCasimirEigenspace A N` at `|¬A| = 0`.

The existing PR
`bipartiteToyGroundStateSubspacePredicted_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero`
gives `predicted GS = (Ŝ_tot)² eigenspace at max Casimir` at
saturated.

Composing:

  `jointSublatticeCasimirEigenspace A N
     = Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
         (saturatedFerromagnetCasimirEigenvalueS Λ N)`

at `|¬A| = 0`. The joint sublattice-Casimir eigenspace at saturated
is **identical** to the maximum-Casimir `(Ŝ_tot)²` eigenspace —
the fully-polarised ferromagnetic SU(2) multiplet.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Joint Casimir eigenspace = (Ŝ_tot)² eigenspace at max
Casimir** at saturated `|¬A| = 0`. -/
theorem jointSublatticeCasimirEigenspace_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool) {N : ℕ}
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    jointSublatticeCasimirEigenspace (Λ := Λ) A N =
      Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS Λ N) := by
  rw [← bipartiteToyGroundStateSubspacePredicted_eq_joint_eigenspace_of_cardNotA_zero
        A N h]
  exact bipartiteToyGroundStateSubspacePredicted_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
    A h

end LatticeSystem.Quantum
