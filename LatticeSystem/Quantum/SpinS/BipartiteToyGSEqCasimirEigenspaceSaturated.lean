import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqSaturatedJointZero
import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace

/-!
# Predicted GS subspace at saturated case = `(Ŝ_tot)²` eigenspace
at maximum Casimir eigenvalue

Composition of PR #2796 (`predicted GS = saturatedFerromagnetJointEigenspace 0 N`
at `|¬A| = 0`) and PR #2801 (`saturatedFerromagnetJointEigenspace 0 N =
(Ŝ_tot)² eigenspace at saturatedFerromagnetCasimirEigenvalueS V N`)
yields the cleanest identification of the saturated-case predicted
GS subspace:

  `bipartiteToyGroundStateSubspacePredicted A N
     = Module.End.eigenspace (Ŝ_tot)².mulVecLin
         (saturatedFerromagnetCasimirEigenvalueS Λ N)`

when `|¬A| = 0`.

The saturated-case predicted GS is **just** the maximum-Casimir
`(Ŝ_tot)²`-eigenspace, free from any auxiliary Hamiltonian.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS at saturated case = `(Ŝ_tot)²` eigenspace at
max Casimir**: when `|¬A| = 0`,
`bipartiteToyGroundStateSubspacePredicted A N =
Module.End.eigenspace (Ŝ_tot)².mulVecLin
(saturatedFerromagnetCasimirEigenvalueS Λ N)`. -/
theorem bipartiteToyGroundStateSubspacePredicted_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N =
      Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS Λ N) := by
  rw [bipartiteToyGroundStateSubspacePredicted_eq_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
        A h,
      saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace]

end LatticeSystem.Quantum
