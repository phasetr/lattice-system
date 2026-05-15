import LatticeSystem.Quantum.SpinS.JointCasimirEqTotalSpinSSquaredEigenspaceSaturated

/-!
# Complement saturated: joint Casimir eigenspace = `(Ŝ_tot)²` eigenspace at max Casimir

PR #2929 (`JointCasimirEqTotalSpinSSquaredEigenspaceSaturated.lean`)
gave `jointSublatticeCasimirEigenspace A N
   = totalSpinSSquaredEigenspace (saturated ferromagnet eigenvalue)`
at `|¬A| = 0`.

The complement mirror at `|A| = 0`:

  `jointSublatticeCasimirEigenspace (fun x => ! A x) N
     = totalSpinSSquaredEigenspace (saturated ferromagnet eigenvalue)`

since `|¬¬A| = |A| = 0` reduces to the original case applied to `¬A`.

The joint sublattice-Casimir eigenspace of the **complement** sublattice
function at complement-saturated is also identical to the maximum-Casimir
`(Ŝ_tot)²` eigenspace — fully-polarised ferromagnetic SU(2) multiplet.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Complement saturated: joint Casimir eigenspace = (Ŝ_tot)² eigenspace
at max Casimir** at `|A| = 0`. Mirror of PR #2929. -/
theorem jointSublatticeCasimirEigenspace_complement_eq_totalSpinSSquaredEigenspace_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool) {N : ℕ}
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    jointSublatticeCasimirEigenspace (Λ := Λ) (fun x => ! A x) N =
      Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS Λ N) := by
  apply jointSublatticeCasimirEigenspace_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
    (fun x => ! A x)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
