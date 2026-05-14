import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqCasimirEigenspaceSaturated

/-!
# Predicted GS at opposite saturated case = `(Ŝ_tot)²` eigenspace

Mirror of PR #2802 for the orientation `|A| = 0`. Applying PR #2802
to the flipped sublattice `¬A` (with `|¬¬A| = 0` reducing to
`|A| = 0` via filter congruence) gives:

  `bipartiteToyGroundStateSubspacePredicted (¬A) N
     = Module.End.eigenspace (Ŝ_tot)².mulVecLin
         (saturatedFerromagnetCasimirEigenvalueS Λ N)`

when `|A| = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS at opposite saturated case = `(Ŝ_tot)²`
eigenspace**: when `|A| = 0`,
`bipartiteToyGroundStateSubspacePredicted (¬A) N =
Module.End.eigenspace (Ŝ_tot)².mulVecLin
(saturatedFerromagnetCasimirEigenvalueS Λ N)`. Mirror of PR #2802
via orientation flip. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_eq_totalSpinSSquaredEigenspace_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N =
      Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS Λ N) := by
  apply bipartiteToyGroundStateSubspacePredicted_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
