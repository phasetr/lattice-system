import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankEqSaturated
import LatticeSystem.Quantum.SpinS.SaturatedFMJointLePredictedGS

/-!
# Equality of predicted GS subspace and saturated FM joint at `J = 0`
(saturated edge case)

PR #2786 established `saturatedFerromagnetJointEigenspace J N ⊆
bipartiteToyGroundStateSubspacePredicted A N` for any `J` at the
saturated edge case `|¬A| = 0`. PR #2792 established the reverse
inclusion at `J = 0` specifically.

Combining gives the **submodule equality** at the saturated case
with `J = 0`:

  `bipartiteToyGroundStateSubspacePredicted A N
     = saturatedFerromagnetJointEigenspace 0 N`.

This identifies the predicted GS subspace exactly with the §2.4
saturated-ferromagnet ground-state subspace (specialised to
`J = 0`, where `Ĥ_J = 0` makes the H-eigenspace component
trivially the full multi-site space).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS = saturated FM joint at J = 0** in the saturated
edge case `|¬A| = 0`:
`bipartiteToyGroundStateSubspacePredicted A N =
saturatedFerromagnetJointEigenspace 0 N`. -/
theorem bipartiteToyGroundStateSubspacePredicted_eq_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N =
      saturatedFerromagnetJointEigenspace (V := Λ) (0 : Λ → Λ → ℂ) N := by
  apply le_antisymm
  · exact bipartiteToyGroundStateSubspacePredicted_le_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
      (N := N) A h
  · exact saturatedFerromagnetJointEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
      (N := N) A 0 h

end LatticeSystem.Quantum
