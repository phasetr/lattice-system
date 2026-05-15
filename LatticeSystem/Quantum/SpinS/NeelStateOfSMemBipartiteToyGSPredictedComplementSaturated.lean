import LatticeSystem.Quantum.SpinS.NeelStateOfSEqAllAlignedStateAtSaturatedComplement
import LatticeSystem.Quantum.SpinS.BipartiteToyGroundStateSaturatedLast

/-!
# Néel ∈ predicted GS subspace (complement orientation) at `|A| = 0`

PR #2915 shows that at `|A| = 0`, `Φ_Néel(A, N) = allAlignedStateS Λ N (Fin.last N)`.
The existing all-down GS witness
(`allAlignedStateS_last_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero`,
PR #2783) gives the membership in the original orientation's
predicted GS subspace at `|¬B| = 0` (with `B = !A`). Applied to
`B := fun x => ! A x` (equivalently the complement orientation),
`|¬B| = |A| = 0` holds, hence

  `Φ_Néel(A, N) ∈ bipartiteToyGroundStateSubspacePredicted (fun x => ! A x) N`
  at `|A| = 0`.

The Néel state IS the predicted GS at the saturated complement
edge — under the complement orientation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Néel ∈ predicted GS at `|A| = 0` (complement orientation)**:
at `|A| = 0`, `Φ_Néel(A, N) ∈
bipartiteToyGroundStateSubspacePredicted (fun x => ! A x) N`. -/
theorem neelStateOfS_mem_bipartiteToyGroundStateSubspacePredicted_complement_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    neelStateOfS A N ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N := by
  rw [neelStateOfS_eq_allAlignedStateS_last_of_cardA_zero A N h]
  -- Apply existing PR with B = (fun x => !A x). Need |¬B| = 0,
  -- which is |A| = 0 (since ¬¬A = A).
  apply allAlignedStateS_last_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
