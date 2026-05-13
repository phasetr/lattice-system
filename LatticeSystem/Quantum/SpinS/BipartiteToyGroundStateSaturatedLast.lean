import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# All-down state in the predicted toy-Hamiltonian GS subspace
(saturated edge case)

Symmetric to PR #2782: the all-down state `|σ_⊥⟩` belongs to
`bipartiteToyGroundStateSubspacePredicted A N` in the saturated
edge case `|¬A| = 0`. Same three eigenvector witnesses but using
the `_last` variants:

  * `(Ŝ_tot)² · |σ_⊥⟩ = s_A(s_A+1) · |σ_⊥⟩`
    (PR #879, with `|V| = |A|`).
  * `(Ŝ_A)² · |σ_⊥⟩ = s_A(s_A+1) · |σ_⊥⟩` (PR's `_last` variant).
  * `(Ŝ_¬A)² · |σ_⊥⟩ = 0 · |σ_⊥⟩` (empty sublattice).

Together with PR #2782, this gives two distinct elements of the
predicted GS subspace at the saturated edge case, confirming the
subspace has dimension ≥ 2 there (in fact `≥ 2 s_A + 1` via
saturated-ferromagnet ladder; full identification is the next
step).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`|σ_⊥⟩` ∈ predicted GS subspace in the saturated case**:
for `[Nonempty Λ]` and `|¬A| = 0`, the all-down state belongs to
`bipartiteToyGroundStateSubspacePredicted A N`. Mirror of PR #2782
using `_last` variants. -/
theorem allAlignedStateS_last_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (allAlignedStateS Λ N (Fin.last N) : (Λ → Fin (N + 1)) → ℂ) ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  -- |V| = |A| + |¬A| = |A| + 0 = |A|.
  have hcardA : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      Fintype.card Λ := by
    have h_sum :
        (Finset.univ.filter (fun x : Λ => A x = true)).card +
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
            Fintype.card Λ := by
      have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
          Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
        congr 1; funext x; rcases A x <;> simp
      rw [hfilter_eq, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun x : Λ => A x = true)
    rw [h] at h_sum
    omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    rw [totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue]
    congr 1
    rw [hcardA, h]
    push_cast
    ring
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    exact sublatticeSpinSquaredS_mulVec_allAlignedStateS_last (Λ := Λ) N A
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    exact sublatticeSpinSquaredS_mulVec_allAlignedStateS_last
      (Λ := Λ) N (fun x => ! A x)

end LatticeSystem.Quantum
