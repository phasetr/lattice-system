import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Non-emptiness of the predicted toy-Hamiltonian ground-state
subspace in the saturated edge case

For the saturated bipartite case `|¬A| = 0` (all sites in `A`,
no second sublattice), the toy Hamiltonian `Ĥ_toy_S = 2 Ŝ_A · Ŝ_¬A`
reduces to the zero operator (empty cross-sum). The predicted
ground-state subspace `bipartiteToyGroundStateSubspacePredicted A N`
(PR #2778) is the joint eigenspace at the three target Casimir
eigenvalues, which for `|¬A| = 0` simplify to:

  * `(Ŝ_tot)²` eigenvalue `s_A(s_A + 1) = |A|·N/2·(|A|·N/2+1)`,
  * `(Ŝ_A)²` eigenvalue same `s_A(s_A + 1)`,
  * `(Ŝ_{¬A})²` eigenvalue `0` (degenerate empty sublattice).

The all-up state `|σ_⊤⟩` is a simultaneous eigenvector at exactly
these three values:

  * via `totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue`
    (PR #878), `(Ŝ_tot)² · |σ_⊤⟩ = m_max(m_max+1) · |σ_⊤⟩` with
    `m_max = |V|·N/2 = |A|·N/2 = s_A` (since `|¬A| = 0` forces
    `|V| = |A|`).
  * via `sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero`
    (PR #1067), `(Ŝ_A)² · |σ_⊤⟩ = s_A(s_A+1) · |σ_⊤⟩`.
  * via the same lemma applied to `¬A` (with `|¬A| = 0`),
    `(Ŝ_¬A)² · |σ_⊤⟩ = 0 · |σ_⊤⟩ = 0`.

This packages the non-emptiness `|σ_⊤⟩ ∈
bipartiteToyGroundStateSubspacePredicted A N` for the saturated
edge case, the first concrete realisation of the
PR #2778 prediction.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`|σ_⊤⟩` ∈ predicted GS subspace in the saturated case**:
for `[Nonempty Λ]` and `|¬A| = 0`, the all-up state belongs to the
predicted ground-state subspace of the toy Hamiltonian. -/
theorem allAlignedStateS_zero_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (allAlignedStateS Λ N (0 : Fin (N + 1)) : (Λ → Fin (N + 1)) → ℂ) ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  -- |V| = |A| + |¬A| = |A| + 0 = |A|, so s_A = |V|·N/2 = m_max.
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
  -- Show membership in the three eigenspaces.
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- (Ŝ_tot)² · |σ_⊤⟩ = ((|A| - 0) · (|A| - 0 + 1)) • |σ_⊤⟩.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    rw [totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue]
    -- m_max(m_max+1) = (|V|·N/2)·(|V|·N/2 + 1) = s_A·(s_A + 1) since |V| = |A|.
    congr 1
    rw [hcardA, h]
    push_cast
    ring
  · -- (Ŝ_A)² · |σ_⊤⟩ = (s_A · (s_A + 1)) • |σ_⊤⟩.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    exact sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero (Λ := Λ) N A
  · -- (Ŝ_¬A)² · |σ_⊤⟩ = 0 • |σ_⊤⟩ since |¬A| = 0 gives s_B = 0.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    exact sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero
      (Λ := Λ) N (fun x => ! A x)

end LatticeSystem.Quantum
