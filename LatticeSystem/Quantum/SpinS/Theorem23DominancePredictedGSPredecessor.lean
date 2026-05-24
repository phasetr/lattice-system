import LatticeSystem.Quantum.SpinS.Theorem23DominancePredictedGS

/-!
# Tasaki §2.5 Theorem 2.3 adjacent predicted-GS predecessor common-energy step

This module contains the adjacent predicted-GS predecessor common-energy step
(the raising-direction companion), split as a stable suffix from
`Theorem23DominancePredictedGS.lean`. The parent module keeps the three
adjacent predicted-GS successor common-energy steps; the predecessor step here
reuses one of them.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS predecessor step from
raised dominance**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the sector-`M+1` source vector in the predicted toy
ground-state subspace supplies the predicted-Casimir hypothesis needed
by the raised dominance common-energy wrapper.

This is the raising-direction companion to
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hdominates

end LatticeSystem.Quantum
