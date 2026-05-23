import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence

/-!
# Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link

This module contains the predecessor sector-existence chain link with the
raised predicted-Casimir variant, split as a stable suffix from
`Theorem23SectorExistence.lean`. The parent sector-existence module keeps
the Theorem 2.3 statement, the base per-sector existence step, and the
successor sector-existence chain links with the lowered- and successor-
predicted-Casimir variants. Splitting this raising-direction companion out
lets the parent elaborate without the predecessor variant.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir**: choose the sector-`M+1` Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir predecessor package.

This is the raising-direction companion to
`tasaki23_successor_sector_existence_with_lowered_predictedCasimir`. -/
theorem tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
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
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M + 1) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_predecessor_common_energy_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

end LatticeSystem.Quantum
