import LatticeSystem.Quantum.SpinS.Theorem23

/-!
# Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor steps

This module contains the adjacent common-energy predecessor steps (the
raising-direction companions: site-sum and Casimir-non-kernel-value variants),
split as a stable suffix from `Theorem23.lean`. The parent module keeps the
adjacent common-energy successor steps; the predecessor steps here are
independent of the successor steps and reuse the same upstream sector / ladder
API.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step**:
inside the admissible sector interval, a source-sector
Marshall-positive eigenvector in sector `M + 1`, together with the
raised site-sum positivity input, produces a Marshall-positive
eigenvector in the predecessor sector `M` at the same eigenvalue.

This is the raising-direction interval wrapper corresponding to
`tasaki23_successor_sector_common_energy_of_site_sum_pos`. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
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
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
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
  have hpred_mem_raw :
      (M + 1) - 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem A N hMlt hM
  have hpred_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa using hpred_mem_raw
  obtain ⟨hraised_ne, μ_pred, v_pred, hμ_pred_lt, hv_pred_pos,
      hmul_pred, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_raising_identifies_adjacent_sector_energy_of_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ hraised_site_sum_pos
  subst μ_pred
  exact ⟨hpred_mem, hμ_lt, hv_pos, hΦ, hraised_ne, v_pred,
    hμ_pred_lt, hv_pred_pos, hmul_pred, r, hr_pos, hrel⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step
from Casimir non-vanishing**: inside the admissible sector interval, a
Marshall-positive source-sector Casimir eigenvector whose Casimir value
is not the raising endpoint value has a non-zero raised image, and a
site-sum positivity proof identifies the predecessor-sector ground-state
energy with the source energy.

This is the raising-direction interval wrapper corresponding to
`tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
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
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
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
  have hpred_mem_raw :
      (M + 1) - 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem A N hMlt hM
  have hpred_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa using hpred_mem_raw
  obtain ⟨hraised_ne, μ_pred, v_pred, hμ_pred_lt, hv_pred_pos,
      hmul_pred, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_raising_identifies_adjacent_sector_energy_with_casimir_nonzero
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ_cas hγ_ne hv_pos hΦ
      (tasaki23_raised_marshall_pos_of_site_sum_pos A
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        hraised_site_sum_pos)
  subst μ_pred
  exact ⟨hpred_mem, hμ_lt, hv_pos, hΦ, hraised_ne, v_pred,
    hμ_pred_lt, hv_pred_pos, hmul_pred, r, hr_pos, hrel⟩

end LatticeSystem.Quantum
