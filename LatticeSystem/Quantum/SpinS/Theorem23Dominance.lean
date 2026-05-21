import LatticeSystem.Quantum.SpinS.Theorem23

/-!
# Tasaki §2.5 Theorem 2.3 dominance common-energy API

This module contains the dominance-form adjacent common-energy wrappers
split from `Theorem23.lean`. The base module keeps the site-sum and
predicted-Casimir common-energy links, while this module converts the
lowered/raised off-`A` dominance hypotheses into those base links.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
lowered dominance**: inside the admissible sector interval, the pointwise
dominance of the off-`A` lowered signed sum over the negative on-`A`
signed sum supplies the strict site-sum positivity input and hence
produces the successor-sector common-energy conclusion.

This is the dominance-form wrapper around
`tasaki23_successor_sector_common_energy_of_site_sum_pos`.  The
substantive remaining proof obligation is the dominance hypothesis
itself. -/
theorem tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact tasaki23_successor_sector_common_energy_of_site_sum_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
        A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step from
raised dominance**: inside the admissible sector interval, the pointwise
dominance of the off-`A` raised signed sum over the negative on-`A`
signed sum supplies the strict site-sum positivity input and hence
produces the predecessor-sector common-energy conclusion.

This is the raising-direction dominance-form wrapper around
`tasaki23_predecessor_sector_common_energy_of_site_sum_pos`. The
substantive remaining proof obligation is the dominance hypothesis
itself. -/
theorem tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA
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
  exact tasaki23_predecessor_sector_common_energy_of_site_sum_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
    (fun τ =>
      tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
        A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
from lowered dominance**: the lowered dominance hypothesis supplies the
strict site-sum positivity input for the predicted-Casimir successor
common-energy wrapper.

This is the predicted-Casimir analogue of
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA`; the
substantive dominance estimate remains an explicit hypothesis. -/
theorem
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (fun τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
with successor Casimir**: the lowered dominance common-energy wrapper also
transfers the predicted total-Casimir identity to the successor-sector
Marshall-positive representative.

This is the source-vector form of the interval-threading step: once the
source sector carries the predicted Casimir, the adjacent successor returned
by Theorem 2.2 uniqueness carries it as well, so later interval induction does
not need a fresh source-Casimir callback at the successor sector. -/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas hdominates
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hcas_lowered :
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) :=
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
      A N hΦ_cas
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
      ⟨r, hr_pos, hrel⟩⟩⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
with successor Casimir from lowered site-sum positivity**: the direct
lowered site-sum positivity common-energy wrapper also transfers the
predicted total-Casimir identity to the successor-sector Marshall-positive
representative.

This is the site-sum form of
`tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA`.
-/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_site_sum_pos
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      hlowered_site_sum_pos
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hcas_lowered :
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) :=
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
      A N hΦ_cas
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
      ⟨r, hr_pos, hrel⟩⟩⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir predecessor step
from raised dominance**: the raised dominance hypothesis supplies the
strict site-sum positivity input for the predicted-Casimir predecessor
common-energy wrapper.

This is the raising-direction companion to
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue`.
-/
theorem
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
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
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
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
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
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
    tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (fun τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hdominates τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS successor step from
lowered dominance**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the source-sector vector in the predicted toy
ground-state subspace supplies the predicted-Casimir hypothesis needed
by the lowered dominance common-energy wrapper.

The dominance estimate remains explicit; this theorem only replaces the
source total-Casimir input by predicted-GS membership. -/
theorem
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hdominates

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS successor step from
lowered site-sum positivity**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the source-sector vector in the predicted toy ground-state
subspace supplies the predicted-Casimir hypothesis, while the direct
lowered site-sum positivity hypothesis supplies Marshall positivity of
the lowered vector.

This is the site-sum analogue of
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hlowered_site_sum_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent successor step with successor
predicted-GS membership from lowered site-sum positivity**: if the source
representative lies in the predicted toy ground-state subspace, then the
successor representative produced by the lowered adjacent-sector step
lies in the same predicted subspace.

The proof uses predicted-GS invariance under `Ŝ^-_tot` and then cancels
the positive real scalar relating the lowered image to the successor
Marshall-positive representative. -/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedGS_of_site_sum_pos
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hM hMlt hμ_lt hv_pos hΦ hΦ_pred
      hlowered_site_sum_pos
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hlowered_ne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hlowered_pred :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
      A N hΦ_pred
  have hsucc_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    tasaki23_mem_bipartiteToyGroundStateSubspacePredicted_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hlowered_pred
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hlowered_ne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred,
    r, hr_pos, hrel⟩

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
