import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceRaisingSiteSum

/-!
# Tasaki §2.5 Theorem 2.3 sector-existence dominance API

This module contains the dominance-form successor and predecessor
sector-existence wrappers split from `Theorem23SectorExistence.lean`. The
base sector-existence module keeps the final theorem proposition, the
per-sector Theorem 2.2 wrapper, and the predicted-Casimir existential
successor/predecessor packages, while this module converts lowered/raised
dominance callbacks into the corresponding site-sum inputs.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir from lowered dominance**: choose the source-sector
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the lowered off-`A` dominance hypothesis into strict
lowered site-sum positivity, then apply the predicted-Casimir successor
package.

The dominance estimate remains an explicit hypothesis; this theorem only
connects that estimate to the sector-existence adjacent-chain wrapper. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
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
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
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
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir from raised dominance**: choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the raised off-`A` dominance hypothesis into strict
raised site-sum positivity, then apply the predicted-Casimir predecessor
package.

This is the raising-direction companion to the lowered dominance wrapper
above. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
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
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
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
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted-GS membership from lowered dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, use
predicted-GS membership to supply the predicted-Casimir input, and
convert the lowered off-`A` dominance hypothesis into the strict
site-sum positivity input.

The membership and dominance estimates remain explicit callbacks for the
chosen source-sector vector. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedGS_of_onA_neg_lt_offA
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
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
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
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted-GS membership from raised dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, use predicted-GS membership to supply the predicted-Casimir
input, and convert the raised off-`A` dominance hypothesis into the
strict site-sum positivity input.

This is the raising-direction companion to the lowered predicted-GS
sector-existence wrapper. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedGS_of_onA_neg_lt_offA
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
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
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
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

end LatticeSystem.Quantum
