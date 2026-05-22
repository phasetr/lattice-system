import LatticeSystem.Quantum.SpinS.Theorem23SectorExistenceInterval
import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundPredecessorDifference

/-!
# Tasaki §2.5 Theorem 2.3 final-boundary API

This module contains final-boundary wrappers and public aliases for the
Tasaki §2.5 Theorem 2.3 proof chain.  It is split out from
`Theorem23.lean` so the main theorem-development module does not keep
accumulating API-only tail definitions.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-GS outside-ground
boundary**: this replaces the left-endpoint-only predicted-GS callback
in the public outside-ground predecessor-difference boundary by a uniform
callback over every admissible source sector.  The wrapper feeds the
left endpoint into that uniform callback and leaves the local
predecessor-difference comparison and the outside-sector ground-energy
lower bounds as the remaining inputs.

This is still a boundary for the same Tasaki §2.5 Theorem 2.3 final
statement; it only exposes the predicted-GS input in the canonical
threaded form used by the adjacent-sector chain. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c) :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c hBA hsector_nonempty
    (fun {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ} hμ_lt hv_pos hΦ =>
      hsource_predictedGS
        (M :=
          min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N)
        (by
          simpa using tasaki23GroundStateSectors_left_mem (V := V) A N)
        hμ_lt hv_pos hΦ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 physical-range non-empty outside-ground
boundary**: this replaces the interval-specific non-emptiness callback
for admissible sectors by a canonical non-emptiness callback on the
physical magnetization range `M ≤ |V| * N`.  The admissible-sector range
bound supplies the required `magConfigS` instance for each sector, and
the remaining inputs are the uniform predicted-GS callback, the local
predecessor-difference comparison, and outside-sector ground-energy
lower bounds. -/
abbrev
    tasaki_2_5_theorem_2_3_of_physical_range_nonempty_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hphysical_nonempty :
      ∀ M, M ≤ Fintype.card V * N → Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c) :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c hBA
    (fun M hM =>
      hphysical_nonempty M
        (tasaki23GroundStateSectors_le_card_mul (V := V) A N hM))
    hsource_predictedGS

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged physical non-empty
outside-ground boundary**: the `magConfigS` non-emptiness input is now
derived from the general physical-range sector construction.  The
remaining visible inputs are the uniform predicted-GS callback, the
local predecessor-difference comparison, and outside-sector
ground-energy lower bounds. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c) :=
  tasaki_2_5_theorem_2_3_of_physical_range_nonempty_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c hBA
    (fun _M hM => magConfigS_nonempty_of_le_card_mul (V := V) (N := N) hM)
    hsource_predictedGS

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback final boundary**: this
short alias exposes the discharged outside-ground theorem through the
three named callback propositions that remain on the current proof
boundary: uniform predicted-GS membership, the predecessor-difference
local comparison, and outside-sector ground-energy lower bounds.

The underlying theorem is
`tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound_discharge_nonempty`;
this wrapper keeps the public API stable while the internal site-sum and
outside-sector route continues to be shortened. -/
abbrev tasaki_2_5_theorem_2_3_of_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference houtside_ground_energy_lower

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback final
boundary**: this public boundary avoids the uniform source-sector
predicted-GS callback when only the current outside-ground route is
needed.  It supplies the admissible-sector `magConfigS` non-emptiness
from the physical-range construction and reuses the left-endpoint
outside-ground theorem directly.

The remaining visible inputs are therefore the weaker left-endpoint
predicted-GS callback, the predecessor-difference local comparison, and
outside-sector ground-energy lower bounds. -/
abbrev tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c hBA
    (fun _M hM =>
      magConfigS_nonempty_of_le_card_mul (V := V) (N := N)
        (tasaki23GroundStateSectors_le_card_mul (V := V) A N hM))
    hleft_predictedGS hpredecessor_difference houtside_ground_energy_lower

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS final wrapper from
lowered site-sum positivity**: this replaces the lowered off-`A` dominance
callback by the direct strict site-sum positivity callback needed to prove
Marshall positivity of the lowered vector.

The predicted-GS callback supplies the predicted-Casimir identity at each
source sector, and global minimality remains explicit. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
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
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hglobal_min :
      ∀ {μ μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      hsource_site_sum_pos
  exact tasaki_2_5_theorem_2_3_of_common_energy_chain
    A N c hcommon (hglobal_min hcommon)
    hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-site-sum final wrapper from sector
minimality**: this refines
`tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos`
by replacing the full-space global-minimality callback with sectorwise
minimality. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
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
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos
      A N c hBA hsector_nonempty hsource_pred hsource_site_sum_pos ?_
  intro μ μ' Ψ' hcommon hΨ'_ne hΨ'_eigen
  exact tasaki23_global_minimality_of_sector_minimality N
    (hsector_min hcommon) hΨ'_ne hΨ'_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-site-sum final wrapper from real-sector
minimality**: this combines the direct lowered site-sum interval chain with
the real-form sector minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
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
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
      A N c hBA hsector_nonempty hsource_pred hsource_site_sum_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS site-sum final
wrapper from sector minimality**: this packages the direct lowered
site-sum interval chain into the final theorem while requiring predicted
toy ground-state membership only at the left endpoint.

This is the final-wrapper counterpart of
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos`.
It is the direct site-sum analogue of the lowered-Marshall final wrapper
used later in the chain. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_site_sum_pos
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpred⟩ := hcommon_pred M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N
        (hsector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-site-sum named-callback final
boundary**: this exposes the direct lowered-site-sum route through named
callbacks for source predicted-GS membership, lowered site-sum
positivity, and sectorwise global minimality.

The theorem is a short alias for the direct lowered-site-sum final
wrapper from sector minimality and adds no extra mathematical input. -/
abbrev tasaki_2_5_theorem_2_3_of_lowered_site_sum_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hlowered_site_sum :
      tasaki23LoweredSiteSumCallback (V := V) A J N c)
    (hsector_min :
      tasaki23SectorMinimalityCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
    (V := V) A (J := J) N c hBA hsector_nonempty
    (fun hM _hMlt => hsource_pred hM)
    hlowered_site_sum hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint lowered-site-sum named
boundary**: this is the left-endpoint version of the direct
lowered-site-sum named-callback boundary.

It requires only the left-endpoint predicted-GS callback, the lowered
site-sum positivity callback, and the sector-minimality callback. -/
abbrev tasaki_2_5_theorem_2_3_of_left_endpoint_lowered_site_sum_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hlowered_site_sum :
      tasaki23LoweredSiteSumCallback (V := V) A J N c)
    (hsector_min :
      tasaki23SectorMinimalityCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
    (V := V) A (J := J) N c hBA hsector_nonempty hleft_predictedGS
    hlowered_site_sum hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowered vector Marshall
positivity**: this replaces the direct site-sum positivity callback by
the natural vector-level Marshall positivity of the lowered ladder image
`S^-_{\mathrm{tot}} Ψ`.

The bridge `tasaki23_lowered_site_sum_pos_of_marshall_pos` expands the
lowered ladder vector into the single-site site-sum callback used by the
successor interval chain. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
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
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hglobal_min :
      ∀ {μ μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_marshall_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      hsource_lowered_marshall_pos
  exact tasaki_2_5_theorem_2_3_of_common_energy_chain
    A N c hcommon (hglobal_min hcommon)
    hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-vector-Marshall final wrapper from
sector minimality**: this refines
`tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos`
by replacing the full-space global-minimality callback with sectorwise
minimality. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
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
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos
      A N c hBA hsector_nonempty hsource_pred hsource_lowered_marshall_pos ?_
  intro μ μ' Ψ' hcommon hΨ'_ne hΨ'_eigen
  exact tasaki23_global_minimality_of_sector_minimality N
    (hsector_min hcommon) hΨ'_ne hΨ'_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-vector-Marshall final wrapper from
real-sector minimality**: this combines the vector-level lowered
Marshall-positivity interval chain with the real-form sector minimality
bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
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
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos_of_sector_minimality
      A N c hBA hsector_nonempty hsource_pred hsource_lowered_marshall_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty


end LatticeSystem.Quantum
