import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundPredecessorRaising

/-!
# Tasaki §2.5 Theorem 2.3 predecessor-difference outside-ground boundary

This module contains the predecessor-difference and outside-sector final
boundary tail for the Tasaki §2.5 Theorem 2.3 proof chain. It imports the
raising-source predecessor final-wrapper suffix so downstream files can depend
directly on the final predecessor-difference API without elaborating the
earlier predecessor source-weight wrappers in the same file.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor
raising-source positive differences**: this threads the real predecessor
source-weight data into a callback stated as positivity of the off-`A`
minus on-`A` predecessor raising-source difference.

The wrapper converts the difference-form callback to the strict
raising-source dominance callback by
`tasaki23_raising_predecessor_source_sum_lt_callback_of_offA_sub_onA_pos`
and then reuses the preceding final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
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
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag
        exact
          tasaki23_raising_predecessor_source_sum_lt_callback_of_offA_sub_onA_pos
            (V := V) (N := N) A v
            (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag))
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive
differences through lowered site sums**: this routes the fully threaded
predecessor-difference callback through the lowered site-sum successor
chain, rather than converting it first to the raising-source dominance
final wrapper.

The wrapper uses
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`
to propagate the common energy and predicted-GS membership, then applies
the usual common-energy and sector-minimality final packaging. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
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
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
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
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive
differences and outside-interval real-sector minimality**: this refines the
direct lowered-site-sum wrapper by discharging the real-sector spectral
minimality callback on the admissible Theorem 2.3 interval from the common
Marshall-positive energy chain itself.

The remaining real-sector lower-bound hypothesis only has to handle
sectors outside `tasaki23GroundStateSectors`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_real_sector_min :
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
          M ∉ tasaki23GroundStateSectors (V := V) A N →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (fun M => by
            by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
            · exact
                tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
                  A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
                  hcommon M hM
            · exact houtside_real_sector_min hcommon M hM))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive
differences and outside-sector ground energies**: this replaces the
outside-real-sector minimality callback in the predecessor-difference
lowered-site-sum boundary by lower bounds only for the Theorem 2.2
Marshall-positive ground-state representatives in sectors outside
`tasaki23GroundStateSectors`.

The admissible interval is still supplied by the predecessor-difference
energy chain.  Outside the interval, the Perron--Frobenius sector bridge
turns the ground-representative lower bound into the full real-sector
minimality callback consumed by the preceding final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_real_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      (fun hcommon =>
        tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate
          (houtside_ground_energy_lower hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final predecessor-difference boundary from
outside-sector ground energies**: this names the final API obtained from
the lowered-site-sum route.  The remaining inputs are exactly the
left-endpoint predicted-GS callback, the local predecessor-difference
callback, and outside-sector lower bounds for the Marshall-positive
Theorem 2.2 ground-state representatives.

The proof content is supplied by
`tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_sector_ground_energy_lower_bound`;
this alias keeps the public boundary independent of the technical
site-sum route used internally. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c


end LatticeSystem.Quantum
