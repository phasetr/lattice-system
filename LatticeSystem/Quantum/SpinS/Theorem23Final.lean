import LatticeSystem.Quantum.SpinS.Theorem23SectorExistenceInterval
import LatticeSystem.Quantum.SpinS.Theorem23OutsideGround
import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundPredecessorDifference

/-!
# Tasaki §2.5 Theorem 2.3 final-boundary API

This module contains final-boundary wrappers and public aliases for the
Tasaki §2.5 Theorem 2.3 proof chain.  It is split out from
`Theorem23.lean` so the main theorem-development module does not keep
accumulating API-only tail definitions. The direct lowered-site-sum
final suffix is split further into `Theorem23FinalLoweredSiteSum.lean`;
the lowered-vector-Marshall final suffix is split further into
`Theorem23FinalLoweredMarshall.lean`.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 source common-energy final boundary with
explicit non-emptiness**: this public boundary routes the source predicted-GS
and predecessor-difference callbacks through the named common-energy chain
before applying the final outside-sector ground-energy theorem, while keeping
the admissible-sector `magConfigS` non-emptiness callback visible.

It is the explicit-nonempty companion to
`tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty`;
the discharged version obtains the same non-emptiness input from the physical
range. -/
theorem
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
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
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_common_energy_chain_of_source_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_predictedGS
      hpredecessor_difference
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hcommon
      (houtside_ground_energy_lower (μ := μ) hcommon)

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
threaded form used by the adjacent-sector chain.

Internally this wrapper now first builds the source common-energy chain and
then invokes the reduced common-energy plus outside-sector final boundary. -/
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
      tasaki23SourcePredictedGSCallback (V := V) A J N c) :
    tasaki23PredecessorDifferenceCallback (V := V) A J N c →
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c →
        tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hpredecessor_difference houtside_ground_energy_lower hJ_real hJ_real'
    hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict h_intermediate hA_nonempty
    hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hBA hsector_nonempty
      hsource_predictedGS hpredecessor_difference houtside_ground_energy_lower
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-GS admissible-reach
boundary**: this replaces the outside-sector ground-energy lower family in
the threaded public predecessor-difference boundary by the ladder-style
admissible-reach callback.

The bridge
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach`
supplies the outside-sector ground-energy lower family, so the visible
remaining inputs are the uniform predicted-GS callback, the local
predecessor-difference comparison, the real-coupling hypotheses, and
admissible reach for outside-sector representatives.

Internally this now feeds the admissible-reach lower family directly into the
source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach :
      tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsector_nonempty
      hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hreach)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 physical-range non-empty outside-ground
boundary**: this replaces the interval-specific non-emptiness callback
for admissible sectors by a canonical non-emptiness callback on the
physical magnetization range `M ≤ |V| * N`.  The admissible-sector range
bound supplies the required `magConfigS` instance for each sector, and
the remaining inputs are the uniform predicted-GS callback, the local
predecessor-difference comparison, and outside-sector ground-energy
lower bounds.

The route now discharges the non-emptiness input and then invokes the explicit
source common-energy final boundary directly. -/
abbrev
    tasaki_2_5_theorem_2_3_of_physical_range_nonempty_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hphysical_nonempty :
      ∀ M, M ≤ Fintype.card V * N → Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c) :
    tasaki23PredecessorDifferenceCallback (V := V) A J N c →
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c →
        tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hpredecessor_difference houtside_ground_energy_lower hJ_real hJ_real'
    hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict h_intermediate hA_nonempty
    hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hBA
      (fun M hM =>
        hphysical_nonempty M
          (tasaki23GroundStateSectors_le_card_mul (V := V) A N hM))
      hsource_predictedGS hpredecessor_difference houtside_ground_energy_lower
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 physical-range non-empty admissible-reach
boundary**: this is the physical-range non-empty version of
`tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach`.

It derives the admissible-sector `magConfigS` non-emptiness callback from
the physical range and supplies outside-sector ground-energy lower bounds
from admissible reach. -/
abbrev
    tasaki_2_5_theorem_2_3_of_physical_range_nonempty_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hphysical_nonempty :
      ∀ M, M ≤ Fintype.card V * N → Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach :
      tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach
    (V := V) A (J := J) N c hBA
    (fun M hM =>
      hphysical_nonempty M
        (tasaki23GroundStateSectors_le_card_mul (V := V) A N hM))
    hsource_predictedGS hpredecessor_difference hJ_real hJ_real' hJ_nn hJ_sym
    hJ_bipartite hc_strict hreach

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 source common-energy final boundary**:
this public boundary routes the source predicted-GS and predecessor-difference
callbacks through the named common-energy chain before applying the final
outside-sector ground-energy theorem.

Unlike `tasaki_2_5_theorem_2_3_of_named_callbacks`, this theorem makes the
reduced proof route explicit: first construct `tasaki23CommonEnergyChain` from
the source predicted-GS callback with admissible-sector non-emptiness discharged,
then feed that common energy to
`tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound`. -/
theorem
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
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
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_common_energy_chain_of_source_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_discharge_nonempty
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsource_predictedGS hpredecessor_difference
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hcommon
      (houtside_ground_energy_lower (μ := μ) hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged physical non-empty
outside-ground boundary**: the `magConfigS` non-emptiness input is now
derived from the general physical-range sector construction.  The
remaining visible inputs are the uniform predicted-GS callback, the
local predecessor-difference comparison, and outside-sector
ground-energy lower bounds.

Internally this now uses the reduced common-energy plus outside-sector route,
so the discharged wrapper shares the same final factorisation as the named
callback boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c) :
    tasaki23PredecessorDifferenceCallback (V := V) A J N c →
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c →
        tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hpredecessor_difference houtside_ground_energy_lower hJ_real hJ_real'
    hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict h_intermediate hA_nonempty
    hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hBA hsource_predictedGS
      hpredecessor_difference houtside_ground_energy_lower
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged non-empty admissible-reach
boundary**: this removes both the explicit physical-range non-emptiness
callback and the outside-sector ground-energy lower-family callback from
the threaded predecessor-difference boundary.

Non-emptiness comes from `magConfigS_nonempty_of_le_card_mul`, while the
outside-sector ground-energy lower family is supplied by the admissible
reach bridge.  Internally this directly invokes the source predicted-GS
common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach :
      tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hreach)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 full-admissible-reach discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
a full-space ladder-reach callback.  The full-space callback is restricted to
the outside-sector lower-family callback by the full-admissible-reach bridge,
then that lower family is fed directly into the common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_full_admissible_reach_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hfull :
      tasaki23OutsideGroundAdmissibleFullReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_full_admissible_reach
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hfull)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 iterated-ladder full-reach discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right non-zeroness callbacks for iterated
total-spin ladder outputs.  The iterated ladder bridge supplies the
outside-sector lower-family callback, and the resulting lower family is fed
directly into the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_iterated_ladder_full_reach_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderFullReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderFullReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_full_reach
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleft hright)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 iterated-ladder Casimir full-reach
discharged boundary**: this version of the discharged final
predecessor-difference boundary accepts left and right Casimir callbacks
which prove non-zeroness for the iterated total-spin ladder outputs.  The
Casimir full-reach bridge supplies the outside-sector lower-family callback
before it is fed directly into the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_iterated_ladder_casimir_full_reach_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_casimir_full_reach
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleft hright)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-Casimir source discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right saturated total-Casimir source callbacks.
Those callbacks feed the saturated-Casimir outside-ground bridge, and the
resulting lower family enters the source common-energy final boundary
directly. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_casimir_sources_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_casimir_sources
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleft hright)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-span source discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right source callbacks in the concrete span of the
saturated ferromagnetic total-spin ladder.  The maximum-Casimir eigenspace
identification is packaged by the saturated-ladder-span outside-ground bridge,
whose lower family is fed directly into the source common-energy final
boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_span_sources_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_span_sources
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleft hright)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-joint source discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
left and right source callbacks in the saturated-ferromagnet joint eigenspace.
The Tasaki §2.4 ladder-span identification converts those source-vector
callbacks through the saturated joint-source outside-ground bridge, whose
lower family is fed directly into the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_sources_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback A J N c)
    (hright :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_sources
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleft hright)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-joint reference discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts sectorwise saturated joint reference callbacks directly.
The reference callbacks first produce the saturated joint source-vector
callbacks by Marshall-positive eigenvalue/eigenvector uniqueness; the resulting
lower family is then passed directly to the source common-energy final
boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_references_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
    hJ_bipartite hc_strict h_intermediate hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated ladder-reference discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts sectorwise saturated ladder-reference callbacks directly.
The ladder references first become saturated joint references through the
Tasaki §2.4 joint-eigenspace/ladder-span equality; the resulting lower family
is then passed directly to the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_references_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
    hJ_bipartite hc_strict h_intermediate hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated ladder-iterate reference discharged
boundary**: this version accepts sectorwise singleton ladder-iterate reference
callbacks directly.  They first become saturated ladder references by the
singleton-span inclusion; the resulting lower family is then passed directly to
the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_references_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
    hJ_bipartite hc_strict h_intermediate hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated eigen-source discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
left and right source callbacks at the saturated Heisenberg eigenvalue plus
the existing saturated-Casimir source callbacks.  These two eigenspace
inputs assemble the outside-sector lower family and feed it directly into the
source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_eigen_sources_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftH :
      tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback A J N c)
    (hrightH :
      tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_eigen_sources
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleftH hrightH hleftCas hrightCas)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated source-energy discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right scalar callbacks identifying each outside
source energy with the saturated-ferromagnet Heisenberg energy, plus the
existing saturated-Casimir source callbacks.  The scalar callbacks supply the
saturated-Heisenberg source equations before the resulting lower family is
fed directly into the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_source_energy_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftEnergy :
      tasaki23OutsideGroundLeftSaturatedEnergySourceCallback A J N c)
    (hrightEnergy :
      tasaki23OutsideGroundRightSaturatedEnergySourceCallback A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_source_energy
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleftEnergy hrightEnergy hleftCas hrightCas)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated joint-source extraction
boundary**: this version accepts the saturated joint source-vector callbacks,
extracts their scalar saturated source-energy and saturated-Casimir
components, and routes through the saturated source-energy final boundary.
This records that the remaining eigenvalue callbacks are consequences of the
joint source-vector API. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_sources_extract_source_eigen_callbacks_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftJoint :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback A J N c)
    (hrightJoint :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_source_energy_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedEnergySourceCallback_of_saturated_joint_source
      A (J := J) N c hleftJoint)
    (tasaki23OutsideGroundRightSaturatedEnergySourceCallback_of_saturated_joint_source
      A (J := J) N c hrightJoint)
    (tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_saturated_joint_source
      A (J := J) N c hleftJoint)
    (tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_saturated_joint_source
      A (J := J) N c hrightJoint)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-joint reference extraction
discharged boundary**: this version combines the reference-vector API with
the source-eigen callback extraction route.  The saturated joint references
first discharge the saturated joint source-vector callbacks, and those source
callbacks then supply the scalar saturated source-energy and saturated-Casimir
inputs used by the existing extracted final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_references_extract_source_eigen_callbacks_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_sources_extract_source_eigen_callbacks_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated ladder-reference extraction
discharged boundary**: this version accepts saturated ladder references and
uses them at the source-eigen callback extraction final boundary.  The ladder
references first become saturated joint references, then the existing
saturated joint-reference extraction boundary supplies the scalar saturated
source-energy and saturated-Casimir callbacks. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_references_extract_source_eigen_callbacks_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_references_extract_source_eigen_callbacks_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    h_intermediate
    (tasaki23OutsideGroundLeftSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated ladder-iterate reference extraction
discharged boundary**: this version accepts singleton ladder-iterate references
at the source-eigen callback extraction final boundary.  The iterate references
first become saturated ladder references, then the existing ladder-reference
extraction boundary supplies the scalar saturated source-energy and
saturated-Casimir callbacks. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_references_extract_source_eigen_callbacks_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_references_extract_source_eigen_callbacks_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 side-admissible-reach discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
separate left and right directional outside-sector reach callbacks.  The side
callbacks feed the side-admissible-reach lower-family bridge before the
resulting lower family is fed directly into the common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_side_admissible_reach_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftAdmissibleReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightAdmissibleReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_side_admissible_reach
        (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
        hc_strict hleft hright)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged boundary from saturated
ladder-iterate successor dominance**: this public discharged final
predecessor-difference boundary replaces the outside-sector ground-energy lower
family by the saturated ladder-iterate successor-dominance route.  The
saturated ferromagnetic energy is supplied as an explicit real scalar for the
outside-ground coefficient callbacks.  Internally this now feeds the resulting
lower family directly into the source common-energy final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_successor_dominance_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_successor_dominance
        (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hμsat hdominates)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged boundary from saturated
ladder-iterate successor dominance with real couplings**: real couplings supply
the saturated-energy real scalar needed internally, so the public discharged
boundary exposes only the successor-dominance input for the saturated ladder
iterates and then enters the source common-energy final boundary directly. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_successor_dominance_of_real_couplings_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_successor_dominance_of_real_couplings
        (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hdominates)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged boundary from saturated
ladder-iterate lowerable attach-sum dominance**: this public discharged final
predecessor-difference boundary replaces the outside-sector ground-energy lower
family by the saturated ladder-iterate explicit lowerable attach-sum dominance
route and then enters the source common-energy final boundary directly. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance
        (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hμsat hdominates)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged boundary from saturated
ladder-iterate lowerable attach-sum dominance with real couplings**: real
couplings supply the saturated-energy real scalar needed internally, so the
public discharged boundary exposes only the explicit lowerable attach-sum
dominance input for the saturated ladder iterates and then enters the source
common-energy final boundary directly. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings
        (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hdominates)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged boundary from saturated
ladder-iterate predecessor differences**: this public discharged final
predecessor-difference boundary replaces the outside-sector ground-energy lower
family by the saturated ladder-iterate predecessor-difference positivity route.
The saturated ferromagnetic energy is still supplied as an explicit real scalar,
matching the lower-family callback used before entering the source common-energy
final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_predecessor_difference_pos_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdiff :
      tasaki23SaturatedLadderIteratePredecessorDifferencePosCallback (V := V) A N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_predecessor_difference_pos
        (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hμsat hdiff)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 discharged boundary from saturated
ladder-iterate predecessor differences with real couplings**: this public
discharged final predecessor-difference boundary replaces the outside-sector
ground-energy lower family by the saturated ladder-iterate predecessor-
difference positivity route.  Real couplings supply the saturated-energy
real scalar needed internally, so no separate `hμsat` input remains before the
source common-energy final boundary is invoked. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings_discharge_nonempty
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdiff :
      tasaki23SaturatedLadderIteratePredecessorDifferencePosCallback (V := V) A N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
    hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
    hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real_final hJ_real'_final hJ_pos_final
      hJ_nn_final hJ_sym_final hJ_bipartite_final hc_strict_final
      h_intermediate_final hBA hsource_predictedGS hpredecessor_difference
      (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings
        (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hdiff)
      hJ_real_final hJ_real'_final hJ_sym_final hJ_nn_final
      hJ_bipartite_final hJ_pos_final hc_strict_final h_intermediate_final
      hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint common-energy final boundary**:
this public boundary is the left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty`.

It builds the named common-energy chain directly from the left-endpoint
predicted-GS callback and the predecessor-difference callback, discharges
admissible-sector non-emptiness from the physical range, and then applies the
same reduced common-energy plus outside-sector theorem. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
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
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA
      (fun _M hM =>
        magConfigS_nonempty_of_le_card_mul (V := V) (N := N)
          (tasaki23GroundStateSectors_le_card_mul (V := V) A N hM))
      hleft_predictedGS hpredecessor_difference
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hcommon
      (houtside_ground_energy_lower (μ := μ) hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback final boundary**: this
short alias exposes the discharged outside-ground theorem through the
three named callback propositions that remain on the current proof
boundary: uniform predicted-GS membership, the predecessor-difference
local comparison, and outside-sector ground-energy lower bounds.

The underlying route now factors through
`tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty`;
this wrapper keeps the public API stable while the internal proof is expressed
through the reduced common-energy plus outside-sector boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_source_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hBA hsource_predictedGS
      hpredecessor_difference houtside_ground_energy_lower hJ_real hJ_real'
      hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict h_intermediate hA_nonempty
      hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated joint
sources**: this public boundary replaces the named outside-sector
lower-family callback by the saturated joint source-vector callbacks.  The
callback-level bridge
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_sources`
supplies the outside family before reusing
`tasaki_2_5_theorem_2_3_of_named_callbacks`. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_joint_sources_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftJoint :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c)
    (hrightJoint :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftJoint hrightJoint)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated joint
references**: this public boundary replaces the saturated joint source-vector
callbacks by the sectorwise saturated joint reference callbacks.  The
source-vector/eigenvalue uniqueness bridge turns those references into
saturated joint source callbacks, and the outside-ground bridge supplies the
named final theorem's lower-family input. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_joint_references_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated ladder
references**: this public boundary replaces saturated joint references by
sectorwise saturated ladder-span references.  The Tasaki §2.4
joint-eigenspace/span identification turns those ladder references into joint
references, and the existing reference route supplies the outside-ground
lower-family input. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_ladder_references_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate references**: the public named final boundary can consume
sectorwise singleton ladder-iterate reference callbacks.  They first become
saturated ladder references, then reuse the ladder-reference outside-ground
route. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_references_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate successor dominance**: the public named final boundary can
consume the filtered successor-dominance input directly as its outside-sector
lower-family source. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_successor_dominance_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_successor_dominance
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hμsat hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate successor dominance with real couplings**: real couplings
discharge the saturated-energy real-scalar input for the successor-dominance
final route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_successor_dominance_of_real_couplings_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_successor_dominance_of_real_couplings
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate lowerable attach-sum dominance**: the public named final
boundary can consume the explicit lowerable attach-sum dominance input directly
as its outside-sector lower-family source. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hμsat hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate lowerable attach-sum dominance with real couplings**: real
couplings discharge the saturated-energy real-scalar input for the lowerable
attach-sum final route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate predecessor differences**: the public named final boundary can
use the saturated ladder-iterate predecessor-difference positivity input
directly as its outside-sector lower-family source.  The wrapper first turns
that local difference form into explicit lowerable attach-sum dominance, then
uses the saturated ladder-iterate coefficient route to discharge the
outside-ground lower-family callback. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_predecessor_difference_pos_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdiff : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                w ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  w ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_predecessor_difference_pos
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hμsat hdiff)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate predecessor differences with real couplings**: real couplings
discharge the saturated-ferromagnet energy realness input, so the public named
boundary only needs the predecessor-difference positivity callback for the
saturated ladder iterates. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdiff :
      tasaki23SaturatedLadderIteratePredecessorDifferencePosCallback (V := V) A N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hdiff)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated Casimir
sources**: the public named final boundary can consume left and right
saturated total-Casimir source callbacks directly.  These callbacks supply
the outside-sector lower-family callback through the saturated-Casimir
outside-ground bridge. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_casimir_sources_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_casimir_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftCas hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-span sources**: source callbacks in the saturated total-spin ladder
span feed the outside-sector lower-family callback through the saturated
ladder-span outside-ground bridge before entering the uniform named final
boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_span_sources_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftSpan :
      tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback (V := V) A J N c)
    (hrightSpan :
      tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_span_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftSpan hrightSpan)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated eigen
sources**: saturated-Heisenberg source callbacks together with
saturated-Casimir source callbacks supply the outside-sector lower-family
callback directly before entering the uniform named final theorem. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_eigen_sources_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftH :
      tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback (V := V) A J N c)
    (hrightH :
      tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback (V := V) A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_eigen_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftH hrightH hleftCas hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated source
energies**: scalar source-energy identifications supply the saturated
Heisenberg source callbacks.  Together with saturated-Casimir source
callbacks, they produce the outside-sector lower-family callback directly for
the uniform named final theorem. -/
abbrev tasaki_2_5_theorem_2_3_of_saturated_source_energy_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftEnergy :
      tasaki23OutsideGroundLeftSaturatedEnergySourceCallback (V := V) A J N c)
    (hrightEnergy :
      tasaki23OutsideGroundRightSaturatedEnergySourceCallback (V := V) A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_source_energy
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftEnergy hrightEnergy hleftCas hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
joint-source extraction**: saturated joint source-vector callbacks already
carry the scalar saturated source-energy and saturated-Casimir source
callbacks.  This uniform boundary records that extraction route before
reusing the saturated source-energy named-callback boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_joint_sources_extract_source_eigen_callbacks_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftJoint :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c)
    (hrightJoint :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_saturated_source_energy_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedEnergySourceCallback_of_saturated_joint_source
      A (J := J) N c hleftJoint)
    (tasaki23OutsideGroundRightSaturatedEnergySourceCallback_of_saturated_joint_source
      A (J := J) N c hrightJoint)
    (tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_saturated_joint_source
      A (J := J) N c hleftJoint)
    (tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_saturated_joint_source
      A (J := J) N c hrightJoint)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
joint-reference extraction**: sectorwise saturated joint references first
produce saturated joint source-vector callbacks by Marshall-positive
eigenvalue/eigenvector uniqueness.  The resulting source callbacks then feed
the uniform saturated source-eigen extraction route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_joint_references_extract_source_eigen_callbacks_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_saturated_joint_sources_extract_source_eigen_callbacks_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-reference extraction**: sectorwise saturated ladder references first
produce saturated joint references through the ladder-span equality.  The
resulting joint references then feed the uniform saturated source-eigen
extraction route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_references_extract_source_eigen_callbacks_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_saturated_joint_references_extract_source_eigen_callbacks_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    h_intermediate
    (tasaki23OutsideGroundLeftSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 named-callback boundary from saturated
ladder-iterate reference extraction**: sectorwise singleton ladder-iterate
references first produce saturated ladder references.  The resulting ladder
references then feed the uniform saturated source-eigen extraction route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_references_extract_source_eigen_callbacks_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_saturated_ladder_references_extract_source_eigen_callbacks_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback final
boundary**: this public boundary avoids the uniform source-sector
predicted-GS callback when only the current outside-ground route is
needed.  It supplies the admissible-sector `magConfigS` non-emptiness
from the physical-range construction and reuses the left-endpoint
outside-ground theorem directly.

The remaining visible inputs are therefore the weaker left-endpoint
predicted-GS callback, the predecessor-difference local comparison, and
outside-sector ground-energy lower bounds.  Internally this boundary now uses
the reduced common-energy plus outside-sector theorem through the explicit
left-endpoint common-energy wrapper. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_common_energy_chain_and_outside_sector_ground_energy_lower_bound_discharge_nonempty
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hBA hleft_predictedGS
      hpredecessor_difference houtside_ground_energy_lower hJ_real hJ_real'
      hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict h_intermediate hA_nonempty
      hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated joint sources**: this is the left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_joint_sources_named_callbacks`.  It keeps
the common-energy input at the weaker left-endpoint predicted-GS callback while
the saturated joint source-vector callbacks supply the outside-sector
lower-family callback. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_joint_sources_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftJoint :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c)
    (hrightJoint :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftJoint hrightJoint)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated joint references**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_joint_references_named_callbacks`.
The weaker left-endpoint predicted-GS input is combined with saturated joint
reference callbacks, which discharge the outside-sector lower-family input
through the source-vector/eigenvalue uniqueness bridge. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_joint_references_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder references**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_references_named_callbacks`.
The ladder-reference inputs are converted to saturated joint references
before the existing reference route supplies the outside-ground lower-family
callback. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_references_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate references**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_references_named_callbacks`.
The singleton ladder-iterate inputs first become saturated ladder references,
then reuse the existing ladder-reference outside-ground route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_references_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_references
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate successor dominance**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_successor_dominance_named_callbacks`.
The weaker left-endpoint predicted-GS input is combined with the filtered
successor-dominance route for the outside-sector lower-family callback. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_successor_dominance_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_successor_dominance
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hμsat hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate successor dominance with real couplings**:
left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_successor_dominance_of_real_couplings_named_callbacks`.
The real-coupling hypothesis supplies the saturated-energy real scalar needed
by the outside-sector successor-dominance route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_successor_dominance_of_real_couplings_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_successor_dominance_of_real_couplings
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate predecessor differences**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_predecessor_difference_pos_named_callbacks`.
The weaker left-endpoint predicted-GS input is combined with the saturated
ladder-iterate predecessor-difference positivity route, which supplies the
outside-sector lower-family callback. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_predecessor_difference_pos_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdiff : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                w ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  w ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_predecessor_difference_pos
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hμsat hdiff)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate predecessor differences with real couplings**:
left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings_named_callbacks`.
The real-coupling hypothesis supplies the saturated-energy real scalar needed
by the outside-sector ladder-iterate coefficient route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdiff :
      tasaki23SaturatedLadderIteratePredecessorDifferencePosCallback (V := V) A N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_predecessor_difference_pos_of_real_couplings
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hdiff)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated Casimir sources**: the left-endpoint final boundary can consume
left and right saturated total-Casimir source callbacks directly.  These
callbacks supply the outside-sector lower-family callback through the
saturated-Casimir outside-ground bridge. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_casimir_sources_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_casimir_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftCas hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-span sources**: the left-endpoint final boundary can consume
left and right source callbacks in the saturated total-spin ladder span.  The
saturated ladder-span outside-ground bridge converts those callbacks directly
to the outside-sector lower-family callback. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_span_sources_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftSpan :
      tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback (V := V) A J N c)
    (hrightSpan :
      tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_span_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftSpan hrightSpan)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated eigen sources**: saturated-Heisenberg source callbacks together
with saturated-Casimir source callbacks supply the outside-sector lower-family
callback directly for the left-endpoint final boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_eigen_sources_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftH :
      tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback (V := V) A J N c)
    (hrightH :
      tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback (V := V) A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_eigen_sources
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftH hrightH hleftCas hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated source energies**: scalar source-energy identifications supply the
saturated-Heisenberg source callbacks.  Together with saturated-Casimir source
callbacks, they produce the outside-sector lower-family callback directly for
the left-endpoint final theorem. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_source_energy_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftEnergy :
      tasaki23OutsideGroundLeftSaturatedEnergySourceCallback (V := V) A J N c)
    (hrightEnergy :
      tasaki23OutsideGroundRightSaturatedEnergySourceCallback (V := V) A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_source_energy
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hleftEnergy hrightEnergy hleftCas hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated joint-source extraction**: saturated joint source-vector callbacks
also discharge the scalar saturated source-energy and saturated-Casimir source
callbacks.  This left-endpoint boundary records that extraction route before
reusing the saturated source-energy named-callback boundary. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_joint_sources_extract_source_eigen_callbacks_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleftJoint :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c)
    (hrightJoint :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_source_energy_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedEnergySourceCallback_of_saturated_joint_source
      A (J := J) N c hleftJoint)
    (tasaki23OutsideGroundRightSaturatedEnergySourceCallback_of_saturated_joint_source
      A (J := J) N c hrightJoint)
    (tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_saturated_joint_source
      A (J := J) N c hleftJoint)
    (tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_saturated_joint_source
      A (J := J) N c hrightJoint)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated joint-reference extraction**: the sectorwise saturated joint
reference callbacks first produce the saturated joint source-vector callbacks
by Marshall-positive eigenvalue/eigenvector uniqueness.  The resulting source
callbacks then discharge the scalar saturated source-energy and
saturated-Casimir source callbacks used by the left-endpoint extraction
route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_joint_references_extract_source_eigen_callbacks_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_joint_sources_extract_source_eigen_callbacks_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-reference extraction**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_references_extract_source_eigen_callbacks_named_callbacks`.
The ladder references first become saturated joint references, then reuse the
left-endpoint saturated joint-reference extraction route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_references_extract_source_eigen_callbacks_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_joint_references_extract_source_eigen_callbacks_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    h_intermediate
    (tasaki23OutsideGroundLeftSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate reference extraction**: left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_references_extract_source_eigen_callbacks_named_callbacks`.
The singleton ladder-iterate references first become saturated ladder
references, then reuse the left-endpoint ladder-reference extraction route. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_references_extract_source_eigen_callbacks_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_references_extract_source_eigen_callbacks_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
    h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate lowerable attach-sum dominance**: left-endpoint
analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_named_callbacks`. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_lowerable_attach_sum_dominance_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hμsat hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint named-callback boundary from
saturated ladder-iterate lowerable attach-sum dominance with real couplings**:
left-endpoint analogue of
`tasaki_2_5_theorem_2_3_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings_named_callbacks`. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings_named_callbacks
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance_of_real_couplings
      (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor-difference named-callback
sector-minimality boundary**: this public boundary replaces the
outside-sector ground-energy lower family in
`tasaki_2_5_theorem_2_3_of_named_callbacks` by the stronger named
sector-minimality callback.

The outside-family input is supplied by
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_sector_minimality`, so
the remaining named hypotheses are source predicted-GS membership, the
predecessor-difference local comparison, and sectorwise minimality. -/
abbrev tasaki_2_5_theorem_2_3_of_predecessor_difference_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hsector_min :
      tasaki23SectorMinimalityCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_sector_minimality
      (V := V) A N c hsector_min)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predecessor-difference
named-callback sector-minimality boundary**: this is the left-endpoint
version of
`tasaki_2_5_theorem_2_3_of_predecessor_difference_named_callbacks`.

It keeps the final public hypotheses in the same named-callback family:
left-endpoint predicted-GS membership, predecessor-difference local
comparison, and sectorwise minimality. -/
abbrev tasaki_2_5_theorem_2_3_of_left_endpoint_predecessor_difference_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hsector_min :
      tasaki23SectorMinimalityCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_sector_minimality
      (V := V) A N c hsector_min)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor-difference named-callback
admissible-reach boundary**: this public boundary replaces the
outside-sector ground-energy lower family in
`tasaki_2_5_theorem_2_3_of_named_callbacks` by the ladder-style
admissible-reach callback.

The outside-family input is supplied by
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach`, so
the remaining named hypotheses are source predicted-GS membership, the
predecessor-difference local comparison, real-coupling hypotheses, and
the admissible-reach callback for outside-sector representatives. -/
abbrev tasaki_2_5_theorem_2_3_of_admissible_reach_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach :
      tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_named_callbacks
    (V := V) A (J := J) N c hBA hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hreach)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predecessor-difference
named-callback admissible-reach boundary**: this is the left-endpoint
version of
`tasaki_2_5_theorem_2_3_of_admissible_reach_named_callbacks`.

It keeps the final public hypotheses in the same named-callback family:
left-endpoint predicted-GS membership, predecessor-difference local
comparison, real-coupling hypotheses, and the ladder-style
admissible-reach callback. -/
abbrev tasaki_2_5_theorem_2_3_of_left_endpoint_admissible_reach_named_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach :
      tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_named_callbacks
    (V := V) A (J := J) N c hBA hleft_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hreach)

end LatticeSystem.Quantum
