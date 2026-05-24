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
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-GS admissible-reach
boundary**: this replaces the outside-sector ground-energy lower family in
the threaded public predecessor-difference boundary by the ladder-style
admissible-reach callback.

The bridge
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach`
supplies the outside-sector ground-energy lower family, so the visible
remaining inputs are the uniform predicted-GS callback, the local
predecessor-difference comparison, the real-coupling hypotheses, and
admissible reach for outside-sector representatives. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c hBA hsector_nonempty hsource_predictedGS
    hpredecessor_difference
    (tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
      (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hreach)

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
/-- **Tasaki §2.5 Theorem 2.3 discharged non-empty admissible-reach
boundary**: this removes both the explicit physical-range non-emptiness
callback and the outside-sector ground-energy lower-family callback from
the threaded predecessor-difference boundary.

Non-emptiness comes from `magConfigS_nonempty_of_le_card_mul`, while the
outside-sector ground-energy lower family is supplied by the admissible
reach bridge. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_physical_range_nonempty_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach
    (V := V) A (J := J) N c hBA
    (fun _M hM => magConfigS_nonempty_of_le_card_mul (V := V) (N := N) hM)
    hsource_predictedGS hpredecessor_difference hJ_real hJ_real' hJ_nn hJ_sym
    hJ_bipartite hc_strict hreach

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 full-admissible-reach discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
a full-space ladder-reach callback.  The full-space callback is restricted to
the sector-coordinate admissible-reach callback before reusing the existing
admissible-reach discharged boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleReachCallback_of_full_reach
      (V := V) A (J := J) N c hfull)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 iterated-ladder full-reach discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right non-zeroness callbacks for iterated
total-spin ladder outputs.  The iterated ladder bridge supplies the
full-space admissible-reach callback before reusing the full-reach final
boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_full_admissible_reach_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_callbacks
      (V := V) A (J := J) N c hleft hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 iterated-ladder Casimir full-reach
discharged boundary**: this version of the discharged final
predecessor-difference boundary accepts left and right Casimir callbacks
which prove non-zeroness for the iterated total-spin ladder outputs.  The
Casimir callback bridge supplies the full-space admissible-reach callback
before reusing the full-reach final boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_full_admissible_reach_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_casimir_callbacks
      (V := V) A (J := J) N c hleft hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-Casimir source discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right saturated total-Casimir source callbacks.
Those callbacks choose the interval endpoints, discharge every intermediate
Casimir kernel-avoidance obligation, and then reuse the iterated-ladder
Casimir full-reach final boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_iterated_ladder_casimir_full_reach_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback_of_saturated_casimir_source
      (V := V) A (J := J) N c hleft)
    (tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback_of_saturated_casimir_source
      (V := V) A (J := J) N c hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-span source discharged
boundary**: this version of the discharged final predecessor-difference
boundary accepts left and right source callbacks in the concrete span of the
saturated ferromagnetic total-spin ladder.  The maximum-Casimir eigenspace
identification converts those span callbacks to saturated-Casimir source
callbacks before reusing the saturated-Casimir final boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_casimir_sources_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_ladder_span_source
      (V := V) A (J := J) N c hleft)
    (tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_ladder_span_source
      (V := V) A (J := J) N c hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-joint source discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
left and right source callbacks in the saturated-ferromagnet joint eigenspace.
The Tasaki §2.4 ladder-span identification converts those source-vector
callbacks to saturated-ladder-span callbacks before reusing the saturated
ladder-span final boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_ladder_span_sources_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback_of_saturated_joint_source
      A (J := J) N c hleft)
    (tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback_of_saturated_joint_source
      A (J := J) N c hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated eigen-source discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
left and right source callbacks at the saturated Heisenberg eigenvalue plus
the existing saturated-Casimir source callbacks.  These two eigenspace
inputs assemble the saturated joint source callbacks before reusing the
saturated-joint final boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_saturated_joint_sources_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_eigen_sources
      A (J := J) N c hleftH hleftCas)
    (tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_eigen_sources
      A (J := J) N c hrightH hrightCas)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 side-admissible-reach discharged boundary**:
this version of the discharged final predecessor-difference boundary accepts
separate left and right directional outside-sector reach callbacks.  The side
callbacks are recombined into the full admissible-reach callback before reusing
the existing admissible-reach discharged boundary. -/
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
    tasaki_2_5_theorem_2_3 (V := V) A N J c :=
  tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_admissible_reach_discharge_nonempty
    (V := V) A (J := J) N c hBA hsource_predictedGS hpredecessor_difference
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleReachCallback_of_side_callbacks
      (V := V) A (J := J) N c hleft hright)

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
