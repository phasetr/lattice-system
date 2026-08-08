---
layout: page
title: "Legacy long-form records: Spin foundations and Tasaki Chapter 2, part 2"
permalink: /formalization/legacy/details/group-spin-foundations-part-02/
---

# Legacy long-form records: Spin foundations and Tasaki Chapter 2, part 2

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-1978"></a>
## Record from former line 1978

**Lean name:** <!-- legacy-detail-lean:start:1978 -->`tasaki23_lowered_ne_zero_of_marshall_pos` / `totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum` / `tasaki23_lowered_marshall_pos_of_site_sum_pos` / `tasaki23_lowering_identifies_adjacent_sector_energy` / `tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero` / `tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos`<!-- legacy-detail-lean:end:1978 -->

**File:** <!-- legacy-detail-file:start:1978 --><!-- legacy-detail-file:end:1978 -->Not recorded in the former two-column table

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1978 -->
**Tasaki §2.5 Theorem 2.3 adjacent-sector energy identification, conditional lowering step with
non-vanishing and site-sum positivity form**: if an embedded `magSumS = M` source-sector eigenvector
has eigenvalue `μ`, and its lowered vector `Ŝ^-_tot Ψ_M` satisfies the Marshall-positive hypothesis
in the adjacent sector `M + 1`, then strict positivity already implies `Ŝ^-_tot Ψ_M ≠ 0`, and the
full-Hilbert-space Theorem 2.2 uniqueness clause in sector `M + 1` identifies the target sector
eigenvalue with `μ`. The lowered component is also expanded as a sum of the single-site lowering
contributions `∑ x, Ŝ^-_x Ψ_M`;

therefore the same package can be invoked from the local site-sum strict positivity hypothesis. This
combines non-vanishing from strict Marshall positivity, ladder eigenvalue preservation, the
sector-support shift, and the #869 target-sector uniqueness theorem;

the remaining critical-path input is to prove the sitewise Marshall-positivity hypothesis for the
lowered vector. Tasaki, Springer 2020, §2.5 Theorem 2.3, p. 42 (file
`Quantum/SpinS/Theorem23Local.lean` for the two surviving subjects
`tasaki23_lowered_ne_zero_of_marshall_pos` and
`totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum`;

`tasaki23_lowered_marshall_pos_of_site_sum_pos` lived in
`Quantum/SpinS/Theorem23LocalDifferenceMarshall.lean`,
`tasaki23_lowering_identifies_adjacent_sector_energy` and
`tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero` lived in
`Quantum/SpinS/Theorem23LocalDifferenceEnergy.lean`, and
`tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos` lived in
`Quantum/SpinS/Theorem23LocalDifferenceEnergyCasimir.lean`, all three deleted in PR #3919 (bulk
orphan-module deletion))
<!-- legacy-detail:end:1978 -->

<a id="record-1986"></a>
## Record from former line 1986

**Lean name:** <!-- legacy-detail-lean:start:1986 -->`heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_of_eigenvec` / `heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_pow_of_eigenvec` / `totalSpinSOpMinus_pow_mulVec_mem_magSubspaceS_of_mem` / `totalSpinSOpPlus_pow_mulVec_mem_magSubspaceS_of_mem` / `tasaki23OutsideGroundLeftIteratedLadderFullReachCallback` / `tasaki23OutsideGroundRightIteratedLadderFullReachCallback` / `tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_callbacks` / `tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_full_reach` / `tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_iterated_ladder_full_reach_discharge_nonempty`<!-- legacy-detail-lean:end:1986 -->

**File:** <!-- legacy-detail-file:start:1986 --><!-- legacy-detail-file:end:1986 -->Not recorded in the former two-column table

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1986 -->
**Outside-ground iterated total-spin ladder reach for Tasaki §2.5 Theorem 2.3**: the outside reach
input is reduced from an arbitrary full-space reached eigenvector to non-zeroness of an iterated
total-spin ladder output. The Lean bridge proves that `(Ŝ^-_tot)^k` and `(Ŝ^+_tot)^k` preserve the
Heisenberg eigenvalue and shift `magSubspaceS` by exactly `-k` and `+k`;

the left and right callbacks therefore only have to choose an admissible target sector and show that
the corresponding iterated ladder vector is nonzero. The resulting full-space admissible-reach
callback feeds the lower-family bridge, and the discharged final boundary passes that lower family
directly to the source common-energy final boundary. Tasaki, Springer 2020, §2.5 Theorem 2.3, p. 42;

Seneta, *Non-negative Matrices and Markov Chains*, 3rd ed., Springer 2006, §1.2, pp. 27–28 (file
`Quantum/SpinS/Theorem23Local.lean` for the four surviving ladder-power lemmas;

`tasaki23OutsideGroundLeftIteratedLadderFullReachCallback`,
`tasaki23OutsideGroundRightIteratedLadderFullReachCallback`,
`tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_callbacks` and
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_full_reach` lived in
`Quantum/SpinS/Theorem23OutsideGround.lean`, and the wrapper
`tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_iterated_ladder_full_reach_discharge_nonempty`
lived in `Quantum/SpinS/Theorem23Final.lean`, both deleted in PR #3645 (unsound saturated-ladder
Theorem 2.3 route))
<!-- legacy-detail:end:1986 -->
