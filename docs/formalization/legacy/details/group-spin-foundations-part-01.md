---
layout: page
title: "Legacy long-form records: Spin foundations and Tasaki Chapter 2, part 1"
permalink: /formalization/legacy/details/group-spin-foundations-part-01/
---

# Legacy long-form records: Spin foundations and Tasaki Chapter 2, part 1

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-1214"></a>
## Record from former line 1214

**Lean name:** <!-- legacy-detail-lean:start:1214 -->`graphLocalOutsideSite` / `graphLocalOutsideSite_fintype` / `graphLocalOutsideSite_decidableEq` / `graphLocalOutsideConfigExtend` / `graphLocalProductConfig` / `graphLocalConfigEquiv` / `graphLocalConfigEquiv_apply_none` / `graphLocalConfigEquiv_apply_some` / `graphLocalConfigEquiv_apply_outside` / `graphLocalConfigEquiv_symm_apply` / `graphLocalProductConfig_outside` / `graphLocalClusterHamiltonianS_product` / `graphLocalClusterHamiltonianS_product_isHermitian` / `graphLocalClusterHamiltonianS_product_apply_of_outside_eq` / `graphLocalClusterHamiltonianS_product_apply_of_outside_ne` / `graphLocalClusterHamiltonianS_product_mulVec` / `matrix_mulVec_reindex_comp_symm` / `dotProduct_comp_equiv_symm` / `rayleighOnVec_reindex_comp_symm` / `dotProduct_product_re_eq_sum_blocks` / `rayleighOnVec_graphLocalClusterHamiltonianS_product` / `graphLocalClusterHamiltonianS_product_rayleigh_lower` / `graphLocalClusterHamiltonianS_product_minEigenvalue_lower` / `graphLocalClusterHamiltonianS_rayleigh_lower` / `graphLocalClusterHamiltonianS_minEigenvalue_lower`<!-- legacy-detail-lean:end:1214 -->

**File:** <!-- legacy-detail-file:start:1214 -->`Quantum/SpinS/GraphLocalStarLowerBoundCore.lean` (product coordinates + product cluster Hamiltonian with Hermiticity / outside-block apply) + `Quantum/SpinS/GraphLocalStarLowerBound.lean` (product mulVec + reindexing + Rayleigh decomposition over outside blocks + lower bound, split for build speed) (PR #4053)<!-- legacy-detail-file:end:1214 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1214 -->
**Problem 2.5.b graph-local product lower-bound bridge**: reindexes a full graph configuration
around `x` as an option-star configuration paired with an outside assignment. In these product
coordinates the graph-local star is block diagonal in the outside coordinate, each diagonal block is
the option-star Hamiltonian, and the Rayleigh numerator and squared norm decompose as sums over
outside blocks. Reindex-invariance lemmas transfer the result back to the original
same-Hilbert-space graph-local star. Therefore any common Rayleigh lower bound for the option-star
blocks gives the same Hermitian minimum-eigenvalue lower bound for the original graph-local star
(γ-6 step 343)
<!-- legacy-detail:end:1214 -->

<a id="record-1847"></a>
## Record from former line 1847

**Lean name:** <!-- legacy-detail-lean:start:1847 -->`axisSwappedParityBlockPFMinAt` / `axisSwappedParityBlockPFMinPath` / `axisSwappedParityBlockStrictRawSupportPath` / `axisSwappedParityBlockLambdaOneRawSupportPath` / `axisSwappedParityBlockDZeroRawSupportPath` / `exists_parityBlock_dressed_diag_strict_upper_bound` / `axisSwappedParityBlockStrictRawSupportPath_of_reachability` / `axisSwappedParityBlockLambdaOneRawSupportPath_of_reachability` / `axisSwappedParityBlockDZeroRawSupportPath_of_reachability` / `axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_full_min_of_pf_min` / `caseII_axisSwapped_submatrix_blocks_path_of_pf_min` / `axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_path_of_caseII_raw_support` / `caseII_axisSwapped_parityBlockPFMinPath_of_raw_support` / `caseII_axisSwapped_submatrix_blocks_path_of_raw_support_pf_min` / `caseII_axisSwapped_parityBlockPFMinPath_of_reachability` / `caseII_axisSwapped_submatrix_blocks_path_of_reachability_pf_min` / `caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj` / `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_block_pf_min_path` / `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_block_pf_min_path` / `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_raw_support_pf_min_path` / `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_raw_support_pf_min_path` / `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_reachability_pf_min_path` / `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_reachability_pf_min_path`<!-- legacy-detail-lean:end:1847 -->

**File:** <!-- legacy-detail-file:start:1847 --><!-- legacy-detail-file:end:1847 -->Not recorded in the former two-column table

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1847 -->
**General spin-S case-(ii) target bridge from pathwise parity-block PF/min callbacks** (Tasaki §2.5
Theorem 2.4, Issue #412): turns the previous row's full-ground-energy parity-block simplicity input
into the existing bare-submatrix conditional form. For each parity block, if a PF eigenvalue `ν` has
`finrank <= 1` and equals that block's Hermitian minimum, then the block has `finrank <= 1` at the
full anisotropic ground energy: if the full ground energy equals the block minimum, this is the
conditional theorem;

if it is lower, `hermitian_eigenspace_eq_bot_of_real_lt_min` makes the block eigenspace zero. The
path wrapper supplies both parity blocks along `γ(t)`, and the target wrappers feed the result to
the block-path bridge above. The raw-support abbreviations name the strict, `lambda = 1`, and `D =
0` reachability/PF inputs for one parity block. The one-block selector chooses among the fixed
raw-support consumers by the case-(ii) path inequalities and leaves only the corner
`(lambda,D)=(1,0)` PF/min callback explicit;

the even/odd raw-support wrapper applies this selector to both parity blocks, and the full-min
wrapper feeds those callbacks into the block-path PF/min transfer. The raw-support target wrappers
derive the support-zero hypothesis from `hJself` and `hJbip`, then expose target uniqueness and zero
magnetization directly from the raw-support input surface. The reachability wrappers use finite
parity blocks to supply strict diagonal shifts automatically, so the public reachability-level
target wrappers require only the even and odd strict, ion-only, and bond-only reachability totality
hypotheses plus the two explicit corner callbacks. Tasaki, Springer 2020, §2.5 Theorem 2.4, pp.
43--44 (foundational parity-block PF/min path lemmas in
`Quantum/SpinS/AnisotropicHeisenbergSpinSCaseIIBlockPFMinCore.lean`;

the packaged `caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj` helper and the six
`anisotropicHeisenbergS_case_ii_target_*` endpoints in
`Quantum/SpinS/AnisotropicHeisenbergSpinSCaseIIBlockPFMin.lean`)
<!-- legacy-detail:end:1847 -->

<a id="record-1855"></a>
## Record from former line 1855

**Lean name:** <!-- legacy-detail-lean:start:1855 -->`neg_one_pow_mul_self_real` / `neg_one_pow_succ_mul_self_real` / `neg_one_pow_mul_succ_self_real` / `caseIIParityGaugeSignReal_mul_eq_one_of_magSumS_eq` / `caseIIParityGaugeSignReal_mul_eq_neg_one_of_magSumS_add_two` / `caseIIParityGaugeSignReal_mul_eq_neg_one_of_add_two_magSumS` / `caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_of_magSumS_eq` / `caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_magSumS_add_two` / `caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_add_two_magSumS` / `caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_magSumS_eq` / `caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_magSumS_add_two` / `caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_add_two_magSumS` / `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonneg` / `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_gauged_entry_neg` / `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_eq` / `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_add_two` / `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_add_two_magSumS`<!-- legacy-detail-lean:end:1855 -->

**File:** <!-- legacy-detail-file:start:1855 --><!-- legacy-detail-file:end:1855 -->Not recorded in the former two-column table

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1855 -->
**General spin-S case-(ii) parity-gauged sign-transfer layer** (Tasaki §2.5 Theorem 2.4, Issue
#412): adds the real parity-gauge product API and structural sign-transfer lemmas for the case-(ii)
shifted PF matrix. Equal-`magSumS` pairs leave the Marshall-dressed real entry unchanged, while +/-2
pairs negate it;

dressed negativity on transverse moves and dressed positivity on parity-bond or single-ion moves
therefore become parity-gauged off-diagonal non-positivity. A diagonal shift bound plus this
off-diagonal non-positivity gives entrywise non-negativity of `c • 1 - R`, and strict dressed signs
transfer to strict shifted entries. The next local case-(ii) task is to prove those dressed signs
under the strict local hypotheses (`-1 < lambda` for transverse moves, `1 < lambda` for parity-bond
moves, and `D < 0` for single-ion moves), then discharge irreducibility and PF/min identification.
Tasaki, Springer 2020, §2.5 Theorem 2.4, pp. 43--44 (files
`Quantum/SpinS/AnisotropicHeisenbergSpinSCaseIIParityGaugedSignsCore.lean` for the real parity-gauge
products and parity-gauged entry sign transfer +
`Quantum/SpinS/AnisotropicHeisenbergSpinSCaseIIParityGaugedSigns.lean` for the shifted-matrix sign
transfer, split for build speed)
<!-- legacy-detail:end:1855 -->

<a id="record-1861"></a>
## Record from former line 1861

**Lean name:** <!-- legacy-detail-lean:start:1861 -->`ionParityStepSOnBlock` / `ionParityReachableSOnBlock` / `bondParityStepSOnBlock` / `bondParityReachableSOnBlock` / `shiftedCaseIIBlock_pos_of_ion_step_lambda_one` / `shiftedCaseIIBlock_pos_of_bond_step_D_zero` / `shiftedCaseIIBlock_pow_pos_of_ion_reachable_lambda_one` / `shiftedCaseIIBlock_pow_pos_of_bond_reachable_D_zero` / `spinSDotXXZSwap_apply_eq_zero_of_parityBondStepS_witness_lambda_one` / `dressedAxisSwappedReMatrix_zero_of_parityBondStep_lambda_one` / `dressedAxisSwappedReMatrix_single_or_zero_of_magSum_add_two_lambda_one` / `dressedAxisSwappedReMatrix_single_or_zero_of_add_two_magSum_lambda_one` / `dressedAxisSwappedReMatrix_zero_of_singleIonStep_D_zero` / `dressedAxisSwappedReMatrix_bond_or_zero_of_magSum_add_two_D_zero` / `dressedAxisSwappedReMatrix_bond_or_zero_of_add_two_magSum_D_zero` / `shiftedCaseIIBlock_nonneg_of_ion_step_support_lambda_one` / `shiftedCaseIIBlock_nonneg_of_bond_step_support_D_zero` / `shiftedCaseIIBlock_nonneg_of_raw_support_lambda_one` / `shiftedCaseIIBlock_nonneg_of_raw_support_D_zero` / `shiftedCaseIIBlock_irreducible_of_ion_step_support_lambda_one` / `shiftedCaseIIBlock_irreducible_of_bond_step_support_D_zero` / `shiftedCaseIIBlock_irreducible_of_raw_support_lambda_one` / `shiftedCaseIIBlock_irreducible_of_raw_support_D_zero`<!-- legacy-detail-lean:end:1861 -->

**File:** <!-- legacy-detail-file:start:1861 --><!-- legacy-detail-file:end:1861 -->Not recorded in the former two-column table

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1861 -->
**General spin-S case-(ii) boundary move-set bridge** (Tasaki §2.5 Theorem 2.4, Issue #412): records
the boundary move-set variants for the case-(ii) parity-gauged shifted block. At `lambda = 1`, the
parity-bond coefficient vanishes, so the raw support classification reduces to ion-only support;

the wrappers use transverse steps plus `SingleIonStepS`, with conditional irreducibility from
`ionParityReachableSOnBlock`. At `D = 0`, the single-ion branch vanishes;

the raw support classification reduces to bond-only support, and the wrappers use transverse steps
plus `ParityBondStepS` with conditional irreducibility from `bondParityReachableSOnBlock`. The
following PF/min row supplies the bare-block conversion for the strict and zero-coefficient boundary
consumers. Tasaki, Springer 2020, §2.5 Theorem 2.4, pp. 43--44 (file
`Quantum/SpinS/AnisotropicHeisenbergSpinSCaseIIBoundaryMoveSetsCore.lean` +
`Quantum/SpinS/AnisotropicHeisenbergSpinSCaseIIBoundaryMoveSets.lean`)
<!-- legacy-detail:end:1861 -->

<a id="record-1908"></a>
## Record from former line 1908

**Lean name:** <!-- legacy-detail-lean:start:1908 -->`tasaki23GroundStateSectors_mem_iff_eq_of_card_eq` / `tasaki23GroundStateSectors_eq_singleton_of_card_eq` / `tasaki23PredictedTotalSpin_eq_zero_of_card_eq` / `tasaki23PredictedCasimirValue_eq_zero_of_card_eq` / `tasaki23_sector_lift_and_casimir_zero_of_card_eq` / `hermitianMinEigenvalue_eq_common_of_eigenvector_and_global_lower` / `exists_tasaki23_common_energy_eq_hermitianMinEigenvalue` / `heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_sector_support` / `heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_outside_projection_zero` / `heisenbergHamiltonianS_outside_projection_zero_of_strict_sector_lower` / `heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower` / `exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one`<!-- legacy-detail-lean:end:1908 -->

**File:** <!-- legacy-detail-file:start:1908 --><!-- legacy-detail-file:end:1908 -->Not recorded in the former two-column table

**Statement and implementation chronicle:**

<!-- legacy-detail:start:1908 -->
**SU(2)-endpoint global-uniqueness bridge from the MLM side** (Tasaki §2.5 Theorem 2.4 obligation
(2), PR #4020): starts the non-circular replacement for the remaining SU(2) global uniqueness input.
The symmetric `|A| = |¬A|` Theorem 2.3 sector band is reduced to a singleton, the predicted spin and
Casimir collapse to `0`, the balanced PF lift is specialized to a total-Casimir-zero vector, the
Theorem 2.3 common energy is identified with the full Heisenberg Hermitian minimum, and `finrank ≤
1` is transferred from the balanced sector matrix to the full eigenspace once outside-sector
projections are excluded. A strict outside-sector lower-bound callback now implies those outside
projections vanish and hence gives the full `finrank ≤ 1` bridge;

the packaged endpoint combines Theorem 2.3, balanced-cardinality arithmetic, sector PF simplicity,
and strict outside-sector ordering into a direct full SU(2) uniqueness conclusion. The remaining
mathematical task is to prove that strict outside-sector lower bound from the MLM/Casimir chain.
Tasaki, Springer 2020, §2.5 Theorems 2.3 and 2.4, pp. 42–44 (foundational lemmas in
`Quantum/SpinS/Theorem24SU2GlobalUniquenessFromMLMCoreSectors.lean`;

packaged endpoints in `Quantum/SpinS/Theorem24SU2GlobalUniquenessFromMLM.lean`)
<!-- legacy-detail:end:1908 -->
