---
layout: page
title: "Legacy open-item and axiom history"
permalink: /history/open-items/
---

# Legacy open-item and axiom history

> Historical mixed ledger moved losslessly from the former monolithic index. It contains completed items and must not be used as the current work queue.

<!-- legacy-source:start:2780:3037 -->
## Open items / axioms

The following Tasaki §2.1 / §2.2 items are **not yet fully proved**.
They are tracked here so that future PRs can pick them up and replace
each axiom by a proof (or fill in the deferred construction).

### ~~TODO (P1d''') — Problem 2.1.a for general `S ≥ 1`~~ **DONE**

**Statement (Tasaki p.15)**: For any spin `S`, every operator on the
single-site Hilbert space `h_0 = ℂ^{2S+1}` (i.e. every `(2S+1) × (2S+1)`
matrix) can be written as a polynomial in `1̂, Ŝ^(1), Ŝ^(2), Ŝ^(3)`.

**Status**: Done in general spin-`S` form (Issue #458 closed in PR #490).
The headline theorem `LatticeSystem.Quantum.spinS_adjoin_eq_top` proves

```
Algebra.adjoin ℂ {Ŝ^(1) N, Ŝ^(2) N, Ŝ^(3) N}
  = (⊤ : Subalgebra ℂ (Matrix (Fin (N+1)) (Fin (N+1)) ℂ))
```

via Tasaki solution S.1: diagonal projectors `P_k` are Lagrange-interpolation
polynomials in `Ŝ^{(3)}` (`spinSDiagProj_eq_lagrange_aeval`); off-diagonal
matrix units `E_{i,j}` are products of ladder-step units
(`single_offset_succ_{,swap_}mem_adjoin`); the entry-wise decomposition
`M = ∑_{i,j} M_{i,j} • E_{i,j}` then closes the spanning. The earlier
concrete-case modules `pauliBasis` (`S = 1/2`) and `spinOne_decomposition`
(`S = 1`) remain as illustrative specialisations.

### ~~TODO — Tasaki Problem 2.2.c (SU(2) non-invariance / averaged state)~~ **DONE**

**Statement (Tasaki p.23, eq. (2.2.15))**: An explicit averaged state
of the form

```
(1/4π) ∫₀^{2π} dφ ∫₀^π dθ sin θ · Û^(3)_φ · Û^(2)_θ · |↑₁⟩|↓₂⟩
```

equals (up to phase) the singlet `(1/√2)(|↑₁⟩|↓₂⟩ - |↓₁⟩|↑₂⟩)`. The
problem asks to verify this and to characterize states that fail to be
SU(2)-invariant.

**Status**: Formally proved with zero `sorry` in `Quantum/SU2Integral.lean`
as `problem_2_2_c`. The proof integrates over the Euler-angle parameter space
using `integral_cexp_I_mul_zero_two_pi`, `integral_cexp_neg_I_mul_zero_two_pi`,
and the half-angle trig integrals established in earlier PRs. See
`Quantum/SpinHalfRotation.lean` for `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown`
and `Quantum/SU2Integral.lean` for all supporting lemmas.

### Tasaki §2.5 antiferromagnetic status (issues [#240](https://github.com/phasetr/lattice-system/issues/240), [#412](https://github.com/phasetr/lattice-system/issues/412))

The original antiferromagnetic Heisenberg / Néel state tracker in Issue #240
has been superseded by the longer Marshall-Lieb-Mattis thread in Issue #412.
The graph-centric Néel state foundation (`neelStateOf`) remains the common
entry point, but the main §2.5 theorem/problem endpoints are now formalised as
follows:

- **DONE: Marshall-Lieb-Mattis Theorem 2.2.**  The general spin-`S`
  magnetization-sector and full-Hilbert-space forms were assembled through
  PRs #794-#870, including the bundled full theorem
  `marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`.
- **DONE: Tasaki Theorem 2.3.**  The current public statement is
  `tasaki_2_5_theorem_2_3`, with structural proof witnesses
  `tasaki_2_5_theorem_2_3_bipartiteToy` and
  `tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`; PR #4082
  synchronized the public status rows with these canonical names.
- **DONE: Problem 2.5.a.**  The final single-cluster equality wrapper
  `singleClusterHamiltonianS_minEigenvalue_eq_gs_of_predicted_joint_witness`
  identifies the Hermitian minimum with the predicted energy
  `singleClusterGSEnergyS z N` for `1 ≤ z` under the explicit
  `[IsAlgClosed ℂ]` hypothesis.
- **DONE: Problem 2.5.b.**  The graph-local lower-bound chain reaches the
  closed-form degree wrappers
  `tasaki25b_heisenbergHamiltonianOnGraphS_half_lower_bound_closed_form` and
  `tasaki25b_heisenbergHamiltonianOnGraphS_half_lower_bound_degree_closed_form`.
- **DONE: Problem 2.5.c.**  The balanced structural wrapper
  `singleSiteSpinSquareExpectationS_all_axes_eq_of_balanced_bipartiteCompletePositive`
  removes the explicit Theorem 2.3 witness and proves
  `E_1 = E_2 = E_3 = N(N+2)/12` for normalized non-zero Heisenberg ground
  states under the standard balanced bipartite hypotheses.
- **DONE: Problem 2.5.d.**  The endpoint
  `twoSpinCorrelationS_re_neg_of_tasaki23_balanced_pf_cross` extracts the
  concrete cross-sublattice negative real two-spin correlation from the
  balanced Perron-Frobenius package.
- **Theorem 2.4 status.**  The spin-`1/2` case-(i) target
  uniqueness and zero-magnetization wrappers are live for
  (`-1 < λ < 1`, `D ≥ 0`) as
  `spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf`
  and
  `spinHalf_aHeisS_target_gState_zeroMag_of_MLM_casLadder_t23_pf`
  in the strict-interior `D > 0` form, and as the suffixed
  `_D_nonneg` declarations for the `D = 0` boundary.  The `λ = 1`
  scalar-shift boundary is live as
  `spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf`
  and
  `spinHalf_aHeisS_lam1_gState_zeroMag_of_MLM_casLadder_t23_pf`.
  The strict spin-`1/2` case-(ii) route is live as
  `spinHalf_anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf`
  and
  `spinHalf_aHeisS_case_ii_target_zeroMag_of_MLM_casLadder_t23_pf`;
  the exact spin-`1/2` parameter-region wrappers
  `spinHalf_anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf`
  and
  `spinHalf_aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf`
  dispatch the `D >= 0` case-(i), scalar `λ = 1`, and strict `1 < λ`,
  `D <= 0` case-(ii) endpoints at `N = 1`.
  The general spin-`S` axis-swap unitary instance is now discharged by
  `axisSwapUnitarySSpinS N` and
  `anisotropicHeisenbergS_eigenspace_finrank_le_two_unconditional_general`;
  the bond-only `D >= 0` parity route gives the corresponding
  `_D_nonneg_general` wrappers.  The MLM/Casimir endpoint wrappers construct
  the SU(2)-endpoint uniqueness input from the general Theorem 2.3
  Perron-Frobenius endpoint, so the general spin-`S` case-(i) target
  uniqueness and zero-magnetization endpoint is live for `-1 < λ < 1`,
  `D >= 0`; the explicit SU(2)-point wrappers
  `aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen`
  and
  `aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_zero_gen`
  cover `λ = 1`, `D = 0`.  The ion-only `λ = 1`, `D > 0` parity route gives the
  corresponding
  `aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_pos_gen`
  and
  `aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_pos_gen`
  wrappers for `2 <= N`.  The case-(ii) path-region and conditional target
  wrappers
  `anisotropicHeisenbergParametricPath_in_case_ii_region`,
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_balanced_eq_full`,
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_balanced_eq_full`
  are live.  The case-(ii) strict-gap wrappers
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_strict_gap` and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_strict_gap`
  replace the direct balanced/full equality input by a strict sector gap.
  The no-full-finrank wrappers
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_strict_gap_no_full_le_two` and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_strict_gap_no_full_le_two`
  remove the full `finrank <= 2` input once strict gap is supplied.  The
  crossing-callback wrappers
  `anisotropicHeisenbergS_case_ii_strict_gap_all_M_of_crossing_contradiction`,
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_crossing_contradiction`,
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_crossing_contradiction`
  reduce the remaining case-(ii) strict-gap derivation to one target crossing
  contradiction callback.  The path-callback wrappers
  `anisotropicHeisenbergS_case_ii_crossing_contradiction_of_path_crossing_contradiction`,
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_crossing_contradiction`,
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_path_crossing_contradiction`
  reduce that target callback to a path crossing contradiction callback.  The
  crossing-set wrappers
  `anisotropicHeisenbergS_case_ii_path_crossing_contradiction_of_set_contradiction`,
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_set_contradiction`,
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_set_contradiction`
  reduce the path callback to a contradiction for non-empty
  `perMCrossingSet M ∩ Icc 0 1`.  The first-crossing wrappers
  `anisotropicHeisenbergS_case_ii_crossing_set_contradiction_of_first_crossing`,
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_first_crossing`,
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_first_crossing`
  reduce crossing-set non-emptiness to a contradiction at
  `sInf (perMCrossingSet M ∩ Icc 0 1)`.  The argmin-first-crossing wrappers
  `anisotropicHeisenbergS_case_ii_crossing_contradiction_of_argmin_first_crossing`,
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_argmin_first_crossing`,
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_argmin_first_crossing`
  use `exists_M_chosen_argmin_per_M_first_crossing` to reduce the target
  crossing contradiction to the selected sector minimising that `sInf` among
  all non-balanced sectors with non-empty crossing set.  The first-crossing
  finrank wrappers
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_first_crossing_finrank_bound`
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_first_crossing_finrank_bound`
  discharge that selected-sector callback from a `finrank <= 2` bound at the
  selected first-crossing point.  The path-global finrank wrappers
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_global_finrank_bound`
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_path_global_finrank_bound`
  use `sInf_perMCrossingSet_inter_Icc_mem` to supply that selected-point bound
  from a `finrank <= 2` hypothesis for every path time `t ∈ Icc 0 1`.
  The block-path finrank wrappers
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_axisSwapped_submatrix_blocks_path`
  and
  `aHeisS_case_ii_target_zeroMag_of_axisSwapped_submat_blocks_path`
  derive that path-global input from pathwise axis-swapped parity-block
  submatrix `finrank <= 1` bounds at the full ground energy.
  The block-PF/min wrappers
  `anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_block_pf_min_path`
  and
  `anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_block_pf_min_path`
  replace those full-ground-energy block bounds by pathwise PF simplicity
  and PF/min identification callbacks for the two bare axis-swapped parity
  blocks; the reachability-level wrappers now supply the strict diagonal shift
  from finite parity-block boundedness, and the block reachability totality
  bridge supplies the strict, ion-only, and bond-only reachability hypotheses
  for `2 <= N`.  The corner bridge handles the exact SU(2) point directly from
  a full ground-eigenspace `finrank <= 1` input, so non-corner path points use
  parity-block PF/min while the corner supplies the needed path-global full
  `finrank <= 2` bound.
  The case-(ii) parity-gauge sign layer
  `caseIIParityGaugeDiagonalOnParity_mul_self` introduces the additional
  parity-block diagonal `(-1)^(magSumS / 2)`: its scalar sign product is `1`
  across equal-`magSumS` pairs and `-1` across `magSumS` changes by `2`, so it
  is ready to flip exactly the parity-bond and single-ion `±2` moves in the
  next shifted PF matrix construction.
  The case-(ii) parity-gauged shifted matrix layer
  `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_isSymm_of_real`
  then combines that parity gauge with the Marshall-dressed axis-swapped real
  matrix on each parity block and records the shifted matrix's structural
  diagonal, off-diagonal, strict-shift, and symmetry facts.  The case-(ii)
  local sign layer
  `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_raiseLowerStepS`,
  `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_parityBondStepS`,
  and
  `shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_singleIonStepS`
  proves strict shifted-entry positivity for the three elementary parity-block
  moves under the corresponding strict local hypotheses (`-1 < lambda` for
  transverse moves, `1 < lambda` for parity-bond moves, and `D < 0` for
  single-ion moves).  The block irreducibility layer then turns those step signs
  into matrix-power positivity from block-level parity reachability and into
  conditional `Matrix.IsIrreducible` from entrywise non-negativity, strict
  diagonal shift, and reachability totality.  The block non-negativity bridge
  then lowers that entrywise non-negativity input to a diagonal shift bound and
  a `magSumS` support split for off-diagonal block pairs: equal `magSumS`,
  target raised by two, source raised by two, or zero-support.  The step-support
  bridge packages the strict local signs as non-positive/non-negative dressed
  entries and feeds a `RaiseLowerStepS` / `ParityBondStepS` / `SingleIonStepS` /
  zero-support split into that block non-negativity bridge.  The raw
  total-Hamiltonian support classification now proves this split from
  axis-swapped Hamiltonian entries under the bipartite support-zero assumption on
  `J`: equal-`magSumS` nonzero entries yield a transverse step, `±2` changes
  yield a parity-bond or single-ion step, and all other off-diagonal entries
  vanish.  The boundary move-set bridge now records the ion-only `lambda = 1`
  variant and the bond-only `D = 0` variant, including raw-support reductions
  at both zero-coefficient boundaries.  The parity-block PF/min bridge now converts shifted
  case-(ii) parity-gauged non-negative irreducible blocks into bare
  axis-swapped parity-block PF/min witnesses, with raw-support consumers for
  the strict case-(ii) region, the `lambda = 1` ion-only boundary, and the
  `D = 0` bond-only boundary.  The block-PF/min bridge now also supplies strict
  diagonal shifts automatically on finite parity blocks, and the reachability
  totality bridge supplies the block-level strict, ion-only, and bond-only
  reachability inputs for `2 <= N`.  The corner bridge and total-reachability
  target endpoint now feed the public
  `anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general`
  and
  `aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf_gen`
  wrappers, which package the current general spin-`S`, `2 <= N`,
  Theorem 2.4 parameter region.

### TODO — remove remaining 7 per-theorem linter suppressions (issue [#377](https://github.com/phasetr/lattice-system/issues/377))

Phase 4 substantially closed `lake build` warnings (zero warnings
+ zero errors as of 2026-04-23), with the exception of 7
per-theorem `set_option linter.{flexible,unusedTactic,unusedSimpArgs} false in`
blocks (4 in `SpinOne{Basis,Decomp}`, 3 in
`SpinHalfRotation/Conjugation`). All are comment-justified and
listed in the [Deprecation window](/lattice-system/deprecations/#remaining-linter-suppressions)
page. Removal requires interactive `simp?` per sub-case.

<!-- legacy-source:end:2780:3037 -->

## Authoritative supplemental implementation record (Problem 2.1.a concrete-case modules)

This section is maintained by hand, lies outside the migrated block above, and corrects one
sentence of it. The migrated block is a frozen historical record — it is pinned byte-for-byte by
`scripts/check_docs_hierarchy.py` and is never edited for later corrections or deletions.

The closing sentence of the P1d''' entry reads "The earlier concrete-case modules `pauliBasis`
(`S = 1/2`) and `spinOne_decomposition` (`S = 1`) remain as illustrative specialisations." Two
things about it are no longer accurate:

- `pauliBasis` is a name that never existed in the library. The `S = 1/2` module was
  `Quantum/SpinHalfDecomp.lean`, whose theorems were `pauli_decomposition` and
  `spinHalf_decomposition`. This is a pre-existing drift, independent of the removal recorded in
  the next item.
- That module has since been removed in full, so the `S = 1/2` half of the sentence no longer
  holds. Problem 2.1.a for `S = 1/2` is the `N := 1` instance of `spinS_adjoin_eq_top`, restated in
  the concrete `spinHalfOp` vocabulary in one line by the bridges
  `spinSOp{1,2,3}_one_eq_spinHalfOp{1,2,3}` (`Quantum/SpinS/SpinHalfSpecialization.lean`).

The `S = 1` half stands: `spinOne_decomposition` in `Quantum/SpinOneDecomp.lean` remains as an
illustrative specialisation. No `spinSOp* 2 = spinOneOp*` bridge exists, so its content is not a
one-line instance of the general theorem in the concrete spin-1 vocabulary.
