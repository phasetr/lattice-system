---
layout: page
title: "Legacy catalogue: Single-mode fermion (P2 skeleton)"
permalink: /formalization/legacy/29-single-mode-fermion-p2-skeleton/
---

# Legacy catalogue: Single-mode fermion (P2 skeleton)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Fermions and Hubbard models](/lattice-system/formalization/legacy/#group-fermions-hubbard)

<!-- legacy-source:start:2149:2245 -->
### Single-mode fermion (P2 skeleton)

Phase 2 entry point: the canonical anticommutation algebra of a single
fermion mode acting on `ℂ²` with computational basis
`|0⟩` (vacuum) and `|1⟩` (occupied).

| Lean name | Statement | File |
|---|---|---|
| `fermionAnnihilation` | `c = !![0, 1; 0, 0] = |0⟩⟨1|` | `Fermion/Mode.lean` |
| `fermionCreation` | `c† = !![0, 0; 1, 0] = |1⟩⟨0|` | `Fermion/Mode.lean` |
| `fermionNumber` | `n = !![0, 0; 0, 1] = |1⟩⟨1|` | `Fermion/Mode.lean` |
| `fermionNumber_eq_creation_mul_annihilation` | `n = c† · c` | `Fermion/Mode.lean` |
| `fermionAnnihilation_sq` | `c² = 0` | `Fermion/Mode.lean` |
| `fermionCreation_sq` | `(c†)² = 0` | `Fermion/Mode.lean` |
| `fermionAnticomm_self` | `c · c† + c† · c = 1` (single-mode CAR) | `Fermion/Mode.lean` |
| `fermionNumber_sq` | `n² = n` (idempotent number operator) | `Fermion/Mode.lean` |
| `fermionAnnihilation_conjTranspose` | `cᴴ = c†` | `Fermion/Mode.lean` |
| `fermionCreation_conjTranspose` | `(c†)ᴴ = c` | `Fermion/Mode.lean` |
| `fermionNumber_isHermitian` | `n` is Hermitian | `Fermion/Mode.lean` |
| `fermionVacuum`, `fermionOccupied` | basis vectors `|0⟩ = (1, 0)`, `|1⟩ = (0, 1)` | `Fermion/Mode.lean` |
| `fermionAnnihilation_mulVec_vacuum` / `_occupied` | `c|0⟩ = 0`, `c|1⟩ = |0⟩` | `Fermion/Mode.lean` |
| `fermionCreation_mulVec_vacuum` / `_occupied` | `c†|0⟩ = |1⟩`, `c†|1⟩ = 0` | `Fermion/Mode.lean` |
| `fermionNumber_mulVec_vacuum` / `_occupied` | `n|0⟩ = 0`, `n|1⟩ = |1⟩` | `Fermion/Mode.lean` |
| `fermionAnnihilation_eq_spinHalfOpPlus` | `c = σ^+` (computational-basis identification) | `Fermion/Mode.lean` |
| `fermionCreation_eq_spinHalfOpMinus` | `c† = σ^-` | `Fermion/Mode.lean` |
| `fermionAnnihilation_eq_spinSOpPlus_one` | `c = spinSOpPlus 1` (transitive bridge to generic spin-`S` at `N = 1`) | `Fermion/SpinSBridge.lean` (PR #936) |
| `fermionCreation_eq_spinSOpMinus_one` | `c† = spinSOpMinus 1` | `Fermion/SpinSBridge.lean` (PR #936) |
| `fermionNumber_eq_half_smul_one_sub_spinSOp3_one` | `n = (1/2) · I − spinSOp3 1` (standard physics identification `n = (I − σ^z)/2` lifted to spin-`S` at `N = 1`) | `Fermion/NumberSpinSBridge.lean` (PR #937) |
| `fermionAnnihilation_mul_fermionCreation_eq_one_sub_number` | `c · c† = 1 − n` (hole occupation) | `Fermion/AnnihilationCreationIdentity.lean` (PR #963) |
| `fermionAnnihilation_mul_fermionCreation_eq_half_smul_one_add_spinSOp3_one` | `c · c† = (1/2) · I + spinSOp3 1` (spin-`S` form) | `Fermion/CCDaggerSpinSBridge.lean` (PR #965) |
| `fermionAnnihilation_mul_fermionCreation_mulVec_vacuum` / `_occupied` | `(c · c†) · |0⟩ = |0⟩`; `(c · c†) · |1⟩ = 0` (vacuum/occupied as eigenstates of `c · c†`) | `Fermion/CCDaggerAction.lean` (PR #966) |
| `fermionVacuum_inner_self` / `fermionOccupied_inner_self` / `fermionVacuum_inner_fermionOccupied` / `fermionOccupied_inner_fermionVacuum` | vacuum/occupied are orthonormal | `Fermion/StatesOrthonormal.lean` (PR #968) |
| `fermionVacuum_expectation_fermionNumber` / `fermionOccupied_expectation_fermionNumber` | `⟨n⟩` on vacuum = 0; on occupied = 1 | `Fermion/NumberExpectations.lean` (PR #969) |
| `fermionVacuum_expectation_fermionAnnihilation_mul_fermionCreation` / `fermionOccupied_expectation_fermionAnnihilation_mul_fermionCreation` | `⟨c · c†⟩` on vacuum = 1; on occupied = 0 | `Fermion/CCDaggerExpectations.lean` (PR #971) |
| `fermionNumber_add_fermionAnnihilation_mul_fermionCreation_eq_one` | `n + c · c† = 1` (resolution of identity in occupation basis) | `Fermion/ProjectionSum.lean` (PR #972) |
| `fermionAnnihilation_mul_fermionCreation_sq` | `(c · c†)² = c · c†` (idempotent projection) | `Fermion/CCDaggerIdempotent.lean` (PR #974) |
| `fermionNumber_mul_fermionAnnihilation_mul_fermionCreation_eq_zero` / `fermionAnnihilation_mul_fermionCreation_mul_fermionNumber_eq_zero` | `n · (c · c†) = 0`; `(c · c†) · n = 0` (orthogonal projections) | `Fermion/ProjectionsOrthogonal.lean` (PR #976) |
| `fermionNumber_commute_fermionAnnihilation_mul_fermionCreation` | `Commute n (c · c†)` (both products zero) | `Fermion/ProjectionsCommute.lean` (PR #978) |
| `fermionAnnihilation_mul_fermionCreation_isHermitian` | `(c · c†)ᴴ = c · c†` | `Fermion/CCDaggerHermitian.lean` (PR #980) |
| `fermionNumber_mul_fermionAnnihilation_eq_zero` / `fermionAnnihilation_mul_fermionNumber_eq_fermionAnnihilation` | `n · c = 0`; `c · n = c` | `Fermion/AnnihilationNumberIdentities.lean` (PR #982) |
| `fermionCreation_mul_fermionNumber_eq_zero` / `fermionNumber_mul_fermionCreation_eq_fermionCreation` | `c† · n = 0`; `n · c† = c†` | `Fermion/CreationNumberIdentities.lean` (PR #984) |
| `fermionAnnihilation_mul_fermionCreation_mul_fermionAnnihilation` / `fermionCreation_mul_fermionAnnihilation_mul_fermionCreation` | `c · c† · c = c`; `c† · c · c† = c†` (partial-isometry relations) | `Fermion/PartialIsometry.lean` (PR #986) |
| `fermionNumber_commutator_fermionAnnihilation` / `fermionNumber_commutator_fermionCreation` | `[n, c] = −c`; `[n, c†] = c†` (ladder commutators) | `Fermion/NumberLadderCommutators.lean` (PR #988) |
| `fermionAnnihilation_commutator_fermionCreation` | `[c, c†] = 1 − 2 · n` (fermion analogue of bosonic `[a, a†] = 1`; ±1 on basis states) | `Fermion/CCDaggerCommutator.lean` (PR #989) |
| `fermionNumber_anticommutator_fermionAnnihilation` / `fermionNumber_anticommutator_fermionCreation` | `{n, c} = c`; `{n, c†} = c†` (number-ladder anticommutators, dual of PR #988) | `Fermion/NumberLadderAnticommutators.lean` (PR #990) |
| `fermionAnnihilation_trace_eq_zero` / `fermionCreation_trace_eq_zero` / `fermionNumber_trace_eq_one` / `fermionAnnihilation_mul_fermionCreation_trace_eq_one` | `tr(c) = 0`; `tr(c†) = 0`; `tr(n) = 1`; `tr(c · c†) = 1` (single-mode trace identities) | `Fermion/Traces.lean` (PR #991) |
| `fermionNumber_pow_succ` / `fermionAnnihilation_mul_fermionCreation_pow_succ` | `n^(k+1) = n`; `(c · c†)^(k+1) = c · c†` for any `k : ℕ` (positive-degree power identities of the idempotent projections) | `Fermion/ProjectionPow.lean` (PR #992) |
| `fermionMultiNumber_anticommutator_fermionMultiAnnihilation_self` / `fermionMultiNumber_anticommutator_fermionMultiCreation_self` | `{n_i, c_i} = c_i`; `{n_i, c_i†} = c_i†` (multi-mode JW same-site ladder anticommutators, mirror of PR #990) | `Fermion/JordanWigner/NumberAnticommutators.lean` (PR #993) |
| `fermionMultiAnnihilation_commutator_fermionMultiCreation_self` | `[c_i, c_i†] = 1 − 2 · n_i` (multi-mode JW same-site `c_i`–`c_i†` commutator, mirror of PR #989) | `Fermion/JordanWigner/CDaggerCCommutator.lean` (PR #994) |
| `fermionMultiNumber_pow_succ` | `n_i^(k+1) = n_i` for any `k : ℕ` (multi-mode JW idempotent projection power identity, mirror of PR #992) | `Fermion/JordanWigner/NumberPow.lean` (PR #995) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number` / `fermionMultiNumber_add_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one` | `c_i · c_i† = 1 − n_i`; `n_i + c_i · c_i† = 1` (multi-mode JW hole-occupation + resolution of identity, mirror of PRs #963 and #972) | `Fermion/JordanWigner/CDaggerCIdentity.lean` (PR #996) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_sq` / `fermionMultiAnnihilation_mul_fermionMultiCreation_pow_succ` | `(c_i · c_i†)² = c_i · c_i†`; `(c_i · c_i†)^(k+1) = c_i · c_i†` (multi-mode JW hole-projection idempotency + power, mirror of PRs #974 and #992) | `Fermion/JordanWigner/CDaggerCProjection.lean` (PR #997) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_isHermitian` | `(c_i · c_i†)ᴴ = c_i · c_i†` (multi-mode JW hole projection Hermitian, mirror of PR #980) | `Fermion/JordanWigner/CDaggerCHermitian.lean` (PR #998) |
| `fermionMultiNumber_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero` / `fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiNumber_eq_zero` | `n_i · (c_i · c_i†) = 0`; `(c_i · c_i†) · n_i = 0` (multi-mode JW orthogonal projections, mirror of PR #976) | `Fermion/JordanWigner/ProjectionsOrthogonal.lean` (PR #999) |
| `fermionMultiNumber_commute_fermionMultiAnnihilation_mul_fermionMultiCreation` | `Commute n_i (c_i · c_i†)` (multi-mode JW projections commute, mirror of PR #978) | `Fermion/JordanWigner/ProjectionsCommute.lean` (PR #1000) |
| `fermionMultiNumber_mul_fermionMultiAnnihilation_eq_zero` / `fermionMultiAnnihilation_mul_fermionMultiNumber_eq_fermionMultiAnnihilation` | `n_i · c_i = 0`; `c_i · n_i = c_i` (multi-mode JW number-annihilation identities, mirror of PR #982) | `Fermion/JordanWigner/AnnihilationNumberIdentities.lean` (PR #1001) |
| `fermionMultiCreation_mul_fermionMultiNumber_eq_zero` / `fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation` | `c_i† · n_i = 0`; `n_i · c_i† = c_i†` (multi-mode JW number-creation identities, mirror of PR #984) | `Fermion/JordanWigner/CreationNumberIdentities.lean` (PR #1002) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiAnnihilation` / `fermionMultiCreation_mul_fermionMultiAnnihilation_mul_fermionMultiCreation` | `c_i · c_i† · c_i = c_i`; `c_i† · c_i · c_i† = c_i†` (multi-mode JW partial-isometry identities, mirror of PR #986) | `Fermion/JordanWigner/PartialIsometry.lean` (PR #1003) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_commute` | `Commute (c_i · c_i†) (c_j · c_j†)` for any `i, j` (multi-mode JW hole projections at any two sites commute) | `Fermion/JordanWigner/HoleProjectionsCommute.lean` (PR #1004) |
| `fermionUpNumber_commute_fermionDownNumber` / `fermionUpNumber_mul_fermionDownNumber_sq` | `Commute n_↑(i) n_↓(i)`; `(n_↑(i) · n_↓(i))² = n_↑(i) · n_↓(i)` (Hubbard same-site double-occupancy projection: cross-spin number commute + idempotency) | `Fermion/JordanWigner/Hubbard/DoubleOccupancyProjection.lean` (PR #1005) |
| `fermionUpNumber_mul_fermionDownNumber_commute` | `Commute (n_↑(i) · n_↓(i)) (n_↑(j) · n_↓(j))` for any `i, j` (cross-site Hubbard double-occupancy commute, makes the on-site interaction a sum of pairwise commuting projections) | `Fermion/JordanWigner/Hubbard/DoubleOccupancyCommute.lean` (PR #1006) |
| `fermionUpNumber_isHermitian` / `fermionDownNumber_isHermitian` / `fermionUpNumber_mul_fermionDownNumber_isHermitian` | `(n_↑(i)).IsHermitian`; `(n_↓(i)).IsHermitian`; `(n_↑(i) · n_↓(i)).IsHermitian` (spinful Hubbard number-operator Hermiticity, named-lemma extraction) | `Fermion/JordanWigner/Hubbard/SpinfulNumberHermitian.lean` (PR #1007) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiAnnihilation_of_ne` / `fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiCreation_of_ne` | `Commute (c_i · c_i†) c_j` and `Commute (c_i · c_i†) c_j†` for `i ≠ j` (cross-site multi-mode hole projection vs ladder operators) | `Fermion/JordanWigner/HoleProjectionCommuteLadder.lean` (PR #1008) |
| `fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiNumber` / `fermionMultiNumber_commute_fermionMultiAnnihilation_mul_fermionMultiCreation_any` | `Commute (c_i · c_i†) n_j` and `Commute n_i (c_j · c_j†)` for any `i, j` (mixed-form sibling of PR #1004) | `Fermion/JordanWigner/HoleProjectionCommuteNumber.lean` (PR #1013) |
| `fermionAnnihilation_mul_fermionAnnihilation_mul_fermionCreation_eq_zero` / `fermionAnnihilation_mul_fermionCreation_mul_fermionCreation_eq_zero` | `c · (c · c†) = 0`; `(c · c†) · c† = 0` (single-mode ladder-on-hole-projection vanishing identities) | `Fermion/CCDaggerLadderZero.lean` (PR #1009) |
| `fermionAnnihilation_add_fermionCreation_sq` | `(c + c†)² = 1` (single-mode X-Pauli analog: `c + c† = σ_x` and `σ_x² = I`) | `Fermion/CPlusCDaggerSq.lean` (PR #1021) |
| `fermionMultiAnnihilation_add_fermionMultiCreation_sq` | `(c_i + c_i†)² = 1` (multi-mode JW `σ_x`-analog, mirror of PR #1021) | `Fermion/JordanWigner/CPlusCDaggerSq.lean` (PR #1022) |
| `fermionAnnihilation_sub_fermionCreation_sq` | `(c − c†)² = −1` (single-mode iY-Pauli analog: `c − c† = i·σ_y` and `(i·σ_y)² = −I`; companion to PR #1021) | `Fermion/CMinusCDaggerSq.lean` (PR #1023) |
| `fermionMultiAnnihilation_sub_fermionMultiCreation_sq` | `(c_i − c_i†)² = −1` (multi-mode JW iY-Pauli analog, mirror of PR #1023) | `Fermion/JordanWigner/CMinusCDaggerSq.lean` (PR #1024) |
| `fermionAnnihilation_add_fermionCreation_mul_fermionAnnihilation_sub_fermionCreation` / `fermionAnnihilation_sub_fermionCreation_mul_fermionAnnihilation_add_fermionCreation` | `(c+c†)(c−c†) = 2·n−1`; `(c−c†)(c+c†) = 1−2·n` (single-mode mixed Pauli-X·iY products = ±σ_z analog) | `Fermion/CPlusCDaggerMulCMinusCDagger.lean` (PR #1025) |
| `fermionAnnihilation_add_fermionCreation_isHermitian` / `fermionAnnihilation_sub_fermionCreation_conjTranspose` / `fermionAnnihilation_add_fermionCreation_anticomm_fermionAnnihilation_sub_fermionCreation` | `(c+c†)` Hermitian; `(c−c†)ᴴ = −(c−c†)`; `{c+c†, c−c†} = 0` (single-mode Pauli-X / iY analog Hermiticity + anticommute structure) | `Fermion/CPlusMinusCDaggerHermitian.lean` (PR #1026) |
| `fermionMultiPlus_mul_fermionMultiMinus` / `fermionMultiMinus_mul_fermionMultiPlus` / `fermionMultiAnnihilation_add_fermionMultiCreation_isHermitian` / `fermionMultiAnnihilation_sub_fermionMultiCreation_conjTranspose` / `fermionMultiPlus_anticomm_fermionMultiMinus` | multi-mode JW Pauli-X/iY analog full structure (mirror of PRs #1025, #1026) | `Fermion/JordanWigner/CPlusMinusCDaggerPauli.lean` (PR #1027) |
| `one_sub_two_smul_fermionNumber_sq` | `(1 − 2·n)² = 1` (single-mode `σ_z`-analog involution; completes Pauli-trio with PRs #1021 and #1023) | `Fermion/OneSubTwoNumberSq.lean` (PR #1028) |
| `one_sub_two_smul_fermionMultiNumber_sq` | `(1 − 2·n_i)² = 1` (multi-mode JW `σ_z`-analog involution, mirror of PR #1028; completes multi-mode Pauli-trio with PRs #1022, #1024) | `Fermion/JordanWigner/OneSubTwoNumberSq.lean` (PR #1029) |
| `fermionMultiAnnihilation_anticomm_of_ne` / `fermionMultiCreation_anticomm_of_ne` / `fermionMultiAnnihilation_creation_anticomm_of_ne` / `fermionMultiCreation_annihilation_anticomm_of_ne` | symmetric `_of_ne` versions of the four cross-site CAR identities (lift `_lt` form via trichotomy + add_comm) | `Fermion/JordanWigner/CAR/CrossSiteOfNe.lean` (PR #1030) |
| `fermionMultiPlus_anticomm_fermionMultiPlus_of_ne` | `{c_i+c_i†, c_j+c_j†} = 0` for `i ≠ j` (cross-site Pauli-X-analog operators anticommute via JW string sign; expansion into 4 `_of_ne` cross-site CAR identities) | `Fermion/JordanWigner/CPlusCDaggerAnticomm.lean` (PR #1031) |
| `fermionMultiMinus_anticomm_fermionMultiMinus_of_ne` / `fermionMultiPlus_anticomm_fermionMultiMinus_of_ne` | `{c_i−c_i†, c_j−c_j†} = 0` and `{c_i+c_i†, c_j−c_j†} = 0` for `i ≠ j` (cross-site mixed Pauli-analog anticommutators; together with PR #1031 covers all 4 sign combinations) | `Fermion/JordanWigner/CMinusCDaggerAnticomm.lean` (PR #1032) |
| `fermionMultiNumber_commute_fermionMultiPlus_of_ne` / `fermionMultiNumber_commute_fermionMultiMinus_of_ne` | `Commute n_i (c_j ± c_j†)` for `i ≠ j` (cross-site number commutes with Pauli-X/iY-analog combinations) | `Fermion/JordanWigner/NumberCommutePauliOfNe.lean` (PR #1033) |
| `fermionMultiAnnihilation_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero` / `fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiCreation_eq_zero` | `c_i · (c_i · c_i†) = 0`; `(c_i · c_i†) · c_i† = 0` (multi-mode JW ladder-on-hole-projection vanishing, mirror of PR #1009) | `Fermion/JordanWigner/CDaggerCLadderZero.lean` (PR #1010) |
| `fermionUpDownNumber_site_partition_eq_one` | `(1−n_↑)(1−n_↓) + n_↑(1−n_↓) + (1−n_↑)n_↓ + n_↑·n_↓ = 1` (Hubbard per-site 4-state partition of identity: empty, only-up, only-down, doubly-occupied) | `Fermion/JordanWigner/Hubbard/SitePartitionIdentity.lean` (PR #1011) |
| `one_sub_fermionUpNumber_mul_one_sub_fermionDownNumber_sq` / `fermionUpNumber_mul_one_sub_fermionDownNumber_sq` / `one_sub_fermionUpNumber_mul_fermionDownNumber_sq` | `(p_∅)² = p_∅`, `(p_↑)² = p_↑`, `(p_↓)² = p_↓` (Hubbard empty/only-up/only-down per-site projections idempotent; companions to PR #1005 `(p_⇈)² = p_⇈`) | `Fermion/JordanWigner/Hubbard/SiteProjectionsIdempotent.lean` (PR #1012) |
| `fermionUpDownNumber_mul_empty_eq_zero` / `empty_mul_fermionUpDownNumber_eq_zero` | `p_⇈ · p_∅ = 0`; `p_∅ · p_⇈ = 0` (Hubbard per-site doubly-occupied and empty projections are mutually orthogonal) | `Fermion/JordanWigner/Hubbard/SiteProjectionsDoublyEmpty.lean` (PR #1014) |
| `one_sub_fermionUpNumber_mul_one_sub_fermionDownNumber_isHermitian` / `fermionUpNumber_mul_one_sub_fermionDownNumber_isHermitian` / `one_sub_fermionUpNumber_mul_fermionDownNumber_isHermitian` | `(p_∅)`, `(p_↑)`, `(p_↓)` Hermitian (companions to PR #1007 `(p_⇈)` Hermitian; together all four per-site occupation projections are Hermitian) | `Fermion/JordanWigner/Hubbard/SiteProjectionsHermitian.lean` (PR #1015) |
| `fermionUpProjection_mul_fermionDownProjection_eq_zero` / `fermionDownProjection_mul_fermionUpProjection_eq_zero` | `p_↑ · p_↓ = 0`; `p_↓ · p_↑ = 0` (Hubbard per-site only-up and only-down projections orthogonal) | `Fermion/JordanWigner/Hubbard/SiteProjectionsUpDown.lean` (PR #1016) |
| `fermionEmptyProjection_mul_fermionUpProjection_eq_zero` / `fermionUpProjection_mul_fermionEmptyProjection_eq_zero` / `fermionEmptyProjection_mul_fermionDownProjection_eq_zero` / `fermionDownProjection_mul_fermionEmptyProjection_eq_zero` | `p_∅ · p_↑ = 0`, `p_↑ · p_∅ = 0`, `p_∅ · p_↓ = 0`, `p_↓ · p_∅ = 0` (Hubbard empty per-site projection orthogonal to both single-occupancy projections) | `Fermion/JordanWigner/Hubbard/SiteProjectionsEmptySingle.lean` (PR #1017) |
| `fermionUpProjection_mul_fermionDoublyProjection_eq_zero` / `fermionDoublyProjection_mul_fermionUpProjection_eq_zero` / `fermionDownProjection_mul_fermionDoublyProjection_eq_zero` / `fermionDoublyProjection_mul_fermionDownProjection_eq_zero` | `p_↑ · p_⇈ = 0`, `p_⇈ · p_↑ = 0`, `p_↓ · p_⇈ = 0`, `p_⇈ · p_↓ = 0` (Hubbard single-occupancy ⊥ doubly-occupied per-site projections; **completes all 6/6 cross-projection orthogonality pairs**) | `Fermion/JordanWigner/Hubbard/SiteProjectionsSingleDoubly.lean` (PR #1018) |
| `fermionUpProjection_add_fermionDoublyProjection_eq_fermionUpNumber` / `fermionDownProjection_add_fermionDoublyProjection_eq_fermionDownNumber` / `fermionEmptyProjection_add_fermionUpProjection_eq_one_sub_fermionDownNumber` / `fermionEmptyProjection_add_fermionDownProjection_eq_one_sub_fermionUpNumber` | `p_↑+p_⇈ = n_↑`; `p_↓+p_⇈ = n_↓`; `p_∅+p_↑ = 1−n_↓`; `p_∅+p_↓ = 1−n_↑` (Hubbard per-site projection-aggregation: 4-state projections aggregate to spin-resolved number operators and complements) | `Fermion/JordanWigner/Hubbard/SiteProjectionsSpinResolved.lean` (PR #1019) |
| (6 pairwise `Commute` lemmas) | `Commute (p_α(i)) (p_β(i))` for all 6 distinct `α, β` ∈ `{∅, ↑, ↓, ⇈}` (same-site Hubbard 4-state projections fully commute; trivial corollaries of PRs #1014, #1016, #1017, #1018 since both products vanish) | `Fermion/JordanWigner/Hubbard/SiteProjectionsCommute.lean` (PR #1020) |
| `fermionDoublyProjection_pow_succ` / `fermionEmptyProjection_pow_succ` / `fermionUpProjection_pow_succ` / `fermionDownProjection_pow_succ` | `(p_α(i))^(k+1) = p_α(i)` for all 4 per-site projections (induction from PRs #1005, #1012; mirrors PR #992) | `Fermion/JordanWigner/Hubbard/SiteProjectionsPow.lean` (PR #1034) |
| `fermionEmptyProjection_commute_of_any` | `Commute (p_∅(i)) (p_∅(j))` for any `i, j` (cross-site Hubbard empty projections commute; companion to PR #1006 for `p_⇈`) | `Fermion/JordanWigner/Hubbard/EmptyProjectionCommute.lean` (PR #1035) |
| `fermionUpProjection_commute_of_any` / `fermionDownProjection_commute_of_any` | `Commute (p_↑(i)) (p_↑(j))`, `Commute (p_↓(i)) (p_↓(j))` for any `i, j` (cross-site Hubbard single-occupancy projections commute; completes diagonal cross-site Commute relations together with PRs #1006, #1035) | `Fermion/JordanWigner/Hubbard/SingleProjectionsCommute.lean` (PR #1036) |
| `fermionUpProjection_commute_fermionDownProjection_of_any` | `Commute (p_↑(i)) (p_↓(j))` for any `i, j` (cross-projection only-up vs only-down commute; non-diagonal extension) | `Fermion/JordanWigner/Hubbard/UpDownProjectionCommute.lean` (PR #1037) |
| (5 remaining cross-projection commutes) | `Commute (p_α(i)) (p_β(j))` for the 5 remaining `(α, β)` pairs (PR #1038, completes the 16/16 cross-projection commute matrix together with PRs #1006, #1020, #1035, #1036, #1037) | `Fermion/JordanWigner/Hubbard/RemainingProjectionCommutes.lean` (PR #1038) |
| `hubbardAllDownState` / `fermionDownNumber_mulVec_allDownState` / `fermionUpNumber_mulVec_allDownState` / `hubbardOnSiteInteraction_mulVec_allDownState` / `fermionUpAnnihilation_mulVec_allDownState` / `fermionDownCreation_mulVec_allDownState` | all-down spin state for spinful Hubbard: `n_↓·|↓..⟩ = |↓..⟩`, `n_↑·|↓..⟩ = 0`, `H_int·|↓..⟩ = 0`, etc. (mirror of `AllUpState.lean`) | `Fermion/JordanWigner/Hubbard/AllDownState.lean` (PR #1039) |
| `fermionTotalDownNumber_mulVec_allDownState` / `fermionTotalUpNumber_mulVec_allDownState` / `fermionTotalSpinZ_mulVec_allDownState` / `fermionTotalSpinMinus_mulVec_allDownState` | `N_↓·|↓..⟩ = (N+1)·|↓..⟩`, `N_↑·|↓..⟩ = 0`, `S^z·|↓..⟩ = -(N+1)/2·|↓..⟩` (lowest weight), `S^-·|↓..⟩ = 0` (mirror of `SaturatedFerromagnetism.lean`'s all-up versions) | `Fermion/JordanWigner/Hubbard/AllDownStateTotalNumber.lean` (PR #1040) |
| `fermionTotalSpinMinus_conjTranspose` / `fermionTotalSpinZ_isHermitian` / `fermionTotalSpinSquared_isHermitian` | `(Ŝ^-_tot)ᴴ = Ŝ^+_tot`; `(Ŝ^z_tot)` Hermitian; `(Ŝ²_tot)` Hermitian (total-spin operator Hermiticity bundle) | `Fermion/JordanWigner/Hubbard/SpinTotHermitian.lean` (PR #1041) |

<!-- legacy-source:end:2149:2245 -->

## Authoritative supplemental implementation record (Hubbard per-site / cross-site projection commute relations)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
the current state of the Hubbard 4-state per-site projection commute relations. The migrated
catalogue block above is a frozen historical record — its rows are pinned byte-for-byte by
`scripts/check_docs_hierarchy.py` and are never edited for later deletions, so the two anonymous
family rows "(6 pairwise `Commute` lemmas)" and "(5 remaining cross-projection commutes)" describe
membership as it stood at migration time.

Both of the modules named by those two rows have since been retired in full as unreferenced
corollaries of the per-site orthogonality results and of `fermionMultiNumber_commute`-style
pairwise number commutation: `Fermion/JordanWigner/Hubbard/SiteProjectionsCommute.lean`
(6 same-site pairwise `Commute` theorems) and
`Fermion/JordanWigner/Hubbard/RemainingProjectionCommutes.lean`
(5 cross-projection `Commute` theorems).
The "16/16 commute matrix" completeness claim of the migrated row therefore no longer describes
the current library.

The cross-site commute relations that survive are unchanged:
`fermionUpProjection_commute_fermionDownProjection_of_any` in
`Fermion/JordanWigner/Hubbard/UpDownProjectionCommute.lean`,
`fermionEmptyProjection_commute_of_any` in
`Fermion/JordanWigner/Hubbard/EmptyProjectionCommute.lean`,
`fermionUpProjection_commute_of_any` / `fermionDownProjection_commute_of_any` in
`Fermion/JordanWigner/Hubbard/SingleProjectionsCommute.lean`, and
`fermionUpNumber_mul_fermionDownNumber_commute` (the `p_⇈` diagonal case,
`Commute (p_⇈(i)) (p_⇈(j))`) in
`Fermion/JordanWigner/Hubbard/DoubleOccupancyCommute.lean`.

---

[← Spin-`S` saturated ferromagnetic state (Tasaki §2.4 generalised)](/lattice-system/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-02/) · [Catalogue](/lattice-system/formalization/legacy/) · [Multi-mode fermion via Jordan–Wigner (P2 backbone) →](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-01/)
