---
layout: page
title: "Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 4"
permalink: /formalization/legacy/details/group-spin-models-part-04/
---

# Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 4

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-748"></a>
## Record from former line 748

**Lean name:** <!-- legacy-detail-lean:start:748 -->`IsHiddenAFMConfig` / `hhafProjection` / `tasaki_prop_6_5_hhaf_spin_one`<!-- legacy-detail-lean:end:748 -->

**File:** <!-- legacy-detail-file:start:748 -->`Quantum/SpinS/HiddenAntiferromagneticOrder.lean` + `Quantum/SpinS/HiddenAntiferromagneticOrderUniqueness.lean` + `Quantum/SpinS/HiddenAntiferromagneticOrderUniquenessCore.lean`<!-- legacy-detail-file:end:748 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:748 -->
**§6.3 Proposition 6.5** (Gómez-Santos;

**PROVED axiom-free**; eqs. (6.3.7)–(6.3.9)): the **S=1 chain on the hidden-AFM subspace `H_HAF`**.
**`tasaki_prop_6_5_hhaf_spin_one` is now a proved theorem** (formerly a documented axiom; `#print
axioms` → `propext`/`Classical.choice`/`Quot.sound`): the final assembly
`tasaki_prop_6_5_hhaf_spin_one` bundles, for even `L>0`, a ground state `Φ = hhafSubspaceEmbedding`
of the balanced Perron–Frobenius eigenvector with (i) projection-fixedness + nonzero + eigenvector
at `E = hhafMinEnergy`, (ii) minimality over `hhafRealSpectrum`, (iii) **uniqueness**
(`hhafRestrictedMatrix_ground_finrank_le_one`: the restricted ground eigenspace is one-dimensional —
at `E < −2` the single-`±` block is vacated since its eigenvalues are `≥ −2`, and the balanced block
contributes the 1-D PF ground state via the injective restriction `R` into the balanced block
eigenspace), lifted to the operator via `hhafSubspaceEmbedding_of_projFixed` +
`hhafRestrictedMatrix_mulVec_of_projFixed_eig` + `finrank_le_one_iff`, (iv) the positive gap
(`exists_hhaf_positive_gap`), and (v) exponential decay (`hhaf_correlation_exp_decay_exists`). For
the spin-1 chain (`N=2`, configs `Fin L → Fin 3`, `σ_x=0/1/2 ↦ +1/0/−1`), a config has **complete
hidden AFM order** (`IsHiddenAFMConfig`, via `IsPM`/`InCyclicOpen`/`IsNextPM`) when the nonzero
(`±`) spins strictly alternate around the ring with arbitrary `0`-spins between (eq. 6.3.9). `H_HAF`
= span of those basis states; `hhafProjection` (diagonal projection),
`hhafRestrictedChainHamiltonianS = P_HAF·Ĥ·P_HAF`, `hhafRealSpectrum` (eigenvalues with `H_HAF`
eigenvectors). For even `L>0`, the restricted chain has a **unique ground state**, a **finite gap**
(`gap>0` in the `H_HAF`-restricted spectrum), and **exponentially decaying** correlation
`\|chainCorrelation\| ≤ C e^{−d(x,y)/ξ}` (`ringDist`) — so the Haldane conjecture for `S=1` holds
rigorously within this artificial subspace. Proof: path-integral / 2D classical stat-mech.
**Spectral foundations now proved** (infrastructure for the now-proved theorem, Issue #4718):
`hhafProjection_isHermitian` (P_HAF Hermitian), `hhafProjection_mul_self` (P_HAF idempotent),
`afmHeisenbergChainHamiltonianS_isHermitian` (defined in `HaldaneConjecture.lean`),
`hhafRestrictedChainHamiltonianS_isHermitian` (compressed `P_HAF·Ĥ·P_HAF` Hermitian).
**Ground-energy existence now proved**: `hhafConfig` (hidden-AFM config subtype),
`hhafRestrictedMatrix` (H_HAF×H_HAF submatrix, Hermitian), `hhafSubspaceEmbedding` (zero-extension)
with the compression–embedding intertwining `P_HAF·Ĥ·P_HAF ∘ emb = emb ∘ restMat`, and
`hhafMinEnergy`/`hhafMinEnergy_mem_realSpectrum` (the minimal restricted eigenvalue is a genuine
`hhafRealSpectrum` member with a nonzero H_HAF ground state), and `exists_hhaf_min_real_eigenvalue`
(it is `≤` every restricted eigenvalue, so a genuine restricted **ground energy** with minimality).
**Per-L exp-decay** proved (`exp_decay_envelope_of_finite`/`hhaf_correlation_exp_decay_exists`): on
the finite ring any state's correlation admits `|⟨Ŝ_x·Ŝ_y⟩| ≤ C e^{−d/ξ}` (ξ=1, C=Σ|corr|e^{d}) —
the decay clause of Prop 6.5 (now all clauses proved). **Max-energy infra** added:
`hhafRestrictedMatrix_eigenvalue_mem_realSpectrum` (every restricted-matrix eigenvalue embeds into
`hhafRealSpectrum`), `hhafMaxEnergy` + `hhafMaxEnergy_mem_realSpectrum`;

**spectral completeness/finiteness** (`hhafRealSpectrum_restrict` reverse bridge,
`hhafRealSpectrum_subset_eigenvalue_range` via mathlib `spectrum_real_eq_range_eigenvalues`,
`hhafRealSpectrum_finite`) — the restricted spectrum IS the finite restricted-matrix eigenvalue set.
**Diagonal bounds**: new general `HermitianVariationalUpperBound` (max-Rayleigh) +
`hhafMinEnergy_le_diag`/`diag_le_hhafMaxEnergy` give `hhafMinEnergy ≤ (restMat σ σ).re ≤
hhafMaxEnergy` via Rayleigh at the basis vector (toward non-scalarity for the gap). **Non-scalarity
PROVED**: `hhafMinEnergy_lt_hhafMaxEnergy` (even L≥2) via all-zero config (diag=0) and domain-wall
config σ=[0,2,1,…,1] (HAF, diag<0); general formula `hhaf_diag_eq_succ_sum` (diag = Σ_x
(1-σx)(1-σ_{x+1})). **Positive gap PROVED**: `exists_hhaf_positive_gap` (even L>0) — first-excited
eigenvalue E₁ = (eigenvalues image filtered above min).min with E₁ ∈ spectrum, E₁ > minEig (gap>0),
and minimal among spectrum elements above minEig (via completeness). These foundations feed the
now-discharged uniqueness clause. **PF real-form foundation** started:
`hhafRestrictedMatrix_im_zero` (entries real), `hhafRestrictedMatrixReal` (real symmetric form) +
`hhafRestrictedMatrixReal_ofReal`/`_isSymm` — the entry point for the Perron-Frobenius uniqueness
route (Marshall gauge (now built: `ringSublattice`, `hhafDressedMatrix`, `hhafDressedMatrix_eq` =
ε(σ)ε(τ)·M_real via the dressed-Heisenberg machinery) + **symmetrized-coupling infra** for the
off-diagonal sign step (`heisenbergHamiltonianS_coupling_swap`: the Heisenberg Hamiltonian is
invariant under transposing the coupling, via `spinSDot_comm`; `ringCouplingSym` = `ringCoupling +
ringCouplingᵀ` with `_symm`/`_im_zero`/`_re_nonneg`; `heisenbergHamiltonianS_ringCouplingSym`:
`H(ringCouplingSym) = 2·H(ringCoupling)`, so the directed ring Hamiltonian equals ½ the
symmetric-coupling one — letting the symmetric-coupling off-diagonal nonpositivity lemma apply) —
**off-diagonal nonpositivity now PROVED**: `ringCouplingSym_bipartite` (even ring `L` is bipartite
w.r.t. `ringSublattice`: for even `L`, `(a+1)%L` flips parity, so equal-parity sites are never
adjacent — via `Nat.mod_mod_of_dvd`), `dressedHeisenbergS_ringCoupling_re_eq_half` (dressed directed
= ½ dressed symmetric), and `hhafDressedMatrix_offdiag_nonpos` (even `L`: `hhafDressedMatrix σ τ ≤
0` for `σ ≠ τ`, via the symmetric-coupling nonpositivity lemma) — the diagonal `±1` Marshall gauge
makes the AFM off-diagonals sign-definite. **Symmetry + nonneg shift now PROVED**:
`hhafDressedMatrix_isSymm` (the dressed matrix is symmetric), `hhafDressedMatrix_diag_eq` (diagonal
= real restricted diagonal, since the Marshall sign squares to `1`),
`hhafDressedMatrix_diag_le_hhafMaxEnergy` (diagonal ≤ max energy), and `hhafShifted_entry_nonneg`
(for `c ≥ hhafMaxEnergy` and even `L`, the shifted matrix `c·I − M` has nonnegative entries — the
nonnegativity hypothesis of `perronFrobenius_real_symmetric`). **Irreducibility started** (Issue
#4732, Gómez-Santos kink ergodicity): `hhafShifted_pos_of_ladderStep` — two hidden-AFM configs
differing by one adjacent raise/lower (ladder) move on a bipartite bond have a strictly positive
shifted entry `(c·I − M) τ σ > 0` (reusing
`dressedHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness` on `ringCouplingSym` + the ½ scaling),
the single-edge positivity for the Perron–Frobenius reachability argument. **Ring bond graph**
added: `hhafRingGraph` (cyclic nearest-neighbour graph on `Fin L`), with
`hhafRingGraph_adj_sublattice_ne` (bipartite w.r.t. `ringSublattice` for even `L`) and
`ringCouplingSym_re_pos_of_ringGraph_adj` (the symmetrized coupling is strictly positive on every
edge) — the bond-graph data feeding the per-step positivity. **HAF reachability + walk→power**
added: `RaiseLowerStepSHhaf` / `RaiseLowerReachableSHhaf` (single HAF-preserving ladder move / its
reflexive-transitive closure), `hhafShifted_pos_of_stepHhaf` (each step gives a strictly positive
shifted entry), and `exists_matrixPow_apply_pos_of_hhafReachable` (HAF-reachability ⇒ some power
`(c·I − M)^k` is strictly positive — the walk→power bridge, mirroring the magnetization-sector
version). **Kink-reduction setup** added: `hhafCanonical` (the all-`0`-spin configuration, defined
in `HiddenAntiferromagneticOrder.lean` where it is also the vanishing-diagonal witness, and reused
here as the kink-reduction base case), `pmCount` (number of `±` spins, the induction measure),
`pmCount_eq_zero_iff` (no `±` spins ⟺ canonical). **Slide move** added: `slidePM` (move the spin at
`a` onto a cyclic neighbour `b`, leaving a `0` at `a`), with `slidePM_apply` (its pointwise values)
and `slidePM_isRaiseLowerStep` (it is a single raise/lower ladder step on the ring-graph bond `{a,
b}` when `a` carries a `±` spin and `b` carries a `0`). **Slide preserves hidden-AFM order PROVEN**
(the kink-ergodicity core): `slidePM_isHiddenAFM` — sliding a `±` spin onto its `0`-carrying cyclic
successor keeps the strict `+,−,…` alternation, proved by transferring each `IsNextPM` pair of the
moved configuration back to one of `σ` (relabelling `b ↦ a`) via the open-arc decomposition lemmas
`inCyclicOpen_succ_left_imp` / `inCyclicOpen_succ_right_imp` / `notInCyclicOpen_succ` (each an
`omega` calculation after splitting the cyclic wrap). **Slide lifted to a subtype step**
(`slidePM_isRaiseLowerStepSHhaf`) and the **annihilation move** added: `annihPM` (set adjacent `a,
b` both to `0`), `annihPM_apply`, and `annihPM_isRaiseLowerStep` (it is a single ladder step when
`a, b` carry opposite `±` spins). **Annihilation preserves hidden-AFM order PROVEN**:
`annihPM_isHiddenAFM` — removing an adjacent opposite-sign `+,−` pair keeps the alternation (each
`IsNextPM` pair of the annihilated config either avoids the removed pair, giving an `IsNextPM` pair
of `σ`, or straddles it, where the chain `x, a, b, y` forces opposite endpoint signs), via the
sub-arc lemmas `inCyclicOpen_succ_iff_mem` / `inCyclicOpen_sub_left` / `inCyclicOpen_sub_right` /
`notInCyclicOpen_succ_right` / `notInCyclicOpen_pred_left`. **Move-count behaviour** added:
`annihPM_isRaiseLowerStepSHhaf` (annihilation as a subtype step), `slidePM_pmCount_card` (sliding
preserves the `±` count), `annihPM_pmCount_card_lt` (annihilation strictly decreases it).
**CONNECTIVITY PROVEN** (the kink-ergodicity theorem): the reduction measure `hhafS = Σ_{± spins}(L
− x)` strictly decreases under a slide (`slidePM_hhafS_lt`, non-wrapping successor) and an
annihilation (`annihPM_hhafS_lt`); `hhaf_single_step` produces, for any balanced (even-`pmCount`)
non-canonical config, a single HAF ladder move to another balanced config of smaller measure (first
`±` spin at `p ≤ L−2`, sliding past a `0` or annihilating an adjacent opposite `±`);
`hhaf_reachable_to_canonical` / `hhaf_reachable_canonical` (strong induction on `hhafS`) then show
**every balanced hidden-AFM configuration is HAF-reachable from the canonical all-`0`
configuration** (with `RaiseLowerReachableSHhaf_symm` for the reverse). **Design note**: the *full*
HAF matrix is reducible — a single-`±` config (`pmCount = 1`, magnetization `±1`) is vacuously
hidden-AFM but unreachable from `canonical` (the moves conserve magnetization), so irreducibility
holds only within the balanced (charge-`0`) sector; this is the sector containing the
antiferromagnetic ground state. **Balanced-sector block irreducibility PROVEN**: `hhafConfig0` (the
even-`pmCount` subtype) with `hhafShiftedMatrix0` (the `c·I − M` block),
`hhaf_reachable_to_canonical0` / `RaiseLowerReachableSHhaf0_symm` (balanced-sector connectivity
lifted to the subtype), `exists_matrixPow_apply_pos_of_hhafReachable0` (subtype walk→power), and
`hhafShiftedMatrix0_isIrreducible` — for even `L` and shift `c > hhafMaxEnergy`, the balanced-sector
shifted matrix is Perron–Frobenius irreducible (`isIrreducible_iff_exists_pow_pos`: nonnegative +
entrywise-positive power, with the diagonal handled by the strict shift `c > hhafMaxEnergy`).
**Balanced-sector unique ground state PROVEN**: `hhafDressedMatrix0` (the dressed block on
`hhafConfig0`), `hhafDressedMatrix0_isSymm` (submatrix of a symmetric matrix),
`hhafShiftedMatrix0_eq` (`hhafShiftedMatrix0 = c·I − M₀`, the identity restricting since
`Subtype.val` is injective), and `hhafDressedMatrix0_ground_finrank_le_one` — applying
`perronFrobenius_real_symmetric` to the balanced block yields a strictly positive lowest eigenvector
with a **one-dimensional** ground eigenspace: the unique ground state of the AFM chain *within the
balanced (charge-`0`) sector* of `H_HAF`. **Marshall-gauge transfer DONE**:
`hhafRestrictedMatrixReal0` (undressed real balanced block), `hhafMarshallDiag0` (the `±1` Marshall
sign diagonal, squaring to `1`), `hhafDressedMatrix0_eq_conj` (`M₀ = Θ·M_real₀·Θ`), and
`hhafRestrictedMatrixReal0_ground_finrank_le_one` — transferring the **full Perron–Frobenius data**
(nonzero lowest eigenvector `Θv`, ground minimality, and `finrank ≤ 1`) through the Marshall
similarity (the generic `matrix_similar_eigenspace_finrank_eq`, now generalised from `ℂ` to any
field), so the **undressed** real balanced block also has a one-dimensional ground eigenspace with
an explicit minimal eigenvector. Remaining for the *global* ground-state uniqueness: the
inter-sector energy ordering (balanced sector strictly lowest, a Marshall–Lieb–Mattis statement
within `H_HAF`). **Néel witness** added (toward that ordering): `hhafNeel` (the maximally-AFM
configuration `+1` on even sites, `−1` on odd), `hhafNeel_isHiddenAFM` (it is hidden-AFM on an even
ring — all sites are `±`, every `IsNextPM` pair is cyclically adjacent hence opposite parity, via
`inCyclicOpen_succ_mem_of_ne`), `hhafNeel_pmCount` (`±`-count `= L`), and `hhafNeelConfig0` (the
Néel configuration as a balanced charge-`0` configuration). **Ground energy ≤ −L PROVEN**:
`hhafNeel_diag` (the Néel diagonal energy is `−L`, every nearest-neighbour bond antiferromagnetic
`(+1)(−1) = −1`) and `hhafMinEnergy_le_neg_L` (the global restricted ground energy `hhafMinEnergy ≤
−L`, via the Rayleigh quotient `hhafMinEnergy_le_diag` at the Néel state) — the first half of the
inter-sector ordering (the balanced sector reaches energy `−L`; the remaining half bounds the
magnetization-`±1` single-`±` sectors above this). Toward that bound:
`hhaf_diag_eq_zero_of_pmCount_one` — a single-`±` configuration has **vanishing diagonal energy**
(every nearest-neighbour bond has a `0`-spin endpoint since only one site is `±`), the
Gershgorin-disc centre for the magnetization-`±1` sectors. `spinSDot_re_abs_le_one_raising_lowering`
/ `spinSDot_re_abs_le_one_lowering_raising` — the spin-`1` ladder off-diagonal amplitude
`|⟨σ'|Ŝ_x·Ŝ_y|σ⟩| ≤ 1` (each `√` factor `≤ √2` for `N = 2`), the Gershgorin-disc radius ingredient.
`hhafDressedMatrix_abs_le_ringCouplingSym` — for two hidden-AFM configs related by a single ladder
move on a bond `{x, y}`, the dressed off-diagonal entry satisfies `|M σ τ| ≤ (ringCouplingSym x
y).re` (the Marshall signs are `±1`, the Heisenberg element is `ringCouplingSym · spinSDot`, and the
ladder amplitude is `≤ 1`). **Magnetization-`±1` sector min `≥ −2` PROVEN** (codex insight: the
cyclic `IsHiddenAFMConfig` forbids odd `pmCount > 1`, so the only HAF sectors are balanced `Sz=0`
(even `pmCount`) and single-`±` `Sz=±1` (`pmCount = 1`) — there are **no higher-`Sz` sectors**,
dissolving the inter-sector Lieb–Mattis wall): `hhafConfigPM1` (the `pmCount = 1` subtype) with
`hhafDressedMatrixPM1` (dressed block), `hhafPM1Site` (the unique `±` site, computed via
`Finset.min'` so `Finset.image` reductions stay light), `hhafPM1_coupling_imp` (a nonzero
off-diagonal forces `τ` to be the slide `slidePM` of `σ`'s `±` spin to its new site, sharing the `±`
value by magnetization conservation `magEigenvalueS_eq_iff`), `hhafDressedMatrixPM1_offdiag_le`
(per-entry bound `≤ ringCouplingSym`), `hhafPM1Site_injOn_support` (the `±`-site map is injective on
the coupling support), `ringCouplingSym_re_row_sum` (`∑_t (ringCouplingSym s t).re = 2`, the two
incident directed ring bonds), the generic `sum_comp_le_sum_univ_of_injOn` (injective-on-support
reindex avoiding a heavy concrete `Finset.univ`), and `hhafDressedMatrixPM1_rowSum_le_two` ⟹
`hhafDressedMatrixPM1_eigenvalue_ge` (Gershgorin `eigenvalue_mem_ball`, diagonal `0` + row sum `≤
2`: every single-`±` eigenvalue `≥ −2`) — the single-kink tight-binding lower bound placing the `Sz
= ±1` sectors above the balanced ground energy (`≤ −L ≤ −2`). **Balanced ground energy `< −L` STRICT
PROVEN** (`hhafDressedMatrix0_ground_lt_neg_L`): the Perron–Frobenius lowest eigenvector `v > 0`
paired with the Néel row gives `μ·v(Néel) = −L·v(Néel) + Σ_{τ≠Néel} M₀(Néel,τ) v(τ)`; every
off-diagonal term is `≤ 0` (`hhafDressedMatrix0_offdiag_nonpos`) and the annihilation neighbour
(`hhafNeel_step_neighbor`, annihilating the adjacent opposite-`±` pair at sites `0,1`) is strictly
`< 0`, so via the generic row inequality `row_sum_mul_lt_diag_mul_of_offdiag_nonpos_exists_neg` and
`hhafDressedMatrix0_Neel_diag` (`M₀(Néel,Néel) = −L`) we get `μ·v(Néel) < −L·v(Néel)`, hence `μ <
−L`. Since `−L ≤ −2`, the balanced sector lies **strictly** below the magnetization-`±1` sectors
with **no `L=2` tie** — the inter-sector ordering is complete. **Sector classification PROVEN**
(`hhaf_pmCount_eq_one_or_even`): every hidden-AFM configuration has `pmCount = 1` or even `pmCount`
— an odd count `≥ 3` is impossible. Proof: the `±` sites read in increasing index order are pairwise
`IsNextPM` (`hhaf_isNextPM_consecutive` — no `±` spin lies strictly between index-adjacent `±`
sites, via `orderEmbOfFin`), so their signs strictly alternate (`hhaf_pm_alternates`: the `i`-th `±`
value is the `0`-th when `i` is even and its complement `2 - ·` when odd, `pm_flip`); and the
maximal/minimal `±` sites are also `IsNextPM` (`hhaf_isNextPM_wrap` — the cyclic wrap arc holds no
`±` spin), which would force the first and last `±` signs to *differ* while the linear alternation
makes them *equal* at odd count — contradiction. The magnetization corollaries
`hhaf_magSumS_eq_L_of_even` (even `pmCount ⟹ magSumS = L`, via `magSumS`-invariance under HAF ladder
moves `magSumS_eq_of_hhafReachable` + reachability from canonical) and
`hhaf_magSumS_ne_L_of_pmCount_one` (single-`±` ⟹ `magSumS = L ± 1 ≠ L`) identify the sectors:
balanced `= Sz 0`, single-`±` `= Sz ±1`, with no higher sectors — the cross-sector vanishing
(magnetization conservation) needed to split a ground eigenvector into balanced + single-`±` blocks.
**Magnetization-block structure of the restricted matrix PROVEN**:
`hhafRestrictedMatrix_eq_zero_of_magSumS_ne` (entries between different-`magSumS` configurations
vanish — magnetization conservation); the generic slice `hhafRestrictedMatrixSlice P` (submatrix on
`{σ // P σ}`) with `hhafRestrictedMatrixSlice_mulVec_of_full_eigen` (a full eigenvector restricted
to a block-closed `P`-slice is a `P`-slice eigenvector with the same eigenvalue); and the two
block-closures `hhafRestrictedMatrix_pmCount_one_block_closed` /
`hhafRestrictedMatrix_even_block_closed` (via the classification: a single-`±` config couples only
to single-`±`, an even config only to even) — the block-diagonal decomposition into the balanced and
single-`±` blocks, the structural input for the ground-eigenspace `finrank ≤ 1`. **Per-block
spectral bounds PROVEN**: the complex blocks are the real blocks cast to `ℂ`
(`hhafRestrictedMatrix_submatrix0_eq_map` / `hhafRestrictedMatrix_submatrixPM1_eq_map`, entries
real); `hhafRestrictedMatrix_submatrix0_eigenspace_finrank_le_one` — the **complex balanced block
ground eigenspace is one-dimensional** (real→complex bridge
`matrix_complex_eigenspace_finrank_le_one_of_real` from the real balanced Perron–Frobenius `finrank
≤ 1`); and `hhafRestrictedMatrix_submatrixPM1_eigenvalue_ge` — the **complex single-`±` block has
all eigenvalues `≥ −2`** (an eigenvalue is real, its re/im part is a real-block eigenvector,
transferred to a dressed-block eigenvector via the Marshall conjugation
`hhafDressedMatrixPM1_eq_conj` where the Gershgorin bound `≥ −2` applies). These are the per-block
spectral inputs: at the ground energy `E < −2` the single-`±` block is vacated and the balanced
block contributes the unique ground state. **Reverse block restriction PROVEN**: `hhafSliceExtend P`
(zero-extension of a `P`-slice vector to all of `hhafConfig`) with `hhafSliceExtend_ne_zero` and
`hhafRestrictedMatrix_mulVec_hhafSliceExtend` (if there is no coupling *into* a `P`-slice from its
complement, the zero-extension of a `P`-slice eigenvector is a full eigenvector at the same
eigenvalue) — the reverse counterpart of the forward slice restriction, used to lift the balanced
Perron–Frobenius eigenvector to a full restricted-matrix eigenvector (so the balanced ground energy
is in the restricted spectrum). (The Perron–Frobenius uniqueness development — kink moves through
the Marshall transfer, the magnetization-`±1` Gershgorin bound, and the strict balanced ground
energy — lives in the companion `Quantum/SpinS/HiddenAntiferromagneticOrderUniqueness.lean`, with
its combinatorial kink-move/balanced-sector core split off into
`Quantum/SpinS/HiddenAntiferromagneticOrderUniquenessCore.lean` for build speed.)
<!-- legacy-detail:end:748 -->

<a id="record-759"></a>
## Record from former line 759

**Lean name:** <!-- legacy-detail-lean:start:759 -->`bondSpin2ProjectionS` / `bondLocal_ker_eq_vbsBondSubspace` / `bondSpin2ProjectionS_mulVec_eq_zero_iff_bondSlice_mem_ker` / `tasaki_lemma_7_4`<!-- legacy-detail-lean:end:759 -->

**File:** <!-- legacy-detail-file:start:759 -->`Quantum/SpinS/AKLTBondProjection.lean`<!-- legacy-detail-file:end:759 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:759 -->
**§7.1.3 Lemma 7.4** (local VBS ground-state characterization;

**PROVED**, `#print axioms` = std3, PR #5087; Tasaki, 1st ed. (2020), Lemma 7.4, eqs.
(7.1.19)–(7.1.21), pp. 186–187): for `1 < L`, a state `Φ` is annihilated by the periodic bond
projection, `P̂₂[Ŝ_x+Ŝ_{x+1}] Φ = 0`, **iff** it has the valence-bond-solid singlet-tensor form on
that bond (`IsVBSGroundForm`). The concrete predicate is independent of `P̂₂`: every
fixed-rest-configuration two-site slice `bondSlice x Φ τ` must lie in the span `W = vbsBondSubspace`
of the four vectors `vbsBondVec σ σ'`. The local proof first gives `finrank W = 4` from
`vbsBondVec_linearIndependent`. Five independent fixed vectors in the range of `P̂₂^{loc}` prove
`rank P̂₂^{loc} ≥ 5`; the intermediate inclusion `W ⊆ ker P̂₂^{loc}`, together with `finrank W = 4`,
ambient dimension `9`, and rank–nullity, proves `rank P̂₂^{loc} ≤ 5`. Thus `rank P̂₂^{loc} = 5`,
rank–nullity gives `finrank (ker P̂₂^{loc}) = 4`, and the equal dimensions upgrade the intermediate
inclusion to `ker P̂₂^{loc} = W`. The pointwise identity `bondSlice_bondSpin2ProjectionS_mulVec`
identifies the slice of the global bond action with the local `9×9` action for every `x` and `τ`.
Consequently, `bondSpin2ProjectionS_mulVec_eq_zero_iff_bondSlice_mem_ker` characterizes global
annihilation by membership of every slice in the local kernel, uniformly for the periodic wrap bond
and for both ordered bonds when `L = 2`. Rewriting that local kernel as `W` gives `tasaki_lemma_7_4`
with the same public statement as the former axiom. The separate affine identity
`aklt_bond_term_eq_bondSpin2Projection` (**PROVED**, eq. (7.1.5), p. 181) relates the AKLT local
term to `P̂₂`, but the theorem itself uses only the local kernel equality and the global slice
equivalence. Proof: explicit finite-dimensional linear algebra and tensor-slice reduction. The
entry-level spin-1 formulas used by the `9×9` computations were moved to the shared module
`Quantum/SpinS/SpinOneTwoSiteEntries.lean` (PR #5095) so that the Knabe-type gap estimates can reuse
them without duplicating declarations. The bond change of variables `glueBond` / `bondSlice` is the
specialization of the shared two-site gluing `glueTwoSitesS` / `twoSiteSliceS`
(`Quantum/SpinS/TwoSiteConfig.lean`) to the periodic ring bond `{x, ringSucc x}`, and `ne_ringSucc`
(`x ≠ ringSucc x` for `1 < L`) now sits next to `ringSucc` itself (PR #5139)
<!-- legacy-detail:end:759 -->

<a id="record-763"></a>
## Record from former line 763

**Lean name:** <!-- legacy-detail-lean:start:763 -->`bondFactor` / `weylMap` / `fBond` / `fBond_dvd_weylMap_of_isVBSGroundForm` / `weylMap_ground_form_eq_const_smul_prod` / `ground_eigen_isVBSGroundForm` / `aklt_ring_ground_state_unique`<!-- legacy-detail-lean:end:763 -->

**File:** <!-- legacy-detail-file:start:763 -->`Quantum/SpinS/AKLTUniqueness/GroundStateUnique.lean`; `Quantum/SpinS/AKLTUniqueness/ProductBondDivisibility.lean`; `Quantum/SpinS/AKLTUniqueness/BondDivisibilityBridge.lean`; `Quantum/SpinS/AKLTUniqueness/LocalBondDivisibility.lean`; `Math/MvPolynomial/WeylSpinMap.lean`; `Math/MvPolynomial/BilinearFactorCoprime.lean`; `Math/MvPolynomial/PairwiseCoprimeProd.lean`<!-- legacy-detail-file:end:763 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:763 -->
**§7.1.3 The uniqueness of the AKLT ground state** (**PROVED**, `#print axioms` = std3, PR #5128;

Tasaki, 1st ed. (2020), §7.1.3, Lemma 7.4, eqs. (7.1.22)–(7.1.25), pp. 186–188;

proof due to Kennedy–Lieb–Tasaki [41], polynomial representation Arovas–Auerbach–Haldane [10]): the
capstone `aklt_ring_ground_state_unique` proves the **uniqueness conjunct** (§7.1.3) of Tasaki
Theorem 7.1 as an independent theorem — for every ring `L = n+1 ≥ 3`, any nonzero eigenvector `Ψ` of
`akltHamiltonianS L` at the ground energy `−(2/3)L` satisfies `∃ c, Ψ = c • akltVBSState L` (the
ground space is one-dimensional). This is conjunct (4) of Tasaki Theorem 7.1;

it is composed with the existence/gap (§7.1.4) and correlation (§7.2.2) conjuncts into the
now-`theorem` `aklt_theorem_7_1` (`AKLTTheorem71.lean`, PR #5131). The proof follows Tasaki's Weyl
(Schwinger-boson) / UFD route. **Spectral bridge** `ground_eigen_isVBSGroundForm`
(frustration-freeness, Lemma A.10): the affine identity `Ĥ_AKLT = 2Ĥ′ − (2/3)L` turns the
eigen-equation into `Ĥ′ Ψ = 0`, so `Ψ` is a zero mode of every bond projection
(`frustration_free_local_eigen`), hence `IsVBSGroundForm L x Ψ` at every bond (Lemma 7.4). **Stage C
polynomial machinery** (recovered infra): the Weyl map `weylMap`, at `N = 2` of type
`((Fin L → Fin 3) → ℂ) →ₗ[ℂ]
MvPolynomial (Fin L × Fin 2) ℂ` (`Math/MvPolynomial/WeylSpinMap.lean`, eq. (7.1.22)) sends each
site's spin-1 state to a degree-2 monomial in `u_x, v_x` with the essential `√2` Clebsch–Gordan
weight;

it is injective and image-homogeneous of degree `2L`. A bond singlet maps into the ideal of the
bilinear bond factor `f_x = u_x v_{x+1} − v_x u_{x+1}` (`bondFactor`,
`Math/MvPolynomial/BilinearFactorCoprime.lean`: `bondFactor_prime`, `bondFactor_isRelPrime`,
`eq_const_smul_of_dvd_of_totalDegree_eq`);

the local-to-global bond-divisibility bridge `fBond_dvd_weylMap_of_isVBSGroundForm`
(`Quantum/SpinS/AKLTUniqueness/LocalBondDivisibility.lean`,
`Quantum/SpinS/AKLTUniqueness/BondDivisibilityBridge.lean`) gives `f_x ∣ weylMap Ψ` for each bond.
**Stage C capstone** `weylMap_ground_form_eq_const_smul_prod`: distinct cyclic bonds are relatively
prime (`fBond_isRelPrime`, via the double-shift combinatorics `ringSucc_ringSucc_ne` valid for `L ≥
3` — coprimality breaks at `L = 2`), so `∏_x f_x ∣ weylMap Ψ` (`prod_dvd_of_pairwise_isRelPrime`);

matching total degrees `2L = 2L` (`totalDegree_prod_of_isDomain`, eq. (7.1.25)) force `weylMap Ψ = C
c · ∏_x f_x`. Applying this to `Ψ` and to `akltVBSState L` (whose Weyl image is nonzero, so `c₀ ≠
0`) and cancelling the common product gives `weylMap Ψ = weylMap ((c/c₀) • akltVBSState L)`;

injectivity of `weylMap` concludes `Ψ = (c/c₀) • akltVBSState L`. Proof: finite-dimensional spectral
theory + multivariate-polynomial UFD factorization (no operator algebra, no infinite volume).
<!-- legacy-detail:end:763 -->

<a id="record-764"></a>
## Record from former line 764

**Lean name:** <!-- legacy-detail-lean:start:764 -->`expectationRatioRe_sum` / `spinSDot_eq_sum_component` / `aklt_correlation_decay`<!-- legacy-detail-lean:end:764 -->

**File:** <!-- legacy-detail-file:start:764 -->`Quantum/SpinS/AKLTCorrelationDecay.lean`; `Quantum/SpinS/AKLTStringOrderTransfer.lean`; `Quantum/SpinS/AKLTStringOrderCovariance.lean`<!-- legacy-detail-file:end:764 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:764 -->
**§7.2.2 The exponential decay of the AKLT correlation function** (**PROVED**, `#print axioms` =
std3, PR #5130;

Tasaki, 1st ed. (2020), §7.2.2, eqs. (7.2.26)–(7.2.34), pp. 197–200, and eq. (7.1.2), p. 178): the
capstone `aklt_correlation_decay` proves the **correlation-function conjunct** (§7.1.2 / §7.2.2) of
Tasaki Theorem 7.1 as an independent theorem — for the explicit periodic valence-bond-solid state
`akltVBSState (n+1)` and any two fixed sites `x, y : ℕ` with `1 ≤ Nat.dist x y`, the ground-state
Rayleigh quotient of `Ŝ_x · Ŝ_y` decays with alternating sign, `⟨Φ, Ŝ_x·Ŝ_y Φ⟩/⟨Φ,Φ⟩ → 4
(−3)^{−|x−y|}` as the ring length `L = n+1 ↑ ∞` (sound eventual-`ε` form, fixed `ℕ`-sites embedded
by `chainSite`). This is the correlation conjunct (6) of Tasaki Theorem 7.1. With this theorem, all
four assertions of Theorem 7.1 are discharged as standalone theorems — existence + gap
(`aklt_knabe_ring_gap`, §7.1.4), uniqueness (`aklt_ring_ground_state_unique`, §7.1.3), and
correlation decay (`aklt_correlation_decay`, §7.2.2) — and composed into the now-`theorem`
`aklt_theorem_7_1` (`AKLTTheorem71.lean`, PR #5131), which is thereby fully axiom-free (`#print
axioms` = std3). The proof is the string-free specialization of the §7.2.1 string-order calculation:
the plain axis-three transfer contraction `Tr[Ã^a B̃ Ã^b B̃ Ã^c]` (interior `phaseTransfer` replaced
by `ordinaryTransfer`, `endpoint_ordinary_endpoint_closed`, eq. (7.2.31)) gives the exact finite
numerator `−¼[(3/4)^b(−1/4)^{a+c} + (−1/4)^b(3/4)^{a+c}]`;

dividing by the norm `(3/4)^L + 3(−1/4)^L` and taking `L↑∞` (the outer eigenvalue power cancels)
gives the axis-three limit `(4/3)(−1/3)^{|x−y|}` (`Internal.plainAxis3Epsilon`, eq. (7.2.33));

the single-site rotation covariance of the VBS state
(`Internal.spinComponentCorrelation_akltVBSState_eq_three`, eq. (7.2.34)) makes the three axes
equal, so `expectationRatioRe (spinSDot ..) = 3 ×` the axis-three correlation
(`spinSDot_eq_sum_component` + additivity `expectationRatioRe_sum`), and `3 · (4/3)(−1/3)^r =
4(−3)^{−r}`. This direct finite-dimensional calculation has no logical dependency on the axiom
`aklt_theorem_7_1`. Proof: finite-dimensional transfer-matrix linear algebra + geometric-series
thermodynamic limit + single-site rotation covariance.
<!-- legacy-detail:end:764 -->

<a id="record-766"></a>
## Record from former line 766

**Lean name:** <!-- legacy-detail-lean:start:766 -->`mpsDualTransferMap` / `HasFaithfulDualEigenmatrix` / `mps_spans_eventually_iff_spans_for_all_large` / `mps_spans_for_all_large_iff_has_primitive_transfer_spectrum` / `mps_theorem_7_5` / `GeneratesSameMPS` / `mps_theorem_7_6`<!-- legacy-detail-lean:end:766 -->

**File:** <!-- legacy-detail-file:start:766 -->`Quantum/SpinS/MPSTheorem75Defs.lean`; `Quantum/SpinS/MPSTheorem75Linear.lean`; `Quantum/SpinS/MPSTheorem75Choi.lean`; `Quantum/SpinS/MPSTheorem75Peripheral.lean`; `Quantum/SpinS/MPSTheorem75.lean`; `Quantum/SpinS/MPSTheorem76Defs.lean`; `Quantum/SpinS/MPSTheorem76Algebra.lean`; `Quantum/SpinS/MPSTheorem76Unitary.lean`; `Quantum/SpinS/AKLTMatrixProduct.lean`<!-- legacy-detail-file:end:766 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:766 -->
**§7.2.2 Matrix product representation.** Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed. (Springer, 2020), §7.2.2, Theorem 7.5, eqs. (7.2.36), (7.2.41)–(7.2.42), pp.
202–203, and Theorem 7.6, eqs. (7.2.43)–(7.2.44), p. 203;

M. Fannes, B. Nachtergaele, and R. F. Werner, “Finitely correlated pure states,” *Journal of
Functional Analysis* **120** (1994), 511–534. The AKLT VBS state is an injective matrix product
state. `MPSMatrices D N = Fin(N+1)→D×D` matrices `A^σ`;

`mpsTransferMatrix A` is the concrete D²×D² transfer matrix;

`orderedProd` forms fixed-length words;

`mpsProductsSpanAt` says that those words span all D×D matrices;

`IsMPSNormalized A λ` is `λ>0` and `Σ_σ A^σ(A^σ)†=λI`;

and `HasPrimitiveTransferSpectrum A λ` says that `λ` has a one-dimensional eigenspace and every
other spectral value has norm `<λ`. The book-facing Theorem 7.5 DAG has five nodes:
`mpsDualTransferMap`, the corrected faithful condition `HasFaithfulDualEigenmatrix A λ := ∃ρ,
ρ.PosDef ∧ mpsDualTransferMap A ρ = λ • ρ`, the (i)↔(ii) span-propagation theorem, the faithful
(ii)↔(iii) transfer theorem, and `mps_theorem_7_5` (**PROVED axiom-free;

Standard 3;

merged in commit `8286635d`**). The proof handles general positive `λ` by `B^σ=λ⁻¹ᐟ²A^σ`: words
acquire a nonzero scalar, while the transfer matrix and its spectrum scale by `λ⁻¹`. Tasaki's
printed theorem omits the faithful-dual condition and supplies no proof. This omission is necessary:
for `A⁰=diag(1,a)`, `A¹=bE₂₁`, `0<a<1`, and `a²+b²=1`, the transfer spectrum is primitive but every
fixed-length word span has dimension at most two;

the only dual fixed matrices are multiples of rank-one `E₁₁`. The corrected hypothesis excludes this
example. The concrete predicate `GeneratesSameMPS A B` requires `trace (orderedProd A (List.ofFn
ss)) = trace (orderedProd B (List.ofFn ss))` for every length `L` and every `ss : Fin L → Fin
(N+1)`. Under injectivity, `mps_theorem_7_6` is **PROVED axiom-free;

Standard 3;

merged in commit `50b30949`**: there is a unitary `U` such that `B^σ = U† A^σ U`, and every unitary
`V` with the same gauge relation satisfies `V = z • U` for some `z` with `‖z‖=1`. The verified DAG
is `GeneratesSameMPS` → (`.eventually`) → `GeneratesSameMPSEventually` →
`exists_word_transport_algEquiv` → `exists_unitary_gauge_data_of_eventually` →
`exists_unitary_gauge_data` / `mps_theorem_7_6_of_eventual_agreement` → `mps_theorem_7_6`:
`exists_word_transport_algEquiv` now takes only the threshold hypothesis (agreement for all
sufficiently large lengths), fixed-length word transport gives a matrix-algebra equivalence,
normalization makes its inner implementer unitary, and the full matrix-algebra center gives
uniqueness up to phase.
<!-- legacy-detail:end:766 -->
