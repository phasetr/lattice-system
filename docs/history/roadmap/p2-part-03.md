---
layout: page
title: "Roadmap history: P2, part 3"
permalink: /history/roadmap/p2-part-03/
---

# Roadmap history: P2, part 3

> Historical implementation record normalized at semicolon-delimited bold milestones. Active work is governed by tracking Issues.

<!-- legacy-source:start:149:149 -->
- existence PR35 + uniqueness PR34) — the position-of-index bookkeeping making the double-peel (i,j)
  of a removed pair unique. **Theorem 11.17 PR37 (Issue #4363, `GeneralFlatBandSlaterReorder.lean`):
  sorted-list erase reduction** — `Finset.sort_eraseIdx_eq_sort_erase` (`(s.sort r).eraseIdx i =
  (s.erase (s.sort r)[i]).sort r`, via `List.Perm.eq_of_pairwise` + sorted-enumeration uniqueness) —
  Codex-endorsed key reducing a positional double-peel of the canonical creation list to a canonical
  list over a smaller index set, so all canonical-list machinery applies to the (D₀−2)-electron
  "rest" states. **Theorem 11.17 PR38 (Issue #4363, `GeneralFlatBandSlaterReorder.lean`):
  eraseIdx-to-canonical bridge** — `flatBandSpinConfigList_eraseIdx` (`(flatBandSpinConfigList I
  σ).eraseIdx i = flatBandSpinConfigList (I.erase L[i].1) σ`, via `List.eraseIdx_map` + PR37) — the
  inner double-peel list over the canonical creation list is itself a canonical creation list over
  the smaller index set, so the (D₀−2)-electron rest states reuse all canonical machinery. **Theorem
  11.17 refactor (Issue #4363): split `GeneralFlatBandSlaterReorder.lean`** — the canonical-list
  coordinate/config machinery (length, `generalOccMonomial_repr`, `cDownUp_canonical_repr_eq_sum`,
  `idxConfigOf`, position↔index, `flatBandSpinConfigList_eraseIdx`) moved to a new
  `GeneralFlatBandCanonicalCoord.lean` (599→364 + 264 lines, parallel build);
- the reorder/extraction machinery stays in `GeneralFlatBandSlaterReorder.lean`. **Theorem 11.17
  PR40 (Issue #4363, `GeneralFlatBandCanonicalCoord.lean`): inner peel-term coordinate** —
  `generalFlatBandPeelTerm_repr` (`repr (peelTerm μ x s qs i) g =
  (-1)^i·[qs[i].2=s]·μ_{qs[i].1}(x)·repr (Slater (qs.eraseIdx i)) g`) — the inner j-sum of the
  canonical double peel is term-wise of this form, reducing collection at g to the bridge coordinate
  of the double-erased rest Slater state. **Theorem 11.17 PR41 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): double-erase canonical bridge** —
  `flatBandSpinConfigList_eraseIdx_eraseIdx` (`((flatBandSpinConfigList I σ).eraseIdx i).eraseIdx j
  = flatBandSpinConfigList ((I.erase a).erase b) σ`, PR38 applied twice) — identifies the
  (D₀−2)-electron double-peel rest list as a canonical list over the twice-erased index set, so its
  coordinate is read off by the bridge repr. **Theorem 11.17 PR42 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): canonical-list σ-congruence** —
  `flatBandSpinConfigList_congr` (σ, σ′ agreeing on S ⟹ equal canonical lists) — on the twice-erased
  set `(I.erase a).erase b` the (D₀−2) rest list is the same for σ and the spin-swapped σ_{a↔b}, so
  the shared rest Slater state cancels in the eq.(11.3.49) comparison `D(σ)=D(σ_{a↔b})` (no
  existential sign comparison). **Theorem 11.17 PR43 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): rest coordinate nonzero at own config** —
  `generalFlatBandSlaterState_repr_self_ne_zero` (`repr (Slater μ qs) (idxConfigOf idx qs) ≠ 0`) —
  the `R ≠ 0` fact cancelled in the eq.(11.3.49) relation: the shared (D₀−2) rest Slater state has
  nonzero coordinate at the rest config, so it divides out. **Theorem 11.17 PR44 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): config determines index set** —
  `idxConfigOf_flatBandSpinConfigList_inj` (for S,S′ ⊆ I, idx inj on I, `idxConfigOf idx (canonical
  S σ) = idxConfigOf idx (canonical S′ σ) ⟹ S = S′`, by evaluating at mode (idx w, σ w)) — the
  injectivity behind "exactly one (i,j)": distinct double-peels empty distinct index pairs ⟹
  distinct target configs, so at a fixed target only the matching pair contributes to
  `cDownUp_canonical_repr_eq_sum`. **Theorem 11.17 PR45 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): erase-pair membership** —
  `Finset.eq_or_eq_of_erase_erase_eq` (generic: `c ∈ I` and `(I.erase c).erase d = (I.erase a).erase
  b ⟹ c = a ∨ c = b`) — applied to both removed indices it pins the unordered double-peel rest pair
  to `{a,b}`, disambiguating which pair a rest set came from. **Theorem 11.17 PR46 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): canonical index membership** —
  `flatBandSpinConfigList_mem_fst_mem` (`q ∈ flatBandSpinConfigList I σ ⟹ q.1 ∈ I`) — supplies the
  `∀ q ∈ qs, q.1 ∈ I` hypothesis of the bridge repr for canonical lists and their eraseIdx-derived
  rest lists. **Theorem 11.17 PR47 (Issue #4363, `GeneralFlatBandCanonicalCoord.lean`): double-peel
  index determination** — `flatBandSpinConfig_doublePeel_index_eq` (if the doubly-erased rest config
  equals the (a,b)-emptied config, with up-guard on outer i and down-guard on inner j, then the
  outer index = a and inner index = b) — combines config-injectivity (PR44) + erase-pair (PR45) +
  spin-guard disambiguation;
- the "exactly one (i,j)" engine for the collapse. **Theorem 11.17 PR48 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): single-peel index determination** —
  `flatBandSpinConfig_singlePeel_index_eq` (for S ⊆ I, if the once-erased rest config equals the
  b-emptied config then the erased index `(canonical S σ)[j].1 = b`;
- config injectivity ⟹ S.erase d = S.erase b ⟹ d = b, no spin guard needed) — the inner-sum "exactly
  one j" engine. **Theorem 11.17 PR49 (Issue #4363, `GeneralFlatBandCanonicalCoord.lean`): inner-sum
  collapse** — `flatBandSpinConfig_inner_sum_collapse` (the inner j-sum of the canonical double
  peel, evaluated at the b-emptied config, collapses via `Finset.sum_eq_single` to its single
  surviving term at the position of b: off-positions give repr=0 by single-peel determination, the
  b-position has the down-guard and rest list `canonical (S.erase b) σ`, Koszul sign `(-1)^pos_b`).
  **Theorem 11.17 PR50 (Issue #4363, `GeneralFlatBandCanonicalCoord.lean`): wrong-outer vanishing**
  — `flatBandSpinConfig_inner_sum_other_outer_zero` (if the outer-peeled index c ∉ {a,b}, the inner
  j-sum over `canonical (I.erase c) σ` at the (a,b)-emptied config is identically 0: no single peel
  can hit it without forcing c ∈ {a,b}) — the off-diagonal case of the outer sum_eq_single collapse.
  **Theorem 11.17 PR51 (Issue #4363, `GeneralFlatBandCanonicalCoord.lean`): double-peel coordinate
  collapses to a single term** — `cDownUp_canonical_repr_twoHole` (for a,b ∈ I, a≠b, σa=0, σb=1, the
  coordinate of ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I σ) at the (a,b)-emptied config = product of the two
  Koszul signs (-1)^pos_a·(-1)^pos_b, μ_a(x), μ_b(x), and the rest coordinate;
- outer sum_eq_single keeps only pos a (PR50 kills others), inner collapse PR49 at pos b). **This is
  the eq.(11.3.49) heart.** **Theorem 11.17 PR52 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): canonical position σ-independence** —
  `flatBandSpinConfigList_get_fst_eq_sort` (index at canonical position p = `(I.sort)[p]`,
  σ-independent) + `flatBandSpinConfigList_choose_eq` (the position of z ∈ I is the same in
  `canonical I σ` and `canonical I σ′`) — lets the eq.(11.3.49) Koszul signs of σ and the
  spin-swapped σ_{a↔b} be compared on common I.sort positions. **Theorem 11.17 PR53 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): two-erase Koszul sign flip** —
  `neg_one_pow_two_erase_shift` (for p ≠ q, `(-1)^(p+(q-[q>p])) = -(-1)^(q+(p-[p>q]))`;
- the two transposition-shifted exponents differ by one) — the sign engine of the comparison coord_σ
  = −coord_σ′ (p,q = I.sort positions of a,b). **Theorem 11.17 PR54 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): eraseIdx position shift** —
  `flatBandSpinConfigList_choose_erase_shift` (`pos_{I.erase a}(b) = pos_I(b) − [pos_I(b) >
  pos_I(a)]`, via `Finset.sort_eraseIdx_eq_sort_erase` + `List.getElem_eraseIdx` + sort nodup) with
  helpers `_sort_getElem_choose`/`_choose_lt_sortLength` — the position arithmetic feeding
  `neg_one_pow_two_erase_shift`. **Theorem 11.17 PR55 (Issue #4363,
  `GeneralFlatBandCanonicalCoord.lean`): two-hole coordinate sign flip** —
  `cDownUp_canonical_repr_twoHole_swap_eq_neg` (the coordinate of ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I
  σ) at the (a,b)-emptied config = − the coordinate for the spin-swapped σ′ = σ∘swap a b;
- both collapse via twoHole, rests coincide by congr, positions agree (choose_eq) + shift
  (choose_erase_shift), Koszul signs negate by neg_one_pow_two_erase_shift). **coord_σ = −coord_σ′
  DONE.** **Theorem 11.17 refactor (Issue #4363): split `GeneralFlatBandTwoHoleCollapse.lean`
  (foundational position-bookkeeping, inner-sum collapse, and two-hole sign helpers further
  extracted to `GeneralFlatBandTwoHoleCollapseCore.lean` for build speed)** — the collapse + sign
  machinery (inner-sum collapse, off-diagonal vanishing, `cDownUp_canonical_repr_twoHole`, position
  σ-independence/shift, `cDownUp_canonical_repr_twoHole_swap_eq_neg`) moved out of
  `GeneralFlatBandCanonicalCoord.lean` (805→489 + 346 lines, parallel build). **Theorem 11.17 PR57
  (Issue #4363, `GeneralFlatBandCanonicalCoord.lean`): config injectivity (σ-varying)** —
  `idxConfigOf_flatBandSpinConfigList_inj_gen` (`idxConfigOf idx (canonical S σ) = idxConfigOf idx
  (canonical S′ σ′) ⟹ S = S′ ∧ σ = σ′ on S`, by evaluating the config at every mode (idx w, s)) —
  the engine for the eq.(11.3.49) sum collapse: only spin configs agreeing with σ off {a,b} can hit
  the target config. **Theorem 11.17 PR58 (Issue #4363, `GeneralFlatBandTwoHoleCollapse.lean`):
  contributing peel forces τ ∈ {σ, σ∘swap}** — `flatBandSpinConfig_doublePeel_config_eq` (if a
  doubly-erased rest config of `Slater(canonical I τ)` hits the (a,b)-emptied target of σ with the
  peel guards, then on I either τ = σ or τ = σ∘swap a b;
- via σ-varying config injectivity + erase-pair + guard spin fix) — the determination feeding the
  sum collapse. **Theorem 11.17 PR59 (Issue #4363, `GeneralFlatBandTwoHoleCollapse.lean`): Slater
  coordinate vanishes off {σ, σ∘swap}** — `cDownUp_canonical_repr_eq_zero_of_ne` (if τ ∉ {σ, σ∘swap
  a b} on I, the (a,b)-emptied coordinate of ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I τ) = 0;
- each double-peel term vanishes via PR58 contradiction or failing guard) — the sum-collapse engine.
  **Theorem 11.17 PR60 (Issue #4363, `GeneralFlatBandTwoHoleCollapse.lean`): coordinate sum
  collapses to two terms** — `cDownUp_canonicalSum_eq_two_terms` (summing the (a,b)-emptied
  coordinate over all spin configs s:I→Fin2 weighted by D s keeps only σ|_I and (σ∘swap)|_I;
- via `Finset.sum_subset` + the vanishing PR59 + `Finset.sum_pair`). **Theorem 11.17 PR61 (Issue
  #4363, `GeneralFlatBandTwoHoleCollapse.lean`): eq.(11.3.49) Marshall-sign relation PROVEN** —
  `flatBand_groundState_D_swap_eq` (for a flat-band ground state Φ = Σ_s D s • Slater(canonical I
  (extend s)) and a connected pair a,b ∈ I (site x with μ_a(x)≠0, μ_b(x)≠0), σa=0, σb=1: `D σ = D
  σ_{a↔b}`). Acting ĉ_{x,↓}ĉ_{x,↑} kills Φ;
- the (a,b)-emptied coordinate collapses (PR60) to the two configs, whose coordinates are negatives
  (PR55) and nonzero, forcing equality. **eq.(11.3.49) DONE (axiom-free).** **Theorem 11.17 PR62
  (Issue #4363, `GeneralFlatBandConnectivity.lean`): graph-adjacent D-swap** —
  `flatBand_groundState_D_swap_eq_of_adj` (if z, z′ adjacent in the special-basis graph and σz=0,
  σz′=1, then D(σ)=D(σ_{z↔z′});
- extracts the witnessing site x from the adjacency and applies the eq.(11.3.49) relation) — the
  per-edge step of the connectivity induction. **Theorem 11.17 PR63 (Issue #4363,
  `GeneralFlatBandConnectivity.lean`): unconditional edge-swap** —
  `flatBand_groundState_D_edgeSwap_eq` (`D σ = D (σ ∘ swap z z′)` for any graph-adjacent z, z′, *no*
  spin condition: same-spin ⟹ swap is identity, else PR62) — so D is invariant under every
  edge-transposition. **Theorem 11.17 PR64 (Issue #4363, `GeneralFlatBandConnectivity.lean`):
  edge-swap as Perm action** — `flatBand_groundState_D_permSwap_eq` (`D s = D (s ∘ Equiv.swap z z′)`
  for any config s:I→Fin2 and graph-adjacent z, z′;
- the per-generator step for the S_I action). **Theorem 11.17 PR65 (Issue #4363,
  `GeneralFlatBandConnectivity.lean`): walk-swap invariance** —
  `flatBand_groundState_D_swap_eq_of_walk` (for a walk z⤳z′ in the special-basis graph, `D (s ∘ swap
  z z′) = D s`;
- walk induction decomposing swap z z′ as the conjugate swap z w · swap w z′ · swap z w, each factor
  invariant). **Theorem 11.17 PR66 (Issue #4363, `GeneralFlatBandConnectivity.lean`): full
  permutation invariance** — `flatBand_groundState_D_perm_eq` (connected ⟹ `D (s ∘ π) = D s` for
  every π ∈ Equiv.Perm I;
- the D-invariant permutations form a subgroup containing all transpositions — each via a connecting
  walk — and transpositions generate S_I by `Equiv.Perm.closure_isSwap`). **D depends only on the
  up-count.** **Theorem 11.17 PR67 (Issue #4363, `GeneralFlatBandConnectivity.lean`): D constant per
  up-count** — generic `exists_perm_comp_of_card_eq` (equal-weight Fin 2 configs differ by a
  permutation, via `Equiv.sumCompl` gluing of fiber bijections) +
  `flatBand_groundState_D_const_of_weight_eq` (connected ⟹ `D s = D s′` when s, s′ have equal
  up-count). **Theorem 11.17 PR68 (Issue #4363, `GeneralFlatBandConnectivity.lean`): ground finrank
  ≤ D₀+1** — `generalFlatBandGround_finrank_le_of_connected` (connected basis ⟹ `finrank (ground) ≤
  D₀+1`;
- every ground state lies in the span of the D₀+1 symmetric weight-states W_0..W_{D₀}, grouping the
  canonical-Slater decomposition by up-count and factoring the constant coefficient). **finrank
  upper bound DONE.** **Theorem 11.17 PR69 (Issue #4363, new `GeneralFlatBandMultiplet.lean`):
  all-up highest-weight Ŝ⁺=0** — `generalFlatBand_totalSpinPlus_mulVec_allUpSlater` (Ŝ⁺_tot
  annihilates the all-up μ-Slater state `Slater(canonical I (fun _ => 0))`;
- each ĉ_{i,↓} kills it via `generalFlatBand_siteAnnihilation_eq_zero`) — the highest-weight
  condition for the SU(2) tower. **Theorem 11.17 PR70 (Issue #4363,
  `GeneralFlatBandMultiplet.lean`): N̂_tot diagonal on Slater** —
  `fermionTotalNumber_mulVec_generalFlatBandSlaterState` (`N̂_tot Slater(μ,qs) = |qs|·Slater`;
- list induction via `fermionTotalNumber_mul_spinfulCreationFromVector`) — the filling input toward
  Ŝᶻ = D₀/2. `fermionTotalNumber_eq_up_add_down` (N̂_tot = N̂_↑ + N̂_↓ via `sum_spinful_reindex`) +
  `fermionTotalDownNumber_mulVec_allUpSlater` (N̂_↓ kills the all-up Slater) give
  `generalFlatBand_totalSpinZ_mulVec_allUpSlater` (Ŝᶻ_tot eigenvalue |I|/2 on the all-up μ-Slater) —
  the second SU(2) highest-weight input for `highestWeight_spinMultiplet_general` (PR #4436).
  `generalFlatBandSlaterState_allUp_ne_zero` (the all-up μ-Slater is nonzero, via its nonzero
  self-coordinate `generalFlatBandSlaterState_repr_self_ne_zero`) supplies the `hv` nontriviality
  hypothesis (PR #4437).
  `spinfulAnnihilationFromVector_mulVec_generalFlatBandSlaterState_eq_zero_of_orthogonal` (a smeared
  annihilation `Ĉ_σ(φ)` kills a μ-Slater when every occupied mode is φ-orthogonal, `Σ_x
  φ(x)μ_{q.1}(x)=0`;
- site-peel + overlap collapse) — the kinetic building block toward the all-up μ-Slater being a
  flat-band ground state (PR #4438). `hubbardKinetic_mulVec_allUpSlater_eq_zero` (kinetic kill:
  T=CᴴC, μ_z∈ker T=ker C ⟹ each Gram-mode `Ĉ_σ(C_k)` kills the Slater) +
  `hubbardOnSiteInteraction_mulVec_allUpSlater_eq_zero` (no double occupancy) ⟹
  `generalFlatBandSlaterState_allUp_mem_groundSubmodule`: the all-up μ-Slater is in
  `generalFlatBandGroundSubmodule` (zero-energy, D₀-electron sector) — the SU(2) highest-weight
  vector sits inside the ground subspace (PR #4439).
  `fermionTotalSpinMinus_mulVec_mem_generalFlatBandGroundSubmodule` (Ŝ⁻_tot preserves the ground
  submodule, since it commutes with both Ĥ via `fermionTotalSpinMinus_commute_hubbardHamiltonian`
  and N̂ via `fermionTotalSpinMinus_commute_fermionTotalNumber`) — so the whole SU(2) lowering tower
  lies in the ground subspace (tower ⊆ ground) (PR #4441). `generalFlatBandGround_finrank_ge`: the
  D₀+1 lin-indep tower states (`highestWeight_spinMultiplet_general` + tower⊆ground +
  `LinearIndependent.of_comp`/`fintype_card_le_finrank`, with eμ/idx from
  `exists_extended_special_basis`) give the **unconditional** lower bound `finrank ground ≥ D₀+1`
  (equality needs connectivity) (PR #4442). `generalFlatBand_connected_isMaximalSpinMultiplet` (**⇐
  direction of Theorem 11.17**): connected ⟹ `IsMaximalSpinMultipletSubmodule M ground D₀` —
  `finrank = D₀+1` (`le_antisymm` of PR68 ≤ and PR77 ≥) and every ground state is a Ŝ²-eigenvector
  at (D₀/2)(D₀/2+1) (the D₀+1 tower states span ground via `span_eq_top_of_card_eq_finrank`, each a
  maximal-Casimir eigenvector);
- mirrors `tJ_halfFilling_isMaximalSpinMultiplet` (PR #4443).
  `hubbardKinetic_mulVec_spinConfigSlater_eq_zero` (kinetic kill for ANY spin config) +
  `generalCDownUp_mulVec_spinSeparatedSlater_eq_zero` (ĉ_{x↓}ĉ_{x↑} kills a spin-separated Slater,
  double-peel + separation) ⟹ `generalFlatBandSlaterState_spinSeparated_mem_groundSubmodule`: a
  spin-separated μ-Slater (opposite-spin modes with disjoint site support) is a ground state — the
  component-colouring seed of the ⟹ direction (PR #4444).
  `exists_disconnection_cut_of_not_connected` (¬connected ⟹ a non-trivial cut (A, Aᶜ) of the index
  set with no crossing μ-overlap, A = a's connected component) + `disconnection_cut_card_lt`
  ((|A|+1)(|Aᶜ|+1) > D₀+1) — the graph setup for the ⟹ direction's `finrank > D₀+1` contradiction
  (PR #4445). `cDownUp_canonicalSlaterSum_repr_twoHole_eq_zero_of_edgeSwap_invariant` (the reverse
  of eq. (11.3.49)): for an edge-swap-invariant D, the D-weighted sum of ĉ_{x↓}ĉ_{x↑}-coordinates at
  the (a,b)-emptied target vanishes — via `cDownUp_canonicalSum_eq_two_terms` collapse + coordinate
  negation, either a,b connect at x (edge ⟹ D(σ)=D(σ') cancel) or the μ_a(x)μ_b(x) factor vanishes
  (PR #4446). `cDownUp_canonicalSlaterSum_repr_eq_zero_of_not_twoHoleTarget` (the off-target
  companion): at a g that is NOT a (D₀-2)-emptied two-hole config, the D-weighted
  ĉ_{x↓}ĉ_{x↑}-coordinate sum vanishes — each inner rest-Slater coordinate is a Kronecker delta
  (`generalFlatBandSlaterState_over_I_repr`) at `idxConfigOf` of the twice-erased canonical list
  (`flatBandSpinConfigList_eraseIdx_eraseIdx`), which g matches for no pair (`hnot`) (PR #4447).
  `generalCDownUp_mulVec_canonicalSlaterSum_eq_zero_of_edgeSwap_invariant` (interaction-kill main:
  ∀g coordinate dispatch L1/L2 via `generalOccBasis` injectivity, σ-modified witness for σa=0/σb=1)
  + `canonicalSlaterSum_mem_groundSubmodule_of_edgeSwap_invariant`: **an edge-swap-invariant
  canonical-Slater sum is a ground state** (kinetic per-Slater + interaction kill + N̂=D₀) — the
  converse of the eq. (11.3.49) characterization, placing per-block weight states into ground (PR
  #4448). `upCountOn_comp_swap_eq` (in-block transposition preserves a block's up-count) +
  `generalFlatBand_blockWeightState_mem_groundSubmodule`: the per-block fiber sum W_{p,q} =
  Σ_{upCount A=p, upCount Aᶜ=q} Slater(extend s) is a ground state, since its indicator coefficient
  is edge-swap-invariant (basis-graph edges lie within one block, so swaps preserve both block
  up-counts) (PR #4449). `exists_blockUpCount_config` (a config with prescribed per-block up-counts)
  + `generalFlatBand_disconnected_finrank_gt`: **¬connected ⟹ finrank ground > D₀+1** — the
  (|A|+1)(|Aᶜ|+1) weight states W_{p,q} are linearly independent (at a fiber representative's index
  config, only its W has a nonzero occupation coordinate, via
  `idxConfigOf_flatBandSpinConfigList_inj_gen`), so finrank ≥ (|A|+1)(|Aᶜ|+1) > D₀+1;
- the contradiction with the multiplet's finrank=D₀+1 (PR #4450). **`generalFlatBand_theorem_11_17`
  (CAPSTONE, AXIOM DISCHARGED)**: `generalFlatBandFerromagnetic T U ↔ generalFlatBandBasisConnected
  I μ` — ⇐ via `generalFlatBand_connected_isMaximalSpinMultiplet`, ⇒ via the `¬connected ⟹ finrank >
  D₀+1` contrapositive;
- the §11.3.4 Theorem 11.17 axiom is now a proved theorem depending only on `propext,
  Classical.choice, Quot.sound` (PR #4451). Remaining: (⟹) direction — ferromagnetic ⟹ connected
  (contrapositive: disconnected ⟹ finrank > D₀+1 via per-component product structure) + final iff
  capstone ⟹ discharge axiom `generalFlatBand_theorem_11_17`. **REFACTOR (PR #4387): split
  `GeneralFlatBandSignPropagation.lean` (510→218 lines) — the reorder/extraction machinery (Slater
  swap/perm, canonical list, head/two-head/swap extraction, move-pair-front, per-pair extraction,
  canonical-Slater D-coefficient expansion;
- PR16-22) moved into the new `GeneralFlatBandSlaterReorder.lean` (~312 lines), for build speed
  (independent rebuilds).** **§11.4 sector minimum energy + ferromagnetism criterion
  (`SectorMinEnergy.lean`, eq. (11.4.26), Issue #4189)**: `sectorMinEnergy H filling twoS` =
  `E_min(S)` (minimum energy in the fixed-particle-number-`filling`, total-spin-`S=twoS/2` sector —
  `⨅ rayleighOnVec H` over unit `EuclideanSpace` vectors with `N̂_tot Φ=filling Φ` and
  `(Ŝ_tot)²Φ=(twoS/2)(twoS/2+1)Φ`) and `exhibitsFerromagnetism H filling twoSmax` (`∀ twoS<twoSmax,
  E_min(Smax)<E_min(twoS)` at fixed `filling`) — the precise definition of "exhibits ferromagnetism"
  used throughout Ch. 11, foundation for the non-singular Hubbard Theorems 11.18–11.20
  (axiomatize-first;
- later PRs));
- **non-singular Hubbard model (`NonsingularHubbardModel.lean`, eq. (11.4.23))**:
  `nonsingularHubbardHamiltonian = flatBandHamiltonian + (ζ:ℂ)•hubbardKinetic` (flat-band model
  perturbed by `ζ Σ t_xy ĉ†ĉ`; `ζ=0` recovers the flat band), with proven Hermiticity, `[Ĥ,N̂]=0`,
  SU(2) invariance `[Ŝ^±_tot,Ĥ]=0` — axiom-free model setup for Theorems 11.18–11.20);
- **§11.4 Theorem 11.18 (local stability, AXIOMATIZED, `NonsingularLocalStability.lean`)**:
  `IsNonsingularHopping` (cyclic translation-invariance (11.4.24) + range-`R` summability (11.4.25)
  of the perturbation) + `axiom nonsingular_theorem_11_18` — `∃ ν₀,η₀,ξ₀>0` (uniform in `K`, dep.
  `d=1,R`) s.t. under the parameter bounds the maximal-spin sector lies below the once-flipped one,
  `E_min(Smax) < E_min(Smax−1)` (`sectorMinEnergy H (K+1) < H (K−1)`); stability against a single
  spin flip (eq. (11.4.29)), deferred);
- **§11.4.1 Wannier-perturbation example model (`WannierExampleModel.lean`, eq. (11.4.1))**: §11.4.1
  is heuristic (no numbered theorems); its example model — the 1D flat-band model with the internal
  on-site potential shifted by `γ` — is `wannierExampleModel = nonsingularHubbardHamiltonian K ν t
  (γ·t) (internal-site indicator) U` (a non-singular instance), with
  `wannierExampleModel_gamma_zero`: `γ=0 ⇒ = flatBandHamiltonian` (eq. (11.4.1)→(11.3.22));
  axiom-free);
- **§11.4.2 lattice translation (`TranslationOperator.lean`, towards Theorem 11.19)**:
  `modeSiteSpinEquiv` (mode `2p+σ ↔ (site p, spin σ)`) + `siteTranslationPerm K z` (the `Equiv.Perm`
  shifting the physical site by `2z` cyclically — the combinatorial datum for the fermionic `τ̂_z`
  of eq. (11.4.30)), `siteTranslationPerm_zero`; step 1 toward the spin-wave bounds (axiom-free);
- **fermionic translation operator (`FermionicTranslation.lean`, eq. (11.4.30), step 2)**:
  `translationJwSign π σ = (-1)^(occupied inversions of π)` (JW fermion sign, `±1`) +
  `translationOperator K z` (signed permutation operator) + `translationOperator_mulVec_basisVec`
  (the defining action `τ̂_z|σ⟩=ε(π,σ)|σ∘π⁻¹⟩`) + `translationOperator_zero` (`z=0⇒1`); axiom-free,
  `E_SW(k)` + axiom 11.19 to follow);
- **§11.4.2 Theorem 11.19 (spin-wave bounds, AXIOMATIZED, `SpinWaveExcitation.lean`)**:
  `momentumPhase K k = e^{-2πik/(K+1)}`, `spinWaveEnergy K H k` = `E_SW(k)` (min energy in
  `Ŝ^z=S_max−1` ∩ `τ̂`-momentum-`k` eigenspace) + `axiom nonsingular_theorem_11_19` — `∃
  ν₁,η₁,ξ₁,ξ₂,a₁..b₃>0` s.t. under (11.4.31)/(11.4.32) the dispersion `E_SW(k)−E_min(S_max)` is
  two-sided bounded by `F·2ν⁴U(1−cos k)` (eq. (11.4.33); `F₁/F₂` (11.4.34)/(11.4.35)); deferred.
  Completes §11.4.2);
- **§11.4.3 Theorem 11.20 (non-singular Hubbard ferromagnetism, PROVED, `tasaki_theorem_11_20` in
  `NonsingularFerromagnetism.lean`, `1≤K`; rests on the analytic Lemma 11.22 and the axiom-free
  Theorem 11.11 classification `flatBand_theorem_11_11_groundSubmodule_eq_multipletSpan`
  (`TasakiFlatBandClassification.lean`, proved via `flatBand_block_finrank_le_one`), Issue #4189)**
  — Lemma 11.21 is now PROVED (`nonsingular_exhibitsFerromagnetism`); the **frustration-free
  decomposition eq. (11.4.46)** is now proved (`NonsingularFrustrationFree.lean`,
  `tasakiNonsingular_eq_sum_localHamiltonian`: `Ĥ = Σ_i ĥ_p − (K+1)(1+2ν²)s·1 + lam·(ΣN̂^β+Σn↑n↓)`,
  all `lam,κ`; κ cancels), axiom-free; the **operator-positivity half of Lemma 11.21** follows
  (`NonsingularFrustrationFreePos.lean`): `nonsingularRemainder_eq_flatBand` (`ΣN̂^β+Σn↑n↓ =
  flatBandHamiltonian K ν 1 1`) + `tasakiNonsingular_add_const_posSemidef` (`ĥ_p≥0 ∧ lam≥0 ⟹
  (Ĥ+(K+1)(1+2ν²)s·1).PosSemidef`, so ground energy `≥ −(K+1)(1+2ν²)s`), axiom-free — the §11.4
  culmination: `tasakiNonsingularHamiltonian = flatBandHamiltonian − s•Σâ†â` (eq. (11.4.38); `s=0 ⇒
  flat-band`) + `tasaki_theorem_11_20` (PROVED, `d=1`, `1≤K`: `∀ ν>0, ∃` thresholds uniform in `K`
  s.t. `t/s,U/s` large ⇒ `exhibitsFerromagnetism` at `S_max=N/2`), via the frustration-free
  `ĥ_p`/Lemma 11.22 + the proved Lemma 11.21 (`nonsingular_exhibitsFerromagnetism`) + reduction to
  Theorem 11.11;
- **Lemma 11.21 is now PROVED — only the analytic Lemmas 11.22/11.23 remain as documented axioms**
  (the Theorem 11.11 classification it invokes is proved axiom-free separately in
  `TasakiFlatBandClassification.lean`): `nonsingularLocalHamiltonian` (`ĥ_p`, eq. (11.4.48), in
  `NonsingularLocalHamiltonian.lean`) + `nonsingular_exhibitsFerromagnetism` (Lemma 11.21, PROVED,
  in `NonsingularFerromagnetism.lean`: `∀p ĥ_p≥0 ⇒ exhibitsFerromagnetism`, via compact-eigenSphere
  attainment + Theorem 11.11), `nonsingular_lemma_11_22` (conditions ⇒ `∀p ĥ_p≥0`, axiom, in
  `NonsingularLocalHamiltonian.lean`), `nonsingular_lemma_11_23` (`t,U↑∞` limit positivity, axiom).
  **§11.4: Theorem 11.20 + Lemmas 11.21 PROVED; only the analytic Lemmas 11.22/11.23 remain
  axioms**);
- **per-site fermionic spin operators (`FermionSiteSpin.lean`, towards §11.5)**:
  `fermionSiteSpinPlus/Minus/Z N i` + `fermionSpinDot N i j` (`Ŝ_x·Ŝ_y`) — building blocks for the
  t-J Heisenberg term (eq. (11.5.4)); axiom-free);
- **§11.5.2 the ferromagnetic t-J model + Proposition 11.24 (AXIOMATIZED, `TJModel.lean`, Issue
  #4198)**: `fermionSiteNumber N i` (`n̂_x`), **`tJHamiltonian N G τ J`** = `−τ P̂hc
  (Σ_{⟨x,y⟩,σ}ĉ†ĉ) P̂hc + J Σ_{⟨x,y⟩}(n̂_x n̂_y/4 − Ŝ_x·Ŝ_y)` (eq. (11.5.4); hopping =
  `hubbardKineticOnGraph` sandwiched by `hubbardHardcoreProjection`, exchange via `fermionSpinDot`;
  `τ,J>0`);
- **`axiom proposition_11_24`** (d=1 periodic `cycleGraph (N+1)`, `Ne<L` odd ⇒
  `IsMaximalSpinMultipletSubmodule N (groundSubmoduleAtFilling …) Ne` — i.e. ground states
  `S_tot=Ne/2` **and** `Ne+1`-fold degeneracy, both via the shared predicate reused from Mielke
  11.13 / general flat-band 11.15) — Perron–Frobenius / spin-charge-separation proof deferred; model
  axiom-free);
- **§11.5.2 Proposition 11.24 discharge (IN PROGRESS, Issue #4230 — replacing the
  `proposition_11_24` axiom by spin–charge separation + Perron–Frobenius)**: (i) **full SU(2)
  invariance of `tJHamiltonian`** `[Ĥ_tJ, Ŝ^α_tot]=0` for `α=z,+,−`
  (`TJSpinSymmetry`/`TJSpinSymmetryRaising`/`TJHermitian.lean`) + `tJHamiltonian_isHermitian`,
  feeding Theorem A.17;
- (ii) **the `Ŝ³=½`, `N̂=Ne` sector basis** `tJConfigOf s` (site-states `s : Fin(N+1)→Fin 3`,
  `0/1/2=∅/↑/↓`;
- hard-core, injective, orthonormal, with `N̂`/`Ŝ³`/`N̂_↑`/`N̂_↓` eigenvalues —
  `TJSectorBasis`/`TJSectorSpin`/`TJSectorNumber.lean`) + the A.17 sector reduction
  `tJHamiltonian_eigenstate_spin_zero_or_half` (`TJSectorReduction.lean`);
- (iii) **sign-freeness of every d=1 cycle hop**: the site-hop move `tJSiteHop`, the config
  identities `tJConfigOf_tJSiteHop_up/_down`, the forward Jordan–Wigner parity
  `jwSign_mul_jwSign_update_forward` (the `2·E_q` of the modes below the source cancels) and its
  backward analogue `jwSign_mul_jwSign_update_backward`, hence `⟨Φ_{s'}|ĉ†_{bσ}ĉ_{aσ}|Φ_s⟩ =
  [s'=tJSiteHop s a b]` for every rightward/leftward nearest-neighbour hop (`+1`) and the wrap bond
  `{0,N}` (`(-1)^(Ne-1)=+1` for odd `Ne`, via a three-way mode split + the total electron count) —
  `TJSectorHop`/`TJSectorHopConfig`/`TJSectorHopAction`/`TJSectorHopNN`/`HopSignBetween`/`TJOccupationCount`/`TJSectorHopWrap`/`TJSectorHopBackward`/`TJSectorHopBackwardWrap.lean`;
<!-- legacy-source:end:149:149 -->
