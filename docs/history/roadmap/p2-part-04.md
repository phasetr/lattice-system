---
layout: page
title: "Roadmap history: P2, part 4"
permalink: /history/roadmap/p2-part-04/
---

# Roadmap history: P2, part 4

> Historical implementation record normalized at semicolon-delimited bold milestones. Active work is governed by tracking Issues.

<!-- legacy-source:start:149:149 -->
- (iv) **the exchange ladder** `Ŝ⁺_iŜ⁻_j|Φ_s⟩ = |Φ_{tJSpinSwap s i j}⟩` with net JW sign `+1` (the
  two same-site creation/annihilation pairs each square to `1`, `TJSectorExchange.lean`) ⟹ exchange
  matrix element `−J/2`;
- (v) **the diagonal terms** `n̂_xn̂_y`/`Ŝ³_xŜ³_y` act diagonally so contribute `0` off-diagonal
  (`TJDiagonalMatrixElement.lean`);
- (vi) **the effective matrix** `tJEffMatrix = Tᴴ Ĥ_tJ T` (Hermitian, `M_{s',s}=⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩`,
  `TJEffMatrix.lean`), the hard-core sandwich reduction `P̂hc·K·P̂hc|Φ_s⟩=P̂hc(K|Φ_s⟩)`
  (`TJKineticSector.lean`), the bra-side projection drop `(P̂hc u)(tJConfigOf s')=u(tJConfigOf s')`
  and the kinetic spin/site expansion `⟨Φ_{s'}|K|Φ_s⟩=Σ_σΣ_iΣ_j
  couplingOf·⟨Φ_{s'}|ĉ†_{iσ}ĉ_{jσ}|Φ_s⟩`
  (`TJOffDiagonal`/`TJKineticMatrixElement`/`TJExchangeMatrixElement.lean`), and the general
  single-hop matrix element `⟨Φ_{s'}|ĉ†_{iσ}ĉ_{jσ}|Φ_s⟩` for arbitrary `i,j,σ`
  (`tJ_hop_matrixElement_apply`;
- vanishes when the source is empty, the target is already filled, or the target site carries the
  opposite spin so the hopped config is non-hard-core —
  `tJ_hop_matrixElement_eq_zero_of_source`/`_of_target`/`_of_target_other`, `TJKineticNonneg.lean`),
  the foundation for the per-term `⟨K⟩≥0` non-negativity, which is **now proven**
  (`tJ_kinetic_summand_zero_or_one`: each summand `couplingOf·⟨Φ_{s'}|ĉ†_{iσ}ĉ_{jσ}|Φ_s⟩` is `0` or
  `1` — non-adjacent killed by the coupling, adjacent dispatched via `cycleGraph_adj_val_cases` to
  the rightward/leftward NN + wrap hop matrix elements or the source/target vanishing;
- `tJKinetic_matrixElement_nonneg`: `0 ≤ ⟨Φ_{s'}|K|Φ_s⟩.re ∧ .im = 0`, `TJKineticSummand.lean`), so
  the kinetic off-diagonal entry `−τ·(≥0) ≤ 0`. **The exchange off-diagonal is likewise
  `{0,1}`-valued** (`TJExchangeNonneg.lean`): the spin-flip ladder vanishes off the antiparallel
  channel — `fermionSpinFlip_matrixElement_eq_zero_of_source` (`s j ≠ ↑` ⟹ `Ŝ⁻_j|Φ_s⟩=0`) and
  `fermionSpinFlip_matrixElement_eq_zero_of_target` (`i≠j`, `s j=↑`, `s i≠↓` ⟹ the raising `Ŝ⁺_i`
  hits an empty down-orbital) — so `tJ_exchange_summand_zero_or_one`: each `couplingOf(cycleGraph) i
  j · ⟨Φ_{s'}|Ŝ⁺_iŜ⁻_j|Φ_s⟩ ∈ {0,1}` (non-adjacent killed by the coupling;
- adjacent antiparallel gives the sign-free indicator `[s'=tJSpinSwap]`), hence the exchange
  off-diagonal entry `−(J/2)·(≥0) ≤ 0`. **The full effective-matrix off-diagonal `M_{s',s} ≤ 0` is
  now assembled** (`TJExchangeBondSum.lean`): different-site ladders commute
  (`fermionSiteSpinMinus_mul_Plus_comm`: `Ŝ⁻_xŜ⁺_y = Ŝ⁺_yŜ⁻_x` for `x≠y`, via four cross-site
  anticommutations through the generic ring helpers
  `anticomm_commute_mul`/`anticomm_commute_mul_mul` in `Math/AnticommuteCommute.lean`), so the
  reversed ladder is also `{0,1}`-valued (`tJ_exchange_swap_summand_zero_or_one`);
- the interaction off-diagonal expands (`tJInteraction_matrixElement_eq`, via a matrix-element
  linearity helper `tJME`) to `−½·Σ_{x,y}(couplingOf·⟨Ŝ⁺_xŜ⁻_y⟩ + couplingOf·⟨Ŝ⁻_xŜ⁺_y⟩)`
  (density/`Ŝ³` products drop), a non-negative real bond-sum, giving
  `tJInteraction_matrixElement_nonpos` (`−(J/2)·(≥0)`);
- combined with the kinetic `−τ·(≥0)`, **`tJEffMatrix_offdiag_nonpos`**: for `τ,J ≥ 0`, odd `Ne`,
  `s' ≠ s`, the entry `M_{s',s} = ⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩` is a non-positive real — the Perron–Frobenius
  hypothesis. **The real-symmetric sector matrix is now set up** (`TJSectorMatrix.lean`): the
  `N̂=Ne`, `Ŝ³=½` sector `TJSpinHalfFillingSector N Ne` (`s` with `#↑=#↓+1`, `#↑+#↓=Ne`), the real
  form `tJEffReMatrix = (tJEffMatrix).re`, its sector restriction `tJEffReMatrixOnSector = submatrix
  Subtype.val`, and `tJEffReMatrixOnSector_isSymm` (`IsSymm` straight from `tJEffMatrix_isHermitian`
  — `M_{q,p}=conj M_{p,q}` gives equal real parts, no global realness needed;
- the full matrix is only sector-real since the wrap-hop needs odd `Ne`);
- this is the `Matrix … ℝ` feeding Theorem A.18. **The connectivity step relation is set up**
  (`TJStepRelation.lean`): `TJStep` (one off-diagonal move — a NN/wrap hop into an adjacent empty
  site, or an adjacent antiparallel spin exchange `tJSpinSwap`), with `tJSpinSwap_count` (the swap
  is `s ∘ Equiv.swap i j`, a site bijection) and `tJStep_preserves_sector` (a step keeps `#↑`/`#↓`,
  so the reachability closure stays in one sector) — the relation whose positive entries will feed
  `matrix_pow_succ_pos_of_path`. **The per-step matrix-entry positivity is proven**
  (`TJStepMatrixEntry.lean`): the moved-electron kinetic summand equals `1`
  (`tJ_cycle_hop_kinetic_summand_eq_one`, via the forward/backward/wrap dispatch), so a hop gives
  `⟨K⟩.re ≥ 1` (`tJKinetic_matrixElement_re_ge_one_of_hop`, by `Finset.single_le_sum` over the
  `{0,1}`-valued summands);
- an exchange gives an interaction bond-sum `.re ≥ 1`, hence `J·interaction.re ≤ −J/2`;
- combining (`tJEffMatrix_re_neg_of_step`), for `τ,J > 0` every `TJStep s s'` produces `M_{s',s}.re
  < 0` (a hop `≤ −τ`, an exchange `≤ −J/2`), i.e. `B_{s',s} = −M_{s',s} > 0`. **The adjacent-swap
  bridge is in place** (`TJAdjacentSwap.lean`): an `AdjacentSwapStep` (exchange the values at an
  adjacent pair of distinct sites, `= s ∘ Equiv.swap a b`) is always a `TJStep`
  (`adjacentSwapStep_to_TJStep` — a hop if one site is empty, an exchange if the two are opposite
  spins), so `AdjacentSwapReachable` lifts to `TJStep`-reachability
  (`tjReachable_of_adjacentSwapReachable`);
- the sector connectivity then reduces to the model-agnostic combinatorial fact that two `Fin
  3`-configs with equal value-counts are adjacent-swap reachable. **The reachability basics are in
  place** (`TJSwapReachableBasics.lean`): `adjacentSwapReachable_swap` (the value-swapped `s ∘
  Equiv.swap a b` is reachable), `adjacentSwapReachable_count` (reachability preserves every
  value-count, so it stays in-sector), and `exists_needed_value_right_of_same_counts` (equal counts
  + prefix agreement ⟹ the needed value `s' p` sits right of `p` — the bubble target). **The sector
  connectivity is now proven** (`TJSwapReachable.lean`): `bubble_reachable` (move a value leftward
  to a target by NN swaps, prefix-preserving, induction on the gap) + `reach_of_agree_aux`
  (selection sort: bubble the needed value into the leftmost disagreement, recurse) assemble into
  **`adjacentSwapReachable_of_same_counts`** — any two `Fin 3`-configs with equal value-counts are
  adjacent-swap reachable, hence (via the bridge) `TJStep`-reachable within a sector. **The shifted
  PF matrix is set up** (`TJSectorShifted.lean`): `tJSectorShifted = c·1 − M` with
  `tJSectorShifted_isSymm`, `tJSectorShifted_nonneg` (entrywise `≥ 0` for `c` above the diagonal),
  `tJStep_ne` (a step changes the config), and `tJSectorShifted_pos_of_step` (a `TJStep` between
  distinct sector states gives a strictly positive off-diagonal `B`-entry). **The shifted sector
  matrix is now proven irreducible** (`TJSectorIrreducible.lean`): `tJ_value_count_total`
  (`#∅+#↑+#↓=N+1`) + `tJSector_same_counts` (distinct sector states share all value-counts) feed the
  connectivity, and `tJSectorShifted_pow_pos_of_reachable` lifts a `TJStep`-reachable chain to a
  positive matrix-power entry (`matrix_pow_succ_pos_of_pow_pos_step`, membership carried via
  `tJStep_preserves_sector`), giving **`tJSectorShifted_isIrreducible`** (`B = c·1 − M` irreducible
  via `isIrreducible_iff_exists_pow_pos`: diagonal positivity + connectivity). **The
  Perron–Frobenius ground state is now obtained** (`TJSectorGroundState.lean`): a `Nonempty
  (TJSpinHalfFillingSector N Ne)` witness (the `Ŝ³=½` filling with `↑`'s left of `↓`'s) supplies
  A.18's `[Nonempty]`, and **`tJEffReMatrixOnSector_perronFrobenius`** applies Theorem A.18 to `M =
  tJEffReMatrixOnSector` — `M` has a strictly positive eigenvector at its lowest eigenvalue `μ` (the
  sector ground energy), with `finrank ≤ 1` (non-degeneracy): the unique positive PF ground state of
  the spin-charge-separated sector. **The sector↔full bridge is started** (`TJExpansion.lean`):
  `tJExpansion v = Σ_s v_s•\|Φ_s⟩`, `tJExpansionCoeff`, and the left inverse
  `tJExpansionCoeff_tJExpansion` (orthonormal basis ⟹ injective expansion), mirroring Nagaoka
  `tasakiCoeff`/`tasakiCoeff_expansion`. **Sector-basis completeness is proven**
  (`TJCompleteness.lean`): `tJ_completeness` (a vector supported on the sector configs equals
  `tJExpansion (tJExpansionCoeff v)`), with the inverse `tJSiteStateOf` and
  `tJConfigOf_tJSiteStateOf_of_hardcore` (`tJConfigOf ∘ tJSiteStateOf = id` on hard-core configs).
  **The charge conservation `[Ĥ_tJ, N̂] = 0` is proven** (`TJNumberCommute.lean`,
  `fermionTotalNumber_commute_tJHamiltonian` — kinetic sandwich + `n̂n̂` + `Ŝ·Ŝ` all
  number-conserving, the `Ŝ⁺Ŝ⁻` ladders via `fermionTotalNumber_commute_hopping`), the remaining
  conservation law (the SU(2) `[Ĥ_tJ,Ŝ^α]=0` were already established) needed for the sector
  closure. **`Ĥ_tJ` preserves the hard-core subspace** (`TJHardcorePreserve.lean`,
  `tJHamiltonian_mulVec_mem_hardcore`): each piece commutes with `P̂hc` — the kinetic sandwich `P̂hc
  K P̂hc` by idempotency `P̂hc²=P̂hc` (`tJKinetic_commute_hubbardHardcoreProjection`), and the
  per-site `Ŝ^±_x,Ŝ³_x,n̂_x` commuting with every double occupancy `n̂_{i↑}n̂_{i↓}`
  (`fermionSiteSpin{Plus,Minus,Z}_commute_hubbardDoubleOccupancy`,
  `fermionSiteNumber_commute_hubbardDoubleOccupancy`) hence with `P̂hc`, so `n̂_xn̂_y` and `Ŝ_x·Ŝ_y`
  commute with `P̂hc` (`tJHamiltonian_commute_hubbardHardcoreProjection`) ⟹ `P̂hc(Ĥ_tJ v)=Ĥ_tJ(P̂hc
  v)=Ĥ_tJ v` (mirrors `fermionTotalSpinMinus_mulVec_mem_hardcore`);
- axiom-free. **The operator lift on a sector basis state is proven** (`TJOperatorLift.lean`,
  `tJHamiltonian_mulVec_tJConfigOf`: `Ĥ_tJ|Φ_s⟩ = Σ_{s'} ⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩ |Φ_{s'}⟩`, reassembling
  its sector-matrix column — mirrors `hubbardEffectiveHamiltonian_mulVec_tasakiState`): `Ĥ_tJ|Φ_s⟩`
  is sector-supported because it stays hard-core and keeps the `N̂=Ne`/`Ŝ³=½` eigenvalues
  (`tJHamiltonian_mulVec_preserves_number`/`_spinZ`), the key new input being the support
  restriction `tJ_mulVec_apply_eq_zero_of_not_sector` (a hard-core `N̂=Ne`,`Ŝ³=½` eigenstate
  vanishes off the sector configs, via the diagonal `Ŝ³` action `fermionTotalSpinZ_mulVec_apply` +
  `mulVec_apply_eq_zero_of_spinZ_ne`), then `tJ_completeness`;
- axiom-free. **The full eigenvector lift is proven** (`TJEigenvectorLift.lean`,
  `tJHamiltonian_mulVec_tJExpansion_ofReal`: a real PF ground eigenvector `c` of
  `tJEffReMatrixOnSector` at eigenvalue `μ` lifts to `Ĥ_tJ(tJExpansion c)=μ•tJExpansion c` — mirrors
  `hubbardEffectiveHamiltonian_mulVec_tasakiExpansion`): via `tJHamiltonian_mulVec_tJExpansion`
  (`Ĥ_tJ` acts on a sector expansion as the effective matrix `M=tJEffMatrix`, from the
  per-basis-state lift `tJHamiltonian_mulVec_tJConfigOf'` +
  `tJExpansionCoeff(Ĥ_tJ|Φ_s⟩)=tJEffMatrix`) and the sector realness `tJEffMatrix_sector_im_zero`
  (off-diagonals by `tJEffMatrix_offdiag_nonpos`, diagonal by Hermiticity), upgrading the real
  eigen-equation to the complex one;
- axiom-free. **The variational bound on the ground energy is proven** (`TJGroundEnergy.lean`, E2
  `≤` direction): `tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen` — a nonzero real sector
  eigenvector `c` of `tJEffReMatrixOnSector` at `μ` gives `groundEnergyAtFilling Ĥ_tJ Ne ≤ μ`, since
  the lifted `tJExpansion c` is admissible (hard-core `N̂=Ne` eigenvector at energy `μ`, via the
  reusable generic `groundEnergyAtFilling_le_of_eigenvector` in `GroundSubspaceAtFilling.lean` + the
  `groundEnergyAtFilling_bddBelow` brick);
- axiom-free. **The reverse-bound crux is proven** (`TJGroundEnergyReverse.lean`, E2 `≥`):
  `tJ_spinHalf_W_eigenvector_to_sector` — a nonzero `Ŝ³=½`, `N̂=Ne`, hard-core eigenvector of `Ĥ_tJ`
  at real `E` yields a nonzero real eigenvector of `tJEffReMatrixOnSector` at `E` (sector-supported
  ⟹ sector expansion ⟹ complex sector-matrix eigenvector, real on the sector by
  `tJEffMatrix_sector_im_zero` ⟹ real eigenvector via `matrix_eigenvec_re/im_of_complex`);
- corollary `tJ_sectorMin_le_of_spinHalf_W_eigenvalue`: under PF minimality, `μ ≤ E`;
- axiom-free. **The full `N̂=Ne` filling basis is set up** (`TJFillingBasis.lean`, W-compression
  foundation): the all-`Ŝ³` analog of the sector basis — `TJFillingSector N Ne = {s // #↑+#↓=Ne}`
  indexing the hard-core fixed-filling space `W`, with
  `tJFillingExpansion`/`tJFillingExpansionCoeff` + left inverse, the support restriction
  `tJ_mulVec_apply_eq_zero_of_not_filling`, and completeness `tJ_filling_completeness` (a hard-core
  `N̂=Ne` vector equals its filling expansion);
- the orthonormal `W`-basis for compressing `Ĥ_tJ` to the filling matrix `Ĥ_W`;
- axiom-free. **The `W`-projection + compression homomorphism are proven**
  (`TJFillingCompress.lean`): `tJFillingEmbedding`, `tJFillingWSubmodule` (`(N̂=Ne)`-eigenspace ⊓
  hardcore), `PreservesTJFillingW`, the projection identity `tJFillingProjection_mulVec_eq_of_mem`
  (`T Tᴴ` fixes `W`, via `Matrix.mulVec_mulVec` + `tJ_filling_completeness`), the compression
  `tJFillingCompress A = Tᴴ A T`, and the **homomorphism**
  `tJFillingCompress_mul_of_right_preserves` (`compress(A)compress(B)=compress(AB)` when `B`
  preserves `W`) + `preservesTJFillingW_tJHamiltonian`;
- axiom-free. **The A.17 operators preserve `W`** (`TJFillingSpinCompress.lean`):
  `preservesTJFillingW_of_commute` (commuting with `N̂` and `P̂hc` ⟹ preserves `W`) + submodule
  closure (`_smul`/`_add`/`_sub`) give `PreservesTJFillingW` for `Ŝ⁽³⁾`, `Ŝ⁺`, `Ŝ⁻`, `Ŝ⁽¹⁾`, `Ŝ⁽²⁾`
  (and `preservesTJFillingW_tJHamiltonian` for `Ĥ_tJ`);
- axiom-free. **The compressed `Ĥ_W`, `Ŝ⁽ᵅ⁾_W` satisfy the A.17 hypotheses**
  (`TJFillingCompressSpinAlgebra.lean`): via the compression homomorphism + `compress` linearity
  (`tJFillingCompress_smul`/`_sub`/`_isHermitian`), the `W`-compressions inherit Hermiticity, the
  su(2) relations (`tJFillingCompress_su2_12`/`_23`/`_31`) and `Ĥ_W`-commutativity
  (`tJFillingCompress_tJHamiltonian_commute_one`/`_two`/`_three`) — exactly the inputs of the matrix
  Theorem A.17;
- axiom-free. **The filling embedding is an isometry + the Rayleigh bridge**
  (`TJFillingRayleighBridge.lean`): `tJFillingEmbedding_conjTranspose_mul_self` (`Tᴴ T = 1`),
  `tJFillingExpansion_dotProduct_self` (`⟨T c, T c⟩=⟨c,c⟩`), and `rayleighOnVec_tJFillingCompress`
  (`rayleighOnVec Ĥ_tJ (tJFillingExpansion c) = rayleighOnVec Ĥ_W c`) — connecting
  `groundEnergyAtFilling` to the matrix `Ĥ_W`;
- axiom-free. **The eigenvector lift is proven** (`TJFillingEigenLift.lean`,
  `mulVec_tJFillingExpansion_of_compress_eigen`): an eigenvector of `compress(A)` at `E` lifts (when
  `A` preserves `W`) to an eigenvector of `A` at `E` on `W`, via the projection identity `T Tᴴ = id`
  on `W`;
- plus `tJFillingExpansion_mem_tJFillingWSubmodule`;
- axiom-free. Remaining for E2-≥: apply the matrix A.17 (`exists_joint_su2_energy_eigenstate`) to
  the min eigenvector of `Ĥ_W` (its hypotheses are the proven compressed su(2)/Hermitian/commute),
  lift it (this lemma), use odd `Ne` to force `Ŝ³=½` (`TJFillingSpinZDiag.lean`: `Ŝ³` is diagonal on
  filling expansions, `fermionTotalSpinZ_mulVec_tJFillingExpansion`, and the only `Ŝ³=0` filling
  state is `0` for odd `Ne`, `tJFillingExpansion_eq_zero_of_spinZ_mulVec_eq_zero`) ⟹ `μ ≤
  hermitianMinEigenvalue Ĥ_W`, identify `groundEnergyAtFilling = hermitianMinEigenvalue Ĥ_W` via the
  bridge, completing `groundEnergyAtFilling = μ`. **E2 is now COMPLETE** (`TJGroundEnergyGe.lean`):
  `tJ_perronFrobeniusMin_le_hermitianMinEigenvalue` (the W-restricted A.17 application),
  `tJ_groundEnergyAtFilling_ge_of_sectorMin` (`μ ≤ groundEnergyAtFilling`), and the capstone
  `tJHamiltonian_groundEnergyAtFilling_eq_perronFrobeniusMin` (`groundEnergyAtFilling = μ`, with the
  strictly-positive PF eigenvector `v` at `μ`) — resting only on Theorem A.17
  (`exists_joint_su2_energy_eigenstate`, **now discharged** §A.3.2). **E3a (the SU(2) upper-bound
  seed, `TJGroundSpinHalfFinrank.lean`) is now COMPLETE**:
  `tJ_groundSubmodule_spinHalf_finrank_le_one` — `finrank ℂ (groundSubmoduleAtFilling Ĥ_tJ Ne ⊓
  (Ŝ³=½)) ≤ 1` — via `groundEnergyAtFilling = μ`, the PF real `finrank ≤ 1`, the real↔complex
  eigenspace bridge `matrix_complex_eigenspace_finrank_le_one_of_real`, and the injective `ℂ`-linear
  embedding `tJExpansionCoeffₗ` (`Φ ↦ tJExpansionCoeff Φ`, injective by sector-support) of the block
  into the complex sector eigenspace at `μ`;
- supporting lemma `tJ_spinHalf_W_complexSectorEigen` (a block element's coefficient vector is a
  complex sector-matrix eigenvector at `μ`);
- no new axioms. **E3b PR1 (`TJSectorRaise.lean`, toward lifting the PF vector to a highest weight)
  is COMPLETE**: the single-site raising operator `Ŝ⁺_x = ĉ†_{x↑}ĉ_{x↓}` is **sign-free** on the
  sector basis — `fermionSiteSpinPlus_mulVec_tJConfigOf_of_down` (`s x=↓ ⟹ Ŝ⁺_x|Φ_s⟩ = |Φ_{s with
  x↦↑}⟩` with net Jordan–Wigner sign `+1`, since the adjacent orbitals `(x↑,x↓)=(2x,2x+1)` with `2x`
  empty collapse the two strings) + `fermionSiteSpinPlus_mulVec_tJConfigOf_of_not_down` (`s x≠↓ ⟹
  Ŝ⁺_x|Φ_s⟩=0`) + the config identity `tJConfigOf_update_raise`;
- fully axiom-free. This Marshall sign-freeness makes the iterated `(Ŝ⁺)^m` have nonnegative config
  coefficients, so a strictly-positive coordinate (from `v q > 0`) gives the non-vanishing
  `(Ŝ⁺)^((Ne-1)/2) Φ₀ ≠ 0`. **E3b PR2 (`TJRaisingTower.lean`) is COMPLETE**: eigenvalue tracking
  along the raising tower — `fermionTotalSpinZ_mulVec_spinPlusPow` (`Ŝ³ (Ŝ⁺)^k v = (m+k)(Ŝ⁺)^k v`,
  via `[Ŝ³,Ŝ⁺]=Ŝ⁺`), `tJHamiltonian_mulVec_spinPlusPow` (energy `μ` preserved, `[Ĥ_tJ,Ŝ⁺]=0`),
  `fermionTotalNumber_mulVec_spinPlusPow` (number `Ne` preserved, `[N̂,Ŝ⁺]=0`);
- so `(Ŝ⁺)^k Φ₀`, when nonzero, is a fixed-`Ne`, energy-`μ`, `Ŝ³=½+k` eigenvector;
- fully axiom-free. **E3b PR3 (`TJRaisingTermination.lean`) is COMPLETE**: the raising tower
  terminates — `fermionTotalDownNumber_mul_fermionTotalSpinPlus` (`[N̂_↓,Ŝ⁺]=−Ŝ⁺`),
  `fermionTotalDownNumber_mulVec_spinPlusPow` (`N̂_↓ (Ŝ⁺)^k v = (m−k)(Ŝ⁺)^k v`), and
  `spinPlusPow_succ_eq_zero_of_downNumber` (`N̂_↓ v = m v ⟹ (Ŝ⁺)^(m+1) v = 0`, since the
  `N̂_↓`-eigenvalue `−1` forces `(↓count+1)·ψ(w)=0` per config);
- fully axiom-free. So for a `Ŝ³=½`, `N̂=Ne` ground state (`N̂_↓=(Ne−1)/2`), the top
  `Ω=(Ŝ⁺)^((Ne−1)/2)Φ` satisfies `Ŝ⁺Ω=0` — a highest weight. **E3b PR4 (`TJHighestWeight.lean`) is
  COMPLETE**: `tJ_raised_highestWeight` combines the tower tracking + termination — `Φ` with
  `Ŝ³Φ=½Φ`, `N̂_↓Φ=mΦ`, `Ĥ_tJΦ=μΦ` ⟹ `Ω=(Ŝ⁺)^m Φ` satisfies `Ŝ⁺Ω=0`, `Ŝ³Ω=(m+½)Ω`, `Ĥ_tJΩ=μΩ` (for
  `m=(Ne−1)/2`, `Ŝ³Ω=(Ne/2)Ω`, the maximal-spin highest weight);
- fully axiom-free. **E3b PR5a (`TJExpansionSpinEigen.lean`) is COMPLETE**: the lifted ground
  vector's sector eigenvalues — `tJSpinHalfFillingSector_down_count` (every sector state has
  `#↓=(Ne−1)/2`), `fermionTotalSpinZ_mulVec_tJExpansion` (`Ŝ³ (tJExpansion v)=½(tJExpansion v)`),
  `fermionTotalDownNumber_mulVec_tJExpansion` (`N̂_↓ (tJExpansion v)=((Ne−1)/2)(tJExpansion v)`),
  letting the highest-weight extraction apply to `Φ₀=tJExpansion(ℂ∘v)` with `m=(Ne−1)/2`;
- fully axiom-free. **E3b PR5b-1 (`TJTotalRaiseAction.lean`) is COMPLETE**:
  `fermionTotalSpinPlus_mulVec_tJConfigOf` — `Ŝ⁺_tot |Φ_s⟩ = Σ_{x:s x=↓} |Φ_{s with x↦↑}⟩` (the
  sign-free expansion, every term `+1`), the keystone for the config-nonnegativity argument toward
  `(Ŝ⁺)^((Ne−1)/2)Φ₀ ≠ 0`;
- fully axiom-free. **E3b PR5b-2 (`TJRaiseCoeffSum.lean`) is COMPLETE**: the coefficient-sum
  functional `coeffSum ψ = Σ_c ψ_c` — `coeffSum_basisVec` (`= 1`) and
  `coeffSum_fermionTotalSpinPlus_tJConfigOf` (`coeffSum (Ŝ⁺_tot|Φ_s⟩) = #↓(s)`);
- with the uniform sector down-count, iterating gives `coeffSum ((Ŝ⁺)^((Ne−1)/2) Φ₀) =
  ((Ne−1)/2)!·Σv_q > 0`, so the raised vector is nonzero;
- fully axiom-free. **E3b PR5b-3a (`TJFillingCoeffSum.lean`) is COMPLETE**:
  `coeffSum_tJFillingExpansion` (`= Σ_s v_s`) and `coeffSum_fermionTotalSpinPlus_tJFillingExpansion`
  (`= Σ_s v_s·#↓(s)`) — together the recursion `coeffSum (Ŝ⁺ψ) = d·coeffSum ψ` for a hard-core
  `N̂_↓`-eigenvector at `d`;
- fully axiom-free. **E3b PR5b-3b (`TJRaisePositivityStep.lean`) is COMPLETE**:
  `fermionTotalDownNumber_mulVec_tJFillingExpansion` (`N̂_↓` diagonal on a filling expansion) and
  `coeffSum_fermionTotalSpinPlus_eq_of_downEigen` — a hard-core `N̂=Ne` vector `ψ` with `N̂_↓ψ=dψ`
  satisfies `coeffSum (Ŝ⁺ψ) = d·coeffSum ψ` (both sides `= Σ_s coeff_s·#↓(s)` via
  `tJ_filling_completeness`);
- fully axiom-free. **E3b PR5c (`TJRaiseHardcore.lean`) is COMPLETE**:
  `fermionTotalSpinPlus_mulVec_mem_hardcore` + `fermionTotalSpinPlus_pow_mulVec_mem_hardcore`
  (`Ŝ⁺_tot` and its powers preserve the hard-core subspace), keeping every tower state `(Ŝ⁺)^k Φ₀`
  hard-core for the recursion;
- fully axiom-free. **E3b PR5d (`TJRaisePositivity.lean`) — the Marshall positivity crux — is
  COMPLETE**: `coeffSum_tJExpansion` (`= Σ_s v_s`) and **`spinPlusPow_ne_zero_of_coeffSum_ne_zero`**
  (a hard-core `N̂=Ne` vector `Φ₀` with `N̂_↓Φ₀=mΦ₀` and nonzero coefficient sum has `(Ŝ⁺)^m Φ₀ ≠
  0`, since each step multiplies `coeffSum` by `m−k ≠ 0`). Applied to `Φ₀=tJExpansion(ℂ∘v)`
  (`coeffSum=Σv_q>0`, `m=(Ne−1)/2`), this gives `Ω = (Ŝ⁺)^((Ne−1)/2) Φ₀ ≠ 0` — the non-vanishing;
- fully axiom-free. **E4 PR6a (`TJMaximalSpinGroundState.lean`) is COMPLETE**:
  `tJ_exists_maximalSpin_highestWeight_groundState` assembles the E3b chain into a nonzero
  highest-weight ground state — `Ω` with `Ŝ⁺Ω=0`, `Ŝ³Ω=(Ne/2)Ω`, `Ĥ_tJΩ=μΩ` at
  `μ=groundEnergyAtFilling`, plus `Ω∈hardcore` and `N̂Ω=Ne·Ω` (so `Ω∈groundSubmoduleAtFilling`) —
  non-vanishing from the Marshall positivity, highest-weight from `tJ_raised_highestWeight`,
  `groundEnergyAtFilling=μ` from E2;
- rests only on A.17 (**now discharged** §A.3.2). **E4 lower bound (`TJGroundDegeneracyLower.lean`)
  is COMPLETE**: `tJ_groundSubmodule_finrank_ge` — `Ne + 1 ≤ finrank (groundSubmoduleAtFilling Ĥ_tJ
  Ne)`. The highest weight `Ω` generates the `Ne+1` LI tower `(Ŝ⁻)^k Ω`
  (`highestWeight_spinMultiplet_general`);
- each member is again a ground state (`Ŝ⁻` commutes `Ĥ_tJ`/`N̂`, preserves hard-core), so
  `LinearIndependent.of_comp` + `fintype_card_le_finrank` give the bound;
- rests only on A.17. **E5 ladder injectivity (`TJLadderInjective.lean`) is COMPLETE**: the SU(2)
  norm identity `‖Ŝ⁻v‖²=‖Ŝ⁺v‖²+2sz‖v‖²` (`fermionTotalSpin_ladder_norm`, from
  `[Ŝ⁺,Ŝ⁻]=2Ŝ³`+`(Ŝ⁻)ᴴ=Ŝ⁺`) gives `Ŝ⁻` injective on weight `sz>0` and `Ŝ⁺` on `sz<0` — no rep theory
  — embedding each `Ŝ³`-weight space of `G` into `Ŝ³=±½`, the key to the upper bound `finrank≤Ne+1`;
- fully axiom-free. **E5b weight-finrank step (`TJGroundWeightFinrank.lean`) is COMPLETE**:
  `tJ_ground_weight_finrank_le_succ` — for `sz≥0`, `finrank (G⊓Ŝ³=sz+1) ≤ finrank (G⊓Ŝ³=sz)` (`Ŝ⁻`
  injects the `sz+1` weight space into the `sz` one, preserving `G` via
  `fermionTotalSpinMinus_mulVec_mem_groundSubmodule` and lowering the weight by one);
- iterating to `½` (and up via `Ŝ⁺`) bounds every weight space by the `Ŝ³=½` block ≤1. **The `Ŝ⁺`
  mirror (`TJGroundWeightFinrankRaise.lean`) is COMPLETE**:
  `tJ_ground_weight_finrank_le_of_spinZ_neg` — for `sz<0`, `finrank (G⊓Ŝ³=sz) ≤ finrank (G⊓Ŝ³=sz+1)`
  (`Ŝ⁺` injects `sz` into `sz+1`), so negative-weight blocks are bounded by `Ŝ³=½` from below too.
  **Every weight block ≤1 (`TJGroundWeightOne.lean`) is COMPLETE**:
  `tJ_ground_weight_finrank_le_one_pos/_neg` — `finrank (G⊓Ŝ³=½+k) ≤ 1` and `finrank (G⊓Ŝ³=−½−k) ≤
  1` (`k:ℕ`), by iterating the two steps to the `Ŝ³=½` block (≤1, E3a);
- the half-integers exhaust the `Ŝ³` spectrum at odd filling. **The `Ŝ³` weight decomposition
  (`TJGroundWeightDirectSum.lean`) is COMPLETE**: `fermionTotalSpinZ_mulVec_mem_groundSubmodule`
  (`Ŝ³` preserves `G`), `fermionTotalSpinZ_iSup_eigenspace_eq_top` (`Ŝ³` diagonal on the
  computational basis, so its eigenspaces span `⊤`), and `tJ_groundSubmodule_eq_iSup_inf_eigenspace`
  — `G = ⨆ μ, G ⊓ eigenspace Ŝ³ μ` (`Submodule.eq_iSup_inf_genEigenspace` for the invariant `G`);
- **The finite `Ŝ³` weight reindexing (`TJGroundWeightReindex.lean`) is COMPLETE**:
  `tJ_groundSubmodule_inf_eigenspace_eq_bot` (off-weight blocks vanish — `G ⊓ eigenspace Ŝ³ μ = ⊥`
  for `μ` outside `{a − Ne/2 : a ∈ Fin (Ne+1)}`) and `tJ_groundSubmodule_eq_iSup_weight` — `G = ⨆ a
  : Fin (Ne+1), G ⊓ eigenspace Ŝ³ (a − Ne/2)` (the all-`ℂ` supremum collapses to the `Ne+1`
  occurring half-integer weights);
- **The degeneracy upper bound (`TJGroundDegeneracyUpper.lean`) is COMPLETE**:
  `tJ_groundSubmodule_finrank_le` — `finrank G ≤ Ne+1` (the `Ne+1` half-integer weight blocks are
  independent (`eigenspaces_iSupIndep`), hence an internal direct sum of `G`
  (`DirectSum.coeLinearMap` injective + `finrank_directSum`), and each block is ≤1 (#4309), so
  `finrank G = ∑ finrank (block) ≤ Ne+1`); paired with the SU(2)-tower lower bound
  (`tJ_groundSubmodule_finrank_ge`, #4305) this pins `finrank G = Ne+1`. **Proposition 11.24 is now
  PROVED** (`proposition_11_24` in `TJProposition1124.lean`, E6 capstone):
  `IsMaximalSpinMultipletSubmodule N (groundSubmoduleAtFilling …) Ne` — `finrank G = Ne+1`
  (le_antisymm of #4305/#4312) and every ground state is an `(Ŝ_tot)²` eigenvector at
  `(Ne/2)(Ne/2+1)` (the `Ne+1` LI tower states `(Ŝ⁻)^k Ω` span `G`, each maximal-spin via
  `highestWeight_spinMultiplet_general`). **This discharges the former `axiom proposition_11_24`**;
  the entire d=1 ferromagnetic t-J ferromagnetism result rests only on Theorem A.17 (**now
  discharged** §A.3.2). Then the total-spin identification (`S_tot = Ne/2`) via the highest weight
  raised this way, the SU(2)-tower lower bound (paired with this `Ŝ³=½` block bound for the upper
  bound), and the capstone replacing the axiom. The discharge lemmas add no new t-J axioms; the only
  inherited dependency is the A.17 sector reduction `tJHamiltonian_eigenstate_spin_zero_or_half`
  (which rests on Theorem A.17 (`exists_joint_su2_energy_eigenstate`, **now discharged**) axiom),
  every other layer being fully axiom-free.**);
- **generic fixed-filling hard-core ground subspace (`GroundSubspaceAtFilling.lean`)**:
  `fillingHardcoreStates`/`groundEnergyAtFilling`/`groundSubmoduleAtFilling` (`H`-eigenspace at the
  ground energy ⊓ `N̂=Ne` ⊓ `hubbardHardcoreSubspace`), shared by Prop 11.24 and Thm 11.26;
  axiom-free;
- **§11.5.3 d=1 decorated Hubbard model + Lemma 11.25 (documented axiom) + **Theorem 11.26 (PROVED,
  `MetallicFerroModel.lean`, Issue #4314)**: the duplicated-internal-site lattice `Λ=E∪(I×{1,2})` in
  `Fin(3K+3)` (`decExternalSite`/`decInternalSite1/2`); localized states
  `decAlpha`/`decBeta1`/`decBeta2` (eqs. (11.5.7)–(11.5.9)) + fermion ops
  `decA/BCreation/Annihilation` (eq. (11.5.10)); `decHopping` (`t Σ b̂†b̂ − s Σ_{⟨p,q⟩∈E,σ}â†_pâ_q`,
  eq. (11.5.14)) + `decInteraction` (`U Σ n̂↑n̂↓`, eq. (11.5.13)) + `decHubbardHamiltonian`;
- **`axiom lemma_11_25`** (`t,U↑∞` Hubbard ≡ `J↑∞` t-J at `τ=(1+4ν²)s`, rendered as spin-structure
  transfer: Hubbard ground subspace is the maximal-spin `Ne+1`-multiplet **iff** the t-J one is, in
  the limits;
<!-- legacy-source:end:149:149 -->
