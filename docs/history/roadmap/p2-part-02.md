---
layout: page
title: "Roadmap history: P2, part 2"
permalink: /history/roadmap/p2-part-02/
---

# Roadmap history: P2, part 2

> Historical implementation record normalized at semicolon-delimited bold milestones. Active work is governed by tracking Issues.

<!-- legacy-source:start:149:149 -->
- **§11.3.4 Theorem 11.15 (general flat-band ferromagnetism, PROVED axiom-free,
  `GeneralFlatBandTheorem1115.lean`, Issue #4453)**: Mielke's general nec-&-suf condition — for a
  Hermitian PSD hopping matrix `T`, flat band `h₀=ker T`, `D₀=dim h₀>0`, `U>0`, filling `N=D₀`, the
  model is saturated-ferromagnetic **iff** the `Λ₀×Λ₀` projection submatrix `(P₀)` is irreducible
  (`Λ₀={x|(P₀)_{x,x}≠0}`). `P₀` = orthogonal projection onto `ker T` via
  `Matrix.toEuclideanLin`→`Submodule.starProjection`→`LinearMap.toMatrixOrthonormal`; irreducibility
  via `Matrix.IsIrreducible` of the real `Complex.normSq(P₀)` support matrix; ferromagnetism via the
  `mielke_theorem_11_13` ground-subspace pattern. `theorem tasaki_theorem_11_15` — DISCHARGED
  axiom-free (Issue #4453, `GeneralFlatBandTheorem1115.lean`): the bridge `projectionIrreducible ↔
  basisConnected` (composed with proved 11.17) — `generalFlatBandProjectionMatrix_apply`
  ((P₀)_{xy}=⟪e_x,P₀ e_y⟫), `_isHermitian` (P₀ Hermitian ⟹ symmetric support), `_isIdempotent`
  (P₀²=P₀) (PR #4454). `generalFlatBandProjectionMatrix_diag_eq` ((P₀)_{xx}=‖P₀ e_x‖² via
  self-adjoint+idempotent) + `generalFlatBand_diag_ne_zero_iff` (active site (P₀)_{xx}≠0 ⟺ e_x ∉
  (ker T)ᗮ, via `starProjection_apply_eq_zero_iff`) (PR #4455). `generalFlatBand_mu_mem_kernel` (μ_z
  ∈ ker T as Euclidean vector, via `toEuclideanLin`/`mulVec`) +
  `generalFlatBand_special_index_active` (**I ⊆ Λ₀**: each index site z is active, since μ_z ∈ ker T
  with μ_z(z)≠0 ⟹ e_z not ⊥ ker T ⟹ (P₀)_{zz}≠0) (PR #4456). `generalFlatBand_kernel_eq_span` (ker T
  = span{toLp μ_z}, via finrank: |I| lin-indep vectors in D₀-dim) +
  `generalFlatBand_active_iff_exists_mu_ne` (**active ⟺ μ-support**: (P₀)_{xx}≠0 ⟺ ∃z∈I μ_z(x)≠0,
  via span_induction on ker=span{μ_z}) (PR #4457). `generalFlatBandProjectionSupportMatrix_isSymm`
  (the support matrix |P₀_{xy}|² is symmetric — P₀ Hermitian + `normSq_conj` — so irreducibility =
  undirected-graph connectivity) (PR #4458). `generalFlatBand_kernel_coord_determined` (a flat-band
  vector vanishing at every index site is 0 — write v=Σc_z μ_z, evaluate at index w, localisation
  μ_{z'}(w)=δ_{z'w}μ_w(w) collapses to c_w μ_w(w), μ_w(w)≠0 ⟹ all c=0): the engine of the cut/block
  argument for the irreducibility↔connectivity bridge (Codex-validated route, avoids the Gram
  inverse) (PR #4459). `generalFlatBand_proj_apply_eq_zero_of_diag_zero` (inactive site ⟹ P₀ e_x =
  0) + `generalFlatBand_proj_row_eq_zero_of_diag_zero` (inactive site ⟹ whole row (P₀)_{xy}=0) —
  P₀'s support is confined to Λ₀, toward the cut/block decomposition (PR #4460).
  `generalFlatBand_proj_offdiag_eq` ((P₀)_{xy}=⟪P₀ e_x,P₀ e_y⟫) +
  `generalFlatBand_proj_active_of_ne_zero` (support edge (P₀)_{xy}≠0 ⟹ both x,y active) — the
  support graph lives on Λ₀ (PR #4461). `generalFlatBand_mu_orthogonal_of_disjoint_support` (μ_z ⊥
  μ_{z'} when their site supports are disjoint — inner = Σ_x conj μ_z(x)·μ_{z'}(x), each term 0):
  makes the per-side flat-band subspaces of a basis cut orthogonal (PR #4462).
  `generalFlatBand_no_shared_site_of_saturated` (for a basis-adjacency-closed J ⊆ I, no site is
  covered by both a J-index and an (I∖J)-index — a shared site would be a basis edge): the
  active-site side-assignment of a basis cut is well-defined (PR #4463).
  `generalFlatBand_basisVec_mem_orthogonal_of_side` (if every μ_z (z∈S) vanishes at x, then e_x ⊥
  span{μ_z:z∈S}, via span_induction + ⟪μ_z,e_x⟫=conj μ_z(x)=0): places P₀ e_x in the complementary
  side, the heart of the block-diagonal decomposition (PR #4464).
  `generalFlatBand_proj_mem_orthogonal` (P₀ preserves orthogonality to a flat-band subspace: V≤ker
  T, e_x⊥V ⟹ P₀ e_x⊥V, since P₀ fixes V and is self-adjoint): so P₀ e_x stays on x's side of a cut
  (PR #4465). `generalFlatBand_kernel_eq_sup` (ker T = span{μ_z:z∈S} ⊔ span{μ_z:z∈Sᶜ} for any S⊆I,
  via span over a union): with side-orthogonality, the orthogonal block decomposition of ker T (PR
  #4466). `generalFlatBand_side_subspaces_orthogonal` (V_S ⊥ V_Sᶜ when the two sides have disjoint
  site supports — each generator pair orthogonal, lifted through span; for a saturated cut the
  disjointness comes from `no_shared_site_of_saturated`) (PR #4467). `generalFlatBand_proj_mem_side`
  (P₀ e_y ∈ V_Sᶜ for y on the Sᶜ-side: P₀ e_y ∈ ker T = V_S ⊕ V_Sᶜ decomposes as a+b, and P₀ e_y ⊥
  V_S with V_S ⊥ V_Sᶜ force a=0, so P₀ e_y = b ∈ V_Sᶜ — P₀ carries each side into itself) (PR
  #4468). `generalFlatBand_proj_offdiag_eq_zero_across_cut` (P₀_xy = 0 when x is S-supported and y
  is Sᶜ-supported: P₀_xy = ⟪P₀ e_x, P₀ e_y⟫ with P₀ e_x ∈ V_S, P₀ e_y ∈ V_Sᶜ, V_S ⊥ V_Sᶜ — the
  projection is block-diagonal across a basis cut) (PR #4469).
  `generalFlatBand_starProjection_expand` / `generalFlatBand_kernel_coord_matvec` (matrix–vector
  form v_y = Σ_x v_x (P₀)_{yx} for v∈ker T) / `generalFlatBand_restrict_mem_kernel` (coordinate
  restriction 1_W·v = Σ_{x∈W} v_x e_x of a kernel vector across a P₀-block cut W stays in ker T —
  the linear-algebra core of "P₀ reducible ⟹ basis cut") (PR #4470).
  `generalFlatBand_truncation_coord` (coordinate of a truncation) +
  `generalFlatBand_mu_confined_of_block` (for a P₀-block coordinate cut W, an index z∈I∩W has μ_z
  supported entirely in W: 1_Wᶜ·μ_z is a kernel vector vanishing at every index site, hence 0 by
  kernel_coord_determined — a basis vector cannot straddle a P₀-block cut) (PR #4471). **Theorem
  11.15 DISCHARGED (axiom-free) — bridge file `GeneralFlatBandTheorem1115.lean`** (`theorem
  tasaki_theorem_11_15`; axiom removed from GeneralFlatBand.lean; #print axioms = [propext,
  Classical.choice, Quot.sound]; composes proved Theorem 11.17 `ferro↔basisConnected` with
  `projIrred↔basisConnected`): `generalFlatBandProjectionBlockReducible` (∃ coordinate cut W with an
  active site each side and no P₀ entry across) +
  `generalFlatBand_blockReducible_of_not_basisConnected` (¬basisConnected ⟹ blockReducible: the
  basis-disconnection cut's μ-support W has A-indices active inside / Aᶜ-indices active outside, and
  P₀_yx=0 across by proj_offdiag_eq_zero_across_cut + Hermitian) (PR #4472).
  `generalFlatBand_not_basisConnected_of_blockReducible` (the converse: blockReducible ⟹
  ¬basisConnected — each μ_z confined to its index's side by mu_confined_of_block, so the index set
  splits into J={z|z.1∈W} closed under adjacency with both sides active-nonempty, and a J-vertex
  cannot reach outside J) (PR #4473). `generalFlatBand_support_pow_eq_zero_across_block` (support
  powers stay in a P₀-block: (support^k)_{ij}=0 for i.1∈W, j.1∉W) +
  `generalFlatBand_not_projectionIrreducible_of_blockReducible` (blockReducible ⟹
  ¬projectionIrreducible: the two active sites never connect, contradicting
  isIrreducible_iff_exists_pow_pos); `generalFlatBandActiveSites` made an `abbrev` so
  Fintype/DecidableEq are transparent for matrix powers (PR #4474).
  `generalFlatBand_blockReducible_of_not_projectionIrreducible` (the reverse: ¬projIrred ⟹
  blockReducible — isIrreducible_iff_exists_pow_pos gives active i₀,j₀ with no positive support
  path; W = sites reachable from i₀ via positive support powers, i₀∈W via self-loop |P₀_{i₀i₀}|²>0,
  j₀∉W unreachable, no P₀ crosses out since an entry would extend a path; inactive y has zero row) —
  completes projIrred ↔ ¬blockReducible (PR #4475). **CAPSTONE
  `generalFlatBand_projectionIrreducible_iff_basisConnected` + `theorem tasaki_theorem_11_15`**
  (Lemma 11.16 special basis → Theorem 11.17 ferro↔connected → bridge connected↔projIrred; axiom
  REMOVED, axiom-free) (PR #4476). **Lemma 11.16** (`generalFlatBand_lemma_11_16`: `ker T` has a
  site-localised basis `{μ_z}_{z∈I}`, `|I|=D₀`, `μ_z(z)≠0`, `μ_z(z')=0` for `z'≠z`) **now discharged
  (axiom-free)** — the coordinate functionals `(EuclideanSpace.projₗ x)|_{ker T}` separate points, a
  `D₀`-subset `I` is a basis of the dual `(ker T)*`, and its reflexive predual basis is the
  localised `{μ_z}` (`generalFlatBand_exists_special_index` +
  `Module.Basis.dualBasis_apply_self`/`apply_evalEquiv_symm_apply`);
- **Theorem 11.17** (`generalFlatBand_theorem_11_17`: ferromagnetic ⇔ the special basis is
  connected, via `generalFlatBandBasisGraph`) **PROVED (axiom DISCHARGED, Issue #4363)** — Mielke's
  second nec-&-suf condition. Proof discharge of 11.15 is later work;
- **Theorem 11.17 discharge STARTED (Issue #4363, PR1 foundation, `GeneralFlatBandOperators.lean` +
  `GeneralFlatBandGroundAnnihilation.lean`, the latter split out in a build-speed refactor):
  general-flat-band smeared creation/annihilation operators `â†_{z,σ} := Ĉ†_σ(μ_z)` over an
  arbitrary special basis, full CAR algebra (unified, bilinear `{Ĉ_σ(φ), Ĉ†_τ(ψ)} = δ_{στ}(Σφψ)·1`,
  site-dual), Slater states + â†-monomial Fock submodule, single + double site-annihilation peel
  (eq. 11.3.48 engine), `generalCDownUp` + double-occupancy Gram identity, kinetic operator PSD from
  hopping PSD (`T = CᴴC` Gram-sum), Rayleigh decomposition, no-double-occupancy kill, ground state
  annihilated by every range-T mode (precise `conj(range T)` / `Ĉ_σ(star(T·w))` and
  nonzero-eigenvalue-eigenvector `Ĉ_σ(ū)` forms — the exact orthonormal-eigenbasis
  occupation-detection operators), and the spectral `ker T ⊕ range T` classification + completeness
  `exists_ker_add_range_decomp` — the operator-algebraic premise of eq. 11.3.46. **Theorem 11.17 PR2
  (Issue #4363, `GeneralFlatBandModeMonomial.lean` + `GeneralFlatBandOccBasis.lean`): general
  occupation basis over an arbitrary single-particle basis** — bilinear creation–creation
  anticommutation `{Ĉ†_σ(φ),Ĉ†_τ(ψ)}=0` + nilpotency `(Ĉ†)²=0`; general-basis Fock monomials `Ĉ†_σ(e
  i)`-products on the vacuum spanning `⊤` (mode + site creation invariance via the basis `repr`,
  computational-basis-vector expansion); reorder/permutation-scaling + repeated-mode vanishing;
  occupation monomials + `generalOccBasis` (a basis of the full Fock space indexed by occupation
  configs of the `2(M+1)` mode-spin slots, `2^(2(M+1))=finrank`). The Theorem 11.11 occupation-basis
  machinery, re-developed generically in the basis for instantiation at the spectral eigenbasis of
  `T`. **Theorem 11.17 PR3 (Issue #4363, `GeneralFlatBandEigenbasis.lean`): spectral-eigenbasis
  annihilation peel** — the orthonormal eigenbasis `T.IsHermitian.eigenvectorBasis` transported to a
  `Module.Basis` of `Fin(M+1)→ℂ` (`eigenbasisAsBasis`), its coordinate orthonormality `Σ_x
  conj(e_j(x))e_k(x)=δ_{jk}`, the dual CAR `{Ĉ_σ(ē_j),Ĉ†_τ(e_k)}=δ_{jk}δ_{στ}·1`, the
  smeared-annihilator vacuum kill `Ĉ_σ(φ)|vac⟩=0`, and the eigenbasis-annihilation peel
  `Ĉ_σ(ē_j)|qs⟩ = Σᵢ (-1)^i·δ_{j,(qs[i]).1}δ_{σ,(qs[i]).2}·|qs∖i⟩` (the occupation-detection
  engine). **The peel layer — the two peel lemmas and the per-position peel-term summand definition
  they were proved with (one of the two stated with it directly, the other only using it inside its
  proof) — was later removed as unused**: PR4 below detects occupation through the eigenmode
  *number* operator `n̂_{j,σ}` built from the same dual CAR, so of this PR the transported
  eigenbasis (`eigenbasisAsBasis`, with its defining equation `eigenbasisAsBasis_apply`), its
  coordinate orthonormality (`eigenbasisAsBasis_orthonormal_sum`), the dual CAR
  (`eigenbasis_dual_annihilation_creation_anticomm`) and the smeared-annihilator vacuum kill
  (`spinfulAnnihilationFromVector_mulVec_vacuum`) remain in `GeneralFlatBandEigenbasis.lean` — all
  but the coordinate-orthonormality one still consumed by `GeneralFlatBandSpanning.lean`, while the
  coordinate-orthonormality lemma is instead consumed by `HubbardImpossibilityLowUTrialCore.lean`.
  **Theorem 11.17 PR4 (Issue #4363, `GeneralFlatBandSpanning.lean`): eq. (11.3.46) Fock spanning
  (hard direction)** — the eigenvalue equation for the transported eigenbasis, the ground-state
  annihilation `Ĉ_σ(ē_j)Φ=0` for every nonzero-eigenvalue mode, the eigenmode number operator
  `n̂_{j,σ}=Ĉ†_σ(e_j)Ĉ_σ(ē_j)` with its creation commutation `[n̂,Ĉ†_τ(e_k)]=δ_{jk}δ_{στ}Ĉ†_τ(e_k)`,
  its diagonality in the occupation basis `n̂_{j,σ}occMon(g)=g(j,σ)·occMon(g)` (list induction), the
  **coefficient vanishing** (ground-state occupation-basis coefficient = 0 on any config occupying a
  nonzero-eigenvalue mode), and the capstone **`flatBand_groundState_mem_flatFockSpan`**: a
  flat-band ground state lies in the span of the flat-band-supported (zero-eigenvalue) occupation
  monomials (`IsFlatSupported`). **Theorem 11.17 PR5 (Issue #4363, `GeneralFlatBandFilling.lean`):
  filling-refined eq. (11.3.46)** — the total fermion number operator is diagonal in the occupation
  basis (`N̂ occMon(g)=|occupied(g)|·occMon(g)`, list induction via `[N̂,Ĉ†(w)]=Ĉ†(w)`), so a
  `D₀`-electron ground state has occupation-basis coefficients supported on the `D₀`-electron
  configs; combined with the flat-band coefficient vanishing this gives
  `flatBand_groundState_atFilling_mem_flatFockSpan` (flat-band ground state ∈ span of flat-supported
  occupation monomials with exactly `D₀` occupied modes). **Theorem 11.17 PR6 (Issue #4363,
  `GeneralFlatBandMuTransport.lean`): transport of eq. (11.3.46) to the special basis** — the
  coordinate identity `ker T = span{μ_z}` (finrank transport via WithLp), the invariance of the
  `μ`-Slater Fock submodule `generalFlatBandFockSubmodule μ` under `Ĉ†_σ(w)` for `w ∈ span{μ_z}`,
  and the capstone `flatBand_groundState_mem_generalFlatBandFockSubmodule`: a flat-band ground state
  at filling lies in the `μ`-Slater Fock submodule of the special basis (since the flat-supported
  eigenbasis monomials use only flat eigenvectors, each ∈ `ker T = span{μ_z}`). **Theorem 11.17 PR7
  in progress (Issue #4363, `GeneralFlatBandSpinConfig.lean`): index-mode number-operator machinery
  toward eq. (11.3.47)** — the site-dual CAR localized on the index set I
  (`{ĉ_{z,σ},â†_{μ_{z'},τ}}=δ_{στ}δ_{zz'}μ_z(z)`), the index-mode number operator
  `n̂^μ_{z,σ}=â†_{μ_z,σ}ĉ_{z,σ}` with its creation commutation, its diagonality in the μ-Slater
  states (`n̂^μ_{z,σ}|qs⟩=μ_z(z)·count·|qs⟩`, list induction), and the **no double occupancy of
  index modes** `n̂^μ_{z,↑}n̂^μ_{z,↓}Φ=0` (operator identity = `â†â†·generalCDownUp` + `ĉ_↓ĉ_↑Φ=0`).
  **Theorem 11.17 PR8 in progress (Issue #4363, `GeneralFlatBandSpinRep.lean`): tight `I`-mode
  transport toward eq. (11.3.47)** — the special basis `{μ_z}` extends to a full `Fin(M+1)`-basis
  `eμ` (`exists_extended_special_basis`); an `I`-mode `μ`-Slater state equals a mode monomial over
  `eμ` (`generalFlatBandSlaterState_eq_generalModeMonomial`, carrying them into `generalOccBasis eμ`
  for linear independence); the tight `I`-mode `μ`-Slater Fock submodule
  (`generalFlatBandIModeFockSubmodule`) is invariant under index-mode creation, and a flat-band
  ground state lies in it (`flatBand_groundState_mem_imode`, resolving the `z∉I` subtlety).
  Remaining: coefficient extraction (PR7 no-double-occ + PR5 filling ⟹ one spin per index, eq.
  11.3.47) + sign propagation (11.3.49) + connectivity capstone);
- **Theorem 11.17 PR9 (Issue #4363, `GeneralFlatBandSpinConfigRepCore.lean` for the index-support /
  coefficient-extraction machinery [`IsIdxSupported`, `flatBandSpecialIdxInv*`,
  coefficient-vanishing facts] + `GeneralFlatBandSpinConfigRep.lean` for the assembled
  representation theorems, split for build speed): eq. (11.3.47) spin-configuration capstone** — a
  left inverse `idxInv` of the extended-basis index map on `I` (`flatBandSpecialIdxInv`);
- the bridge `occMon_eμ g = Π_{z∈I} â†_{μ_z,σ}` for `idx(I)`-supported `g`
  (`generalOccMonomial_eq_generalFlatBandSlaterState_of_idxSupported` + preimage-list count);
- the double index-mode number operator diagonal on supported `occMon_eμ` (eigenvalue `μ_z(z)²[g(idx
  z,↑)][g(idx z,↓)]`);
- the three coefficient-vanishing facts for `Φ`'s `generalOccBasis eμ`-representation — support
  (`flatBand_groundState_eμ_repr_eq_zero_of_not_idxSupported`, via
  `Basis.repr_support_subset_of_mem_span`), no double occupancy
  (`flatBand_groundState_eμ_repr_eq_zero_of_doublyOccupied`), filling (general-basis
  `generalOccBasis_repr_eq_zero_of_card_ne`);
- assembled into `flatBand_groundState_mem_spinConfigSpan` (`Φ ∈ span` of the one-spin-per-index
  `μ`-Slater states — eq. (11.3.47), sorry-free, axiom-clean). **Theorem 11.17 PR10 (Issue #4363,
  `GeneralFlatBandSpinConfigRep.lean`): eq. (11.3.47) explicit one-spin-per-index** — the pigeonhole
  `flatBandSpinConfig_occupied_per_index` (a spin-config occupation occupies every index mode `idx
  z`, since the first-coordinate projection is injective on the occupied finset by
  no-double-occupancy and `|occupied| = D₀ = |I|`) + corollary
  `flatBandSpinConfig_exactlyOne_per_index` (exactly one spin per index, combining with
  no-double-occupancy). **Theorem 11.17 PR11 (Issue #4363, `GeneralFlatBandSpinConfigRep.lean`): eq.
  (11.3.47) `σ`-parametrised form** — `flatBandSpinConfigOcc`/`flatBandSpinConfigState` (the
  one-spin-per-index occupation / `μ`-Slater state `Π_{z∈I} â†_{μ_z,σ_z}|vac⟩` of a spin
  configuration `σ : Fin(M+1)→Fin 2`);
- `flatBandSpinConfig_eq_spinConfigOcc` (every surviving spin-config occupation `=
  flatBandSpinConfigOcc` of its spin function);
- capstone `flatBand_groundState_mem_spinConfigStateSpan` (`Φ ∈ span (range
  flatBandSpinConfigState)` = eq. (11.3.47) `σ`-form, the `C(σ)` foundation for eq. 11.3.48).
  **Theorem 11.17 PR12 (Issue #4363, `GeneralFlatBandSignPropagation.lean`): spin-config state
  linear independence** — `flatBandSpinConfigState_linearIndependent` (the states
  `flatBandSpinConfigState`, indexed by spin configurations `s : I → Fin 2`, are distinct elements
  of `generalOccBasis eμ` hence linearly independent;
- via injectivity of `flatBandSpinConfigOcc` on `I`-restrictions + `Basis.linearIndependent.comp`),
  making the `C(σ)` coefficients well-defined for the sign argument. **Theorem 11.17 PR13 (Issue
  #4363, `GeneralFlatBandSignPropagation.lean`): explicit `C(σ)` sum + Slater form** —
  `flatBandSpinConfigOcc_idxSupported`;
- `flatBandSpinConfigState_eq_slaterState` (each spin-config state = `generalFlatBandSlaterState μ`
  of its preimage list, so the proved double-annihilation peel engine applies);
- `flatBandSpinConfigOcc_congr` (the occupation depends only on σ|_I) +
  `flatBand_groundState_eq_spinConfigStateSum` (`Φ = Σ_s C(s)·flatBandSpinConfigState (extend s)`
  explicitly, indexed by `s : I → Fin 2` to match the linear-independence index type, via
  `Submodule.mem_span_range_iff_exists_fun`) — the explicit `C(σ)` form of eqs. (11.3.47)/(11.3.48).
  **Theorem 11.17 PR14 (Issue #4363, `GeneralFlatBandSignPropagation.lean`): eq. (11.3.48) raw
  form** — `flatBandSpinConfigState_cDownUp_eq_slaterDoubleAnnih` (the site double-annihilation
  `ĉ_{x,↓}ĉ_{x,↑}` of a spin-config state = double annihilation of its μ-Slater preimage list, so
  the proved peel engine `generalFlatBand_double_siteAnnihilation_peel` expands it) +
  `flatBand_cDownUp_spinConfigSum_eq_zero` (the `C(σ)`-weighted sum of double-annihilated
  spin-config states vanishes for every site `x`, from `ĉ_{x,↓}ĉ_{x,↑}Φ=0`) — eq. (11.3.48) LHS in
  `C(σ)` form. **Theorem 11.17 PR15 (Issue #4363, `GeneralFlatBandSignPropagation.lean`): spin-aware
  peel vanishing** — `generalFlatBand_siteAnnihilation_eq_zero` (ĉ_{x,σ}|qs⟩=0 if every mode has
  μ_{q.1}(x)=0 or wrong spin — every peel term vanishes;
- general analogue of the proved Thm 11.11 `flatBand_siteAnnihilation_eq_zero`) +
  `flatBandSpinConfigState_cDownUp_eq_zero_of_disconnected` (ĉ_{x,↓}ĉ_{x,↑}|s⟩=0 when x connects to
  no index mode — the trivial branch of eq. 11.3.48). **Theorem 11.17 PR16 (Issue #4363,
  `GeneralFlatBandSignPropagation.lean`): μ-Slater permutation scaling** —
  `generalFlatBandSlaterState_swap` (swapping the first two creations negates the state) +
  `generalFlatBandSlaterState_perm` (a permutation of the creation list scales the Slater state by a
  nonzero ±1 sign;
- the generalFlatBandSlaterState analogue of `generalModeMonomial_perm`), letting list orderings
  (opaque preimage list vs. canonical order) be compared up to a tracked sign for the peel-term
  collection. **Theorem 11.17 PR17 (Issue #4363, `GeneralFlatBandSignPropagation.lean`): canonical
  spin-config list** — `flatBandSpinConfigOcc_occFinset` (occupied finset = {(idx z,σ z):z∈I});
- `flatBandSpinConfigList` (the sorted creation list `(z,σ z)` for `z∈I`, general analogue of Thm
  11.11 `flatBandAlphaSpinList`) + nodup/toFinset + `flatBandSpinConfigList_perm_preimageList` (perm
  of the opaque preimage list);
- `flatBandSpinConfigState_eq_smul_canonical` (the spin-config state = nonzero-sign·Slater of the
  canonical list — the orbital-ordered form for explicit peel positions/signs). **Theorem 11.17 PR18
  (Issue #4363, `GeneralFlatBandSignPropagation.lean`): cDownUp two-head extraction** —
  `generalFlatBand_siteAnnihilation_head` (ĉ_{x,σ} removes the leading matching-spin creation (z,σ)
  with amplitude μ_z(x) when rest is disconnected;
- general analogue of Thm 11.11 `flatBand_siteAnnihilation_head`) +
  `generalFlatBand_cDownUp_two_head` (ĉ_{x,↓}ĉ_{x,↑} removes the leading up head (a,↑) and down head
  (b,↓), leaving μ_a(x)·μ_b(x)·Slater(rest) — the seed of the eq. 11.3.48 sign relation;
- analogue of Thm 11.11 `flatBand_cDownUp_two_head`). **Theorem 11.17 PR19 (Issue #4363,
  `GeneralFlatBandSignPropagation.lean`): cDownUp swapped two-head** —
  `generalFlatBand_cDownUp_two_head_swap` (ĉ_{x,↓}ĉ_{x,↑} on the swapped down–up head pair
  (a,↓)(b,↑) gives −μ_a(x)μ_b(x)·Slater(rest) — the OPPOSITE sign from the canonical up–down
  assignment, one extra Koszul transposition;
- via `generalFlatBandSlaterState_swap` + two-head). This relative −1 is the seed of the eq.
  (11.3.49) sign relation `C(σ)=C(σ_{z₁↔z₂})` (analogue of Thm 11.11 `flatBand_cDownUp_swap`).
  **Theorem 11.17 PR20 (Issue #4363, `GeneralFlatBandSignPropagation.lean`): Slater
  move-pair-front** — `generalFlatBandSlaterState_move_one_past_two` (moving the head past the next
  two creations is +1, two transpositions) + `generalFlatBandSlaterState_move_pair_front`
  (`Slater(l₁ ++ a::b::l₂) = Slater(a::b::(l₁++l₂))`, sign +1;
- general-basis analogue of Thm 11.11 `flatBandModeMonomial_move_pair_front`), bringing an arbitrary
  occupied pair to the head for the cDownUp two-head extraction. **Theorem 11.17 PR21 (Issue #4363,
  `GeneralFlatBandSignPropagation.lean`): cDownUp extract pair at arbitrary position** —
  `generalFlatBand_cDownUp_extract_pair` (ĉ_{x,↓}ĉ_{x,↑} on `l₁ ++ (a,↑)::(b,↓)::l₂` with l₁,l₂
  disconnected from x removes the pair → μ_a(x)μ_b(x)·Slater(l₁++l₂), via move-pair-front +
  two-head) + `generalFlatBand_cDownUp_extract_pair_swap` (swapped (a,↓)(b,↑) →
  −μ_a(x)μ_b(x)·Slater(l₁++l₂);
- the per-pair eq. 11.3.49 relative −1). **Theorem 11.17 PR22 (Issue #4363,
  `GeneralFlatBandSignPropagation.lean`): canonical-Slater D-coefficient expansion** —
  `flatBand_groundState_eq_canonicalSlaterSum` (Φ = Σ_s D(s)·generalFlatBandSlaterState μ
  (flatBandSpinConfigList σ_s), indexed by s : I → Fin 2, in the CANONICAL sorted order;
- unlike the flatBandSpinConfigState coefficients which carry the existential ±1 canonical sign, the
  D(s) are order-fixed, making the eq. 11.3.49 sign-relation comparison clean). **Theorem 11.17 PR23
  (Issue #4363, `GeneralFlatBandSlaterReorder.lean`): cDownUp canonical double-peel** —
  `cDownUp_canonical_eq_doublePeel` (ĉ_{x,↓}ĉ_{x,↑} on Slater(flatBandSpinConfigList σ) = the
  explicit position double-sum over the orbital-ordered canonical list, via the proved engine
  `generalFlatBand_double_siteAnnihilation_peel`), the explicit form whose (i,j) terms are collected
  by removed index pair in the reindexing step. **Theorem 11.17 PR24 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): canonical list structure** — `flatBandSpinConfigList_length`
  (= |I|) + `flatBandSpinConfigList_mem_snd_eq` / `flatBandSpinConfigList_get_snd_eq` (each mode is
  (z, σ z): the spin at a position equals σ of its index — lets the double-peel spin guard be read
  as a condition on σ in the reindexing). **Theorem 11.17 PR25 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): occupation-monomial coordinate** — `generalOccMonomial_repr`
  (`(generalOccBasis eμ).repr (occMon_eμ h) g = [h = g]`, since occMon_eμ h is the basis vector;
- via `Basis.repr_self` + `Finsupp.single_apply`) — the coordinate functional projecting the double
  peel onto a fixed (D₀−2)-config in the collection step. **Theorem 11.17 PR26 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): canonical eraseIdx structure** —
  `flatBandSpinConfigList_eraseIdx_mem_snd_eq` (each mode of a one-erased canonical list is still
  (z, σ z)) + `flatBandSpinConfigList_eraseIdx_nodup` (still nodup);
- lets the (D₀−1)/(D₀−2)-electron states from the double peel be treated as spin-config lists over a
  smaller index set. **Theorem 11.17 PR27 (Issue #4363, `GeneralFlatBandSlaterReorder.lean`):
  canonical position↔index** — `flatBandSpinConfigList_getElem` (the mode at position i is (z_i, σ
  z_i) where z_i is the i-th smallest index of I;
- via `List.getElem_map` on the sorted list), pinning each double-peel position to its index for the
  removed-pair collection. **Theorem 11.17 PR28 (Issue #4363, `GeneralFlatBandSlaterReorder.lean`):
  canonical double-peel coordinate expansion** — `cDownUp_canonical_repr_eq_sum` (applying the
  occ-basis coordinate functional `(generalOccBasis eμ).repr · g` to ĉ_{x,↓}ĉ_{x,↑}Slater(canonical
  σ) distributes by linearity over the position double-sum, leaving the coordinates of the
  doubly-erased (D₀−2)-Slater states weighted by the peel amplitudes and Koszul signs). **Theorem
  11.17 PR29 (Issue #4363, `GeneralFlatBandSlaterReorder.lean`): Slater-over-I coordinate bridge** —
  `generalFlatBandSlaterState_over_I_repr` (for a nodup list qs of index modes, `(generalOccBasis
  eμ).repr (Slater μ qs) g = z·[config(qs)=g]` for a nonzero sign z, config(qs) = occupation of
  {(idx z,σ):(z,σ)∈qs};
- via the μ-Slater↔mode-monomial bridge + permutation scaling + the occupation-monomial coordinate).
  Computes the coordinate of every (D₀−2)-Slater state from the double peel. **Theorem 11.17 PR30
  (Issue #4363, `GeneralFlatBandSlaterReorder.lean`): nodup eraseIdx toFinset** —
  `List.toFinset_eraseIdx_of_nodup` (generic: `(l.eraseIdx i).toFinset = l.toFinset.erase l[i]` for
  nodup l) — the engine tracking which mode a double-peel eraseIdx removes. **Theorem 11.17 PR31
  (Issue #4363, `GeneralFlatBandSlaterReorder.lean`): idxConfigOf + single-erase** — `idxConfigOf`
  (the idx-image occupation config {(idx z,σ):(z,σ)∈qs} that
  `generalFlatBandSlaterState_over_I_repr` reads) + `idxConfigOf_eraseIdx` (one-erase zeroes the
  config at the removed mode (idx qs[i].1, qs[i].2);
- via `List.eraseIdx_map` + the nodup eraseIdx-toFinset). **Theorem 11.17 PR32 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): idxConfigOf double-erase** — `idxConfigOf_eraseIdx_eraseIdx`
  (erasing positions i then j zeroes the config at the two removed modes;
- via two applications of `idxConfigOf_eraseIdx`) — the config of every (D₀−2)-Slater state from the
  double peel in terms of the two removed modes. **Theorem 11.17 PR33 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): idxConfigOf canonical = spinConfigOcc** —
  `idxConfigOf_flatBandSpinConfigList` (`idxConfigOf idx (flatBandSpinConfigList I σ) =
  flatBandSpinConfigOcc I idx σ`), connecting the eraseIdx-tracking config to the established
  spin-config-occupation machinery (PR9-11). **Theorem 11.17 PR34 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): canonical index injectivity** —
  `flatBandSpinConfigList_get_fst_inj` (the index at position i determines i;
- each mode (z,σz) + nodup ⟹ equal indices give equal positions) — the injectivity behind "exactly
  one (i,j) per removed pair". **Theorem 11.17 PR35 (Issue #4363,
  `GeneralFlatBandSlaterReorder.lean`): canonical membership + position existence** —
  `flatBandSpinConfigList_mem` (z∈I ⟹ (z,σz)∈canonical) + `flatBandSpinConfigList_exists_pos` (∃
  position with mode (z,σz));
- with the index injectivity (PR34, uniqueness) this pins the unique position carrying each index.
  **Theorem 11.17 PR36 (Issue #4363, `GeneralFlatBandSlaterReorder.lean`): unique position of
  index** — `flatBandSpinConfigList_existsUnique_pos` (each z∈I sits at exactly one canonical-list
  position;
<!-- legacy-source:end:149:149 -->
