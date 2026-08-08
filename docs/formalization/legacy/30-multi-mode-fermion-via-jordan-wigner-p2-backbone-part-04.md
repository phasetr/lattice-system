---
layout: page
title: "Legacy catalogue: Multi-mode fermion via Jordan–Wigner (P2 backbone) (part 4 of 4)"
permalink: /formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/
---

# Legacy catalogue: Multi-mode fermion via Jordan–Wigner (P2 backbone) (part 4 of 4)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Fermions and Hubbard models](/lattice-system/formalization/legacy/#group-fermions-hubbard)

<!-- legacy-source:start:2605:2731 -->
| Lean name | Statement | File |
|---|---|---|
| <a id="tasaki-chapter-10-part-02"></a> `theorem_10_4_lieb_repulsive_half_filling` | **Theorem 10.4** (Tasaki §10.2.2, p. 350, **AXIOM**): at half-filling `N = \|Λ\|`, the ground subspace is nonzero, energy-minimal, consists entirely of total-spin `S₀ = \|\|A\|−\|B\|\|/2` states (Casimir `S₀(S₀+1)`), and has dimension exactly `\|A\|−\|B\|+1` (the unavoidable SU(2) multiplet degeneracy). Lieb's reflection positivity via the Shiba transformation → faithful documented axiom. | `Fermion/JordanWigner/Hubbard/LiebRepulsive.lean` |
| <a id="tasaki-chapter-9-part-03"></a> `shibaConfig` / `shibaConfigEquiv` / `shibaConfig_up` / `shibaConfig_down` / `shibaConfig_involutive` | **Shiba configuration involution** (Tasaki §9.3.3, eq. (9.3.48), p. 335): particle-hole flip on down-spin occupations `(n̂↑, n̂↓) ↦ (n̂↑, 1−n̂↓)` as the permutation part of the Shiba transformation for Theorem 10.4. `shibaConfig` is the down-species flip; `shibaConfigEquiv` packages it as an involution (`Equiv`); proofs establish it is self-inverse with fixed up-config and flipped down-config. **PR #4950 (c2)**: axiom-free infrastructure. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaTransform.lean` |
| `shibaPermMatrix` / `shibaPermMatrix_apply` / `shibaPermMatrix_isHermitian` / `shibaPermMatrix_conj_diagonal` | **Shiba permutation matrix** (Tasaki §9.3.3, eqs. (9.3.48)/(9.3.50), pp. 335–336): the permutation matrix realizing the Shiba involution on Fock configurations; Hermitian (`Pᴴ=P`); conjugating a diagonal by `P` reindexes via `shibaConfig`. **PR #4950 (c3)**: unsigned permutation part of the full Shiba unitary; axiom-free infrastructure. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaUnitary.lean` |
| `symmetricRepulsiveInteractionDiag` / `symmetricRepulsiveHubbardInteraction_eq_diagonal` / `shibaConfig_apply_up` / `shibaConfig_apply_down` / `symmetricRepulsiveInteractionDiag_shibaConfig` / `shibaPermMatrix_conj_symmetricInteraction` / `shibaSignedUnitary` / `shibaSignedUnitary_conjTranspose` / `shibaSignedUnitary_conj_symmetricInteraction` | **Shiba interaction conjugation** (Tasaki §9.3.3, eqs. (9.3.47)/(9.3.54), pp. 334–336): the symmetric repulsive interaction `Ĥ_{int}'` is diagonal; Shiba flip negates each term (n̂↓−½ changes sign); **capstone `shibaSignedUnitary_conj_symmetricInteraction`**: the signed-Shiba unitary satisfies `Ûᴴ·Ĥ_{int}'·Û = −Ĥ_{int}'` (eq. 9.3.54). **PR #4950 (c5)**: discharges axiom-free interaction sign-flip; consumed by the c6 full-conjugation capstone (PR #4952). | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaInteraction.lean` |
| `gaugeSign` / `shibaGauge` / `shibaCrossingSpecies` / `shibaJwFlipParity` / `shibaSignFn` / `gaugeSign_mul_of_bipartite` / `shibaGauge_star_mul_self` / `shibaSignFn_star_mul_self` / `shibaSignedUnitary_conj_symmetricKinetic` | **Shiba kinetic-term conjugation** (Tasaki §9.3.3, eq. (9.3.52), p. 336): the Shiba transformation leaves the symmetric kinetic term invariant `Ûᴴ·Ĥ_kin·Û = Ĥ_kin`. Mechanism: on a bipartite bond `x∈A, y∈B`, the particle-hole flip converts `ĉ†_x ĉ_y` into `−ĉ†_y ĉ_x` (CAR sign −1) while the sublattice gauge contributes `ε_x ε_y = −1`; the two signs multiply to `+1`, restoring the symmetric term `t_xy = t_yx`. **capstone `shibaSignedUnitary_conj_symmetricKinetic`**: kinetic invariance; `shibaSignFn_star_mul_self` (|s|=1) feeds the c6 conjugation. **PR #4951 (c4)**: axiom-free kinetic-term preservation. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaKinetic.lean` |
| `symmetricHubbardOnSite_expand` / `hubbardKinetic_add` / `hubbardKinetic_diagonal` / `neg_symmetricRepulsiveInteraction_eq` / `shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive` | **Shiba full conjugation repulsive→attractive** (Tasaki §10.2.2, eqs. (10.2.10)/(10.2.11), p. 352): combining c4 (kinetic invariance) and c5 (interaction sign-flip), **capstone `shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive`**: `Ûᴴ·(Ĥ_kin+Ĥ_int')·Û = attractiveHubbardHamiltonian (T + diag(U/2)) U − ¼Σ_x U_x` (eq. 10.2.10). The chemical shift of `−Ĥ_int'` (from `(n̂↑−½)(n̂↓−½)=n̂↑n̂↓−½(n̂↑+n̂↓)+¼`, eq. 10.2.11) is absorbed into the hopping diagonal, leaving the negative scalar constant. **PR #4952 (c6)**: axiom-free; consumes the c4/c5 milestones; feeds the c7 balanced-sector transport. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaConjugation.lean` |
| `sum_spinful_split` / `fermionTotalNumber_eq_diagonal` / `fermionTotalSpinZ_eq_diagonal` / `shibaSignedUnitary_conj_diagonal` / `shibaSignedUnitary_conj_totalNumber` / `shibaSignedUnitary_conj_totalSpinZ` | **Shiba number/spin-z charge exchange** (Tasaki §§9.3.3/10.2.2, eqs. (9.3.48)/(9.3.50), pp. 334–352): the charges `N̂`, `Ŝ³` are diagonal in the Fock basis, and the Shiba flip interchanges them — `Û·N̂·Ûᴴ = 2Ŝ³ + (N+1)·1` and `Ûᴴ·Ŝ³·Û = ½(N̂ − (N+1)·1)`. **PR #4953 (c7 foundation)**: axiom-free; the sector-correspondence identities feeding the balanced-sector transport. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaSector.lean` |
| `spinZSectorEuclidean` / `repulsiveSpinZSector_ground_unique` | **Theorem 10.4, general spin-`z`-sector portion** (Tasaki §10.2.2, pp. 350–352, eqs. (10.2.10)/(10.2.11), **PROVED axiom-free**): for any `N`, an even electron number `0 < Ne < 2(N+1)`, connected real symmetric bipartite hopping and on-site repulsion `U_x > 0`, the symmetric (`μ = U/2`) repulsive Hubbard Hamiltonian has a **unique** ground state on the spin-`z` sector `Ŝ³ = m` with `m = (Ne−(N+1))/2`. Proved by transporting Theorem 10.2 (number sector `N̂ = Ne`) through the Shiba unitary (c6 conjugation + c7 charge exchange `Û N̂ Ûᴴ = 2Ŝ³+(N+1)·1`, so `Ne ↦ m`). The total-spin value is **not** claimed — `Û` maps `Ŝ²` to the η-pseudospin Casimir; identifying it needs the deferred degenerate perturbation axiom. Half-integer `m` (odd `Ne`) is out of scope (Theorem 10.2 requires `Even Ne`). **PR #4955 (general-sector PR-1)**. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveBalancedGround.lean` |
| `shibaCrossingSpecies_update_flip_product` / `shibaGauge_update_down_flip_product` / `shibaSignedUnitary_conj_siteSpinPlus` / `shibaSignedUnitary_conj_siteSpinMinus` / `shibaSignedUnitary_conj_spinPlusMinus` | **Shiba spin-operator conjugation** (Tasaki §10.2.2, eq. (10.2.13), p. 353, **PROVED axiom-free**): the Shiba flip sends the transverse spin operators to the on-site pair (η-pairing) operators — `Ûᴴ Ŝ⁺_x Û = ε_x·ĉ†_{x↑}ĉ†_{x↓}`, `Ûᴴ Ŝ⁻_x Û = ε_x·ĉ_{x↓}ĉ_{x↑}` (`ε_x` = sublattice gauge), hence **capstone `shibaSignedUnitary_conj_spinPlusMinus`**: `Ûᴴ(Ŝ⁺_xŜ⁻_y)Û = ε_xε_y·hubbardPairCorrelationOp N x y`. Basis-vec computation mirroring the Shiba down-hop conjugation. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveShibaSpinOp.lean` |
| `fermionSpinTransverse` / `vectorExpectation` / `SameSublattice` / `theorem_10_5_shen_qiu_tian_transverse_sign` | **Theorem 10.5** (Shen–Qiu–Tian; Tasaki §10.2.2, p. 351/353, eqs. (10.2.7)/(10.2.8)/(10.2.13), **PROVED axiom-free** on the general spin-`z` sector `Ŝ³=m` (PR #4956)): for any `N`, even electron number `0<Ne<2(N+1)`, the transverse spin correlation `⟨φ\| Ŝ¹_xŜ¹_y+Ŝ²_xŜ²_y \|φ⟩` (`= ½(Ŝ⁺_xŜ⁻_y+Ŝ⁻_xŜ⁺_y)`) in the unique repulsive-Hubbard ground state on the sector `Ŝ³=m` (`m=(Ne−(N+1))/2`) is real, strictly positive when `x,y` are in the same sublattice and strictly negative otherwise. Proof: transport `φ=Ûφ_attr` through the Shiba unitary via the general-sector uniqueness `repulsiveSpinZSector_ground_unique`, apply the spin↔pair conjugation (eq. 10.2.13) and Tian's positivity (Theorem 10.3). Only the correlation sign is claimed (total-spin value not asserted); the balanced `Ŝ³=0` sector is the `Ne=N+1` special case. | `Fermion/JordanWigner/Hubbard/LiebRepulsiveCorrelation.lean` |
| `fermionStaggeredCasimirOp` / `theorem_10_6_lieb_ferrimagnetism` | **Theorem 10.6** (Shen–Qiu–Tian ferrimagnetism; Tasaki §10.2.3, p. 354, eqs. (10.2.16)/(10.2.17), **AXIOM**): every normalized repulsive-Hubbard ground state satisfies `⟨v\| (Ô_L)² \|v⟩ ≥ ((\|A\|−\|B\|)/2)²`, where `(Ô_L)² = Σ_{x,y} ε_xε_y Ŝ_x·Ŝ_y` (staggered sign `ε_x=±1` per sublattice) — ferrimagnetic long-range order. Reuses `IsLiebRepulsiveModel`. Reflection positivity → faithful documented axiom. | `Fermion/JordanWigner/Hubbard/LiebFerrimagnetism.lean` |
| `bipartiteSignMatrix` / `proposition_10_7_charpoly_neg_eq` / `proposition_10_7_zero_mode_lower_bound` | **Proposition 10.7** (Tasaki §10.2.3, p. 356, **PROVED axiom-free**): for a bipartite real symmetric hopping `T`, (i) the single-electron spectrum is symmetric about zero — `(-T).charpoly = T.charpoly` via the gauge `D T D = -T` (`D = diag(±1)`); (ii) there are at least `\|A\|−\|B\|` zero modes — `Module.finrank (ker T.mulVecLin) ≥ \|A\|−\|B\|` via the `A→B` block map and rank–nullity. The one Chapter-10 item that is finite-dim linear algebra. | `Fermion/JordanWigner/Hubbard/BipartiteSpectrum.lean` |
| `totalPairAnnihilationOperator` / `totalPairCreationOperator` / `totalPairCorrelationOperator` / `symmetricAttractiveHubbardHamiltonian` / `liebShenQiuPairLowerBound` / `theorem_10_8_lieb_shen_qiu_superconductivity` | **Theorem 10.8** (Lieb–Shen–Qiu superconductivity; Tasaki §10.2.3, p. 359, eq. (10.2.22), **AXIOM**): for the **symmetric** attractive Hubbard model `Ĥhop − Σ_x U_x(n̂_↑−½)(n̂_↓−½)` (eq. (10.2.21)) on a bipartite lattice with even `N`, `2\|B\| ≤ N ≤ 2\|A\|`, the unique ground state satisfies `⟨φ\| b̂† b̂ \|φ⟩ ≥ (\|A\|−N/2)(N/2−\|B\|)` with `b̂ = Σ_x ĉ_{x↓}ĉ_{x↑}` — off-diagonal long-range order (fermion-pair condensation / superconductivity). Reflection positivity + Theorem 10.2 uniqueness → faithful documented axiom. | `Fermion/JordanWigner/Hubbard/LiebShenQiu.lean` |

#### Kubo–Kishi finite-temperature susceptibility bound (Tasaki §10.2.5, Theorem 10.11, AXIOM)

The finite-temperature version of Lieb's theorem (Kubo–Kishi): at half-filling the repulsive Hubbard model's charge and on-site pairing susceptibilities are bounded uniformly in temperature and wave number, so there is no CDW or superconducting long-range order. Tasaki states it **without proof**, citing Kubo–Kishi, *Phys. Rev. B* **41**, 4866 (1990) → recorded as a **documented axiom** (same policy as `mielke_theorem_11_13` / `theorem_10_4`).

| Lean name | Statement | File |
|---|---|---|
| `imagTimeEvolve` / `duhamelStaticSusceptibility` | (generic) the imaginary-time (Wick-rotated) Heisenberg evolution `A(τ) = e^{τH}A e^{-τH}` and the **Duhamel (Kubo) static isothermal susceptibility** `χ_{AB}(β) = ∫₀^β (⟨A(τ)B⟩_β − ⟨A⟩_β⟨B⟩_β) dτ` (Tasaki §10.2.5, the fluctuation–dissipation form of the second-derivative susceptibilities eqs. (10.2.53)/(10.2.54); prefactor `1`, `ℂ`-valued `intervalIntegral`) | `Quantum/GibbsState/Duhamel.lean` |
| `grandCanonicalRepulsiveHubbard` / `fourierCharacter` / `chargeFourierMode` / `pairFieldFourierMode` / `chargeSusceptibility` / `pairSusceptibility` | the grand-canonical Hamiltonian `Ĥ − μN̂` (core of eq. (10.2.52)); the 1D wave-number character `w_x = exp(2πi k x/(N+1))` (eq. (10.2.55), `|w_x|=1`, genuine periodic lattice character); the charge Fourier mode `ñ_q = |Λ|^{-1/2}Σ_x w_x n̂_x` and the pairing Fourier mode `p̂_q = |Λ|^{-1/2}Σ_x w_x(ĉ†_{x↑}ĉ†_{x↓}+ĉ_{x↓}ĉ_{x↑})`; and the charge / on-site pairing susceptibilities `χ^c_q`, `χ^p_q` as Duhamel two-point functions of these modes at `±q` (eqs. (10.2.53)/(10.2.54)) | `Fermion/JordanWigner/Hubbard/LiebKuboKishi.lean` |
| `theorem_10_11_kubo_kishi_susceptibility_bound` | **Theorem 10.11** (Kubo–Kishi; Tasaki §10.2.5, pp. 368–369, eqs. (10.2.52)–(10.2.56), **AXIOM**, PR #4957): for the uniform repulsive Hubbard model (`U > 0`, eq. (10.2.5)) on a bipartite real symmetric connected hopping `T` (Theorem 10.4 conditions except electron number) at half-filling `μ = U/2`, for every `β > 0` and every wave number `k` the susceptibilities are real and `χ^c_k(β, U/2) ≤ 1/U`, `χ^p_k(β, U/2) ≤ 2/U` (eq. (10.2.56)) — no CDW or superconducting order at finite temperature. Tasaki states it without proof, citing Kubo–Kishi, *Phys. Rev. B* **41**, 4866 (1990) → faithful documented axiom. | `Fermion/JordanWigner/Hubbard/LiebKuboKishi.lean` |

#### Hubbard effective Hamiltonian on the hard-core sector (Tasaki §11.2)

| Lean name | Statement | File |
|---|---|---|
| <a id="tasaki-chapter-11-part-03"></a> `hubbardEffectiveHamiltonian N t U` | the hard-core compression `Ĥ_eff = P̂_hc · H · P̂_hc` of the full Hubbard Hamiltonian (Tasaki §11.2; 1st ed., pp. 381-388) | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonian.lean` |
| `hubbardEffectiveHamiltonian_isHermitian` | `Ĥ_eff` is Hermitian for Hermitian `t` and real `U` | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonian.lean` |
| `hubbardEffectiveHamiltonian_mulVec_eq_projected_kinetic_of_mem` | `U → ∞` reduction: on a hard-core vector, `Ĥ_eff ψ = P̂_hc (H_hop ψ)` (interaction drops out) | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonian.lean` |
| `hubbardEffectiveHamiltonian_mulVec_mem` | `Ĥ_eff ψ` always lies in `hubbardHardcoreSubspace` | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonian.lean` |
| `hubbardHardcoreProjection_mulVec_effectiveHamiltonian` | `P̂_hc` fixes every vector in the range of `Ĥ_eff` | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonian.lean` |

#### Tasaki ordered-creation basis (Tasaki §11.2, eq. (11.2.3))

| Lean name | Statement | File |
|---|---|---|
| `occupationOf js` | the configuration occupied exactly on the indices in a list `js` | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |
| `prod_creation_mulVec_vacuum` | a strictly index-sorted product of creation operators applied to the vacuum yields `basisVec (occupationOf js)`, every Jordan–Wigner string sign being `1` | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |
| `tasakiIndexList N τ` / `tasakiIndexList_sorted` / `mem_tasakiIndexList_iff` | the increasing list of occupied JW indices of the all-filled spin-`τ` configuration; strictly sorted; membership iff the spin label selects that orbital | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |
| `hubbardTasakiBasisState N x σ` | the (11.2.3) ordered-creation basis state `\|Φ_{x,σ}⟩ = ĉ_{x,↑} (∏_{y} ĉ†_{y,σ̄_y}) \|vac⟩` | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |
| `hubbardTasakiBasisState_eq_smul_basisVec` | `\|Φ_{x,σ}⟩ = ε • basisVec (hubbardOneHoleConfig N x σ)`, where `ε` is the single annihilation string sign | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |
| `hubbardTasakiBasisSign_mul_self` | the string sign squares to `1` | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |
| `hubbardTasakiBasisState_inner` / `hubbardTasakiBasisState_self_inner` | orthonormality inherited from `basisVec`: the pairing is the sign product times the configuration-equality indicator; self-overlap is `1` | `Fermion/JordanWigner/Hubbard/TasakiBasis.lean` |

#### Uniform-sign hole-filling action (Tasaki §11.2, eq. (11.2.4))

| Lean name | Statement | File |
|---|---|---|
| `jwSign_eq_neg_one_pow` | `jwSign N j c = (-1)^{∑_{k<j} (c k).val}` (string sign as parity of occupied modes) | `Fermion/JordanWigner/Hubbard/TasakiHopActionCore.lean` |
| `sum_spinful_reindex` | reindex a sum over the `2N+2` JW modes into a double site/spin sum | `Fermion/JordanWigner/Hubbard/TasakiHopActionCore.lean` |
| `hubbardTasakiBasisSign_eq` | the Tasaki basis sign is `ε = (-1)^x` (independent of `σ`) | `Fermion/JordanWigner/Hubbard/TasakiHopActionCore.lean` |
| `hop_jwSign_source` / `hop_jwSign_target` | the two hop string signs as `(-1)` to the occupied-site count below the source / target orbital | `Fermion/JordanWigner/Hubbard/TasakiHopActionCore.lean` |
| `hubbardTasakiHop_mulVec` | eq. (11.2.4): `ĉ†_{(x,s)} ĉ_{(z,s)} \|Φ_{x,σ}⟩ = -\|Φ_{z, σ_{z→x}}⟩` — the four fermion signs combine to the uniform `-1` (parity `2(x+z)-1` is odd) | `Fermion/JordanWigner/Hubbard/TasakiHopAction.lean` |

#### Effective-Hamiltonian matrix element (Tasaki §11.2, eq. (11.2.5))

| Lean name | Statement | File |
|---|---|---|
| `hubbardEffective_tasaki_matrixElement` | eq. (11.2.5), off-diagonal (`x ≠ y`): `⟨Φ_{y,τ} \| Ĥ_eff \| Φ_{x,σ}⟩ = -t_{x,y}` if `τ = σ_{y→x}` (configurations coincide), else `0`. Only the hole-filling channel `(x, y, σ_y)` survives the hard-core projection | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonianMatrix.lean` |
| `hubbardEffective_tasaki_matrixElement_diag` | eq. (11.2.5), diagonal (`x = y`) under no self-hopping (`∀ i, t_{ii} = 0`): `⟨Φ_{x,τ} \| Ĥ_eff \| Φ_{x,σ}⟩ = 0` — `Ĥ_eff` moves the hole off `x`, so its image is orthogonal to `\|Φ_{x,τ}⟩` | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonianMatrix.lean` |

#### Cauchy–Schwarz energy bound (Tasaki §11.2, eq. (11.2.9))

| Lean name | Statement | File |
|---|---|---|
| `HoleSpin N x` / `holeSpinMoveEquiv` | canonical hole-spin configurations (hole-site spin fixed `↑`); the hole-move bijection `HoleSpin N x ≃ HoleSpin N y` | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `hubbardEffEnergy` / `hubbardEffEnergy_expand` | the real-bilinear effective-Hamiltonian energy; its quadratic-form expansion in the Tasaki basis | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `oneHoleConfig_move_eq_iff` | the hole-move bridge: the moved configuration matches `C_{x,σ}` iff `τ` is the hole-move image | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `hubbardEffEnergy_tasaki_quadratic` | eq. (11.2.9) line 2: `⟨Φ\|Ĥ_eff\|Φ⟩ = -Σ_{x≠y} t_{y,x} Σ_σ c_{x,σ} c_{y, σ_{x→y}}` (no self-hopping) | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `tasakiQuadForm_ferro_le` | the Cauchy–Schwarz bound on the real quadratic form: `Q(Φ_↑) ≤ Q(Φ)` for `t ≥ 0` | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `hubbardWeakNagaoka_energy_bound` | eq. (11.2.9): `⟨Φ_↑\|Ĥ_eff\|Φ_↑⟩ ≤ ⟨Φ\|Ĥ_eff\|Φ⟩` (`t ≥ 0`, `t_{ii}=0`) — the ferromagnetic state is also a ground state | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `tasakiState_orthonormal` | orthonormality of the Tasaki basis (indexed by hole site and canonical hole-spin) | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |
| `tasakiExpansion_normSq` / `ferroCoeff_normSq_eq` / `tasakiFerro_normSq_eq` | eqs. (11.2.7)–(11.2.8): `‖Σ ϕ_p Φ_p‖² = Σ ϕ_p²`, and the ferromagnetic state has the same norm `‖Φ_↑‖ = ‖Φ‖` | `Fermion/JordanWigner/Hubbard/WeakNagaoka.lean` |

#### SU(2) symmetry of the effective Hamiltonian (Tasaki §11.2)

| Lean name | Statement | File |
|---|---|---|
| `fermionTotalSpinPlus_commute_hubbardHardcoreProjection` | `Ŝ^+_tot` commutes with the hard-core projection `P̂_hc` (spin operators preserve the no-double-occupancy subspace) | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonianSpinSymmetry.lean` |
| `fermionTotalSpinPlus_commute_hubbardEffectiveHamiltonian` / `fermionTotalSpinMinus_commute_hubbardEffectiveHamiltonian` | `[Ĥ_eff, Ŝ^±_tot] = 0` — the effective Hamiltonian inherits SU(2) symmetry (the backbone of the `(2S_max+1)`-degeneracy in Theorem 11.5) | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonianSpinSymmetry.lean` |
| `fermionTotalSpinZ_commute_hubbardEffectiveHamiltonian` / `fermionTotalSpinSquared_commute_hubbardEffectiveHamiltonian` | `[Ĥ_eff, Ŝ^z_tot] = 0` and `[Ĥ_eff, (Ŝ_tot)²] = 0` — `Ĥ_eff` conserves total spin, so its eigenspaces split into fixed-`S_tot` sectors (Theorem 11.5 / 11.7) | `Fermion/JordanWigner/Hubbard/EffectiveHamiltonianSpinSymmetry.lean` |

#### Weak Nagaoka spin multiplet (Tasaki §11.2.1, Theorem 11.5 core)

| Lean name | Statement | File |
|---|---|---|
| `fermionTotalSpinPlus_commutator_fermionTotalSpinMinus` | SU(2) ladder commutator `[Ŝ^+_tot, Ŝ^-_tot] = 2 Ŝ^z_tot` (Tasaki §9.3.3) | `Fermion/JordanWigner/Hubbard/WeakNagaokaTheoremCore.lean` |
| `fermionTotalSpinSquared_commute_fermionTotalSpinMinus` | `[(Ŝ_tot)², Ŝ^-_tot] = 0` — the Casimir is constant along the spin-lowering tower | `Fermion/JordanWigner/Hubbard/WeakNagaokaTheoremCore.lean` |
| `fermionTotalSpinPlus_mul_fermionTotalSpinMinus` | `Ŝ^+_tot Ŝ^-_tot = (Ŝ_tot)² − Ŝ^z_tot(Ŝ^z_tot − 1)` — raising-after-lowering via the Casimir | `Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean` |
| `fermionTotalSpinZ_mulVec_spinMinusPow` / `fermionTotalSpinSquared_mulVec_spinMinusPow` | `Ŝ^z` / Casimir towers: `(Ŝ^-_tot)^k v` has `Ŝ^z = N/2 − k` and constant Casimir, for any highest-weight `v` | `Fermion/JordanWigner/Hubbard/WeakNagaokaTheoremCore.lean` (`fermionTotalSpinZ_mulVec_spinMinusPow`) + `Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean` (`fermionTotalSpinSquared_mulVec_spinMinusPow`) |
| `spinMinusPow_ne_zero` / `spinMinusPow_linearIndependent` | the `N+1` lowered states `(Ŝ^-_tot)^k v` (`k ≤ N`) are nonzero (ladder eigenvalue `(k+1)(N−k) ≠ 0`) and linearly independent (distinct `Ŝ^z`) | `Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean` |
| `weakNagaoka_spinMultiplet` | **Theorem 11.5 core**: a nonzero highest-weight `Ĥ_eff`-eigenvector `v` (`Ŝ^+_tot v = 0`, `Ŝ^z_tot v = (N/2) v`) generates `N+1 = 2 S_max + 1` linearly independent `Ĥ_eff`-eigenvectors `(Ŝ^-_tot)^k v` at the same energy, all with `S_tot = S_max = N/2`. | `Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean` |
| `tasakiEffMatrix` / `tasakiEffMatrixUp` | the Tasaki matrix `M = Tᴴ Ĥ_eff T` of `Ĥ_eff` in the one-hole basis (Hermitian, entries `⟨Φ_q\|Ĥ_eff\|Φ_p⟩`) and its all-up principal block `M_↑` (Hermitian); `Ĥ_eff` preserves the all-up sector | `Fermion/JordanWigner/Hubbard/WeakNagaokaGroundState.lean` |
| `hubbardEffectiveHamiltonian_mulVec_tasakiState` / `_tasakiExpansion` | operator lift: `Ĥ_eff Φ_p = Σ_q ⟨Φ_q\|Ĥ_eff\|Φ_p⟩ Φ_q` and `Ĥ_eff (Σ c_q Φ_q) = Σ_q (M c)_q Φ_q` (via particle-number conservation, sector completeness `tasaki_completeness`) | `Fermion/JordanWigner/Hubbard/WeakNagaokaGroundStateCore.lean` + `Fermion/JordanWigner/Hubbard/WeakNagaokaGroundState.lean` |
| `weakNagaoka_theorem_11_5` | **Tasaki Theorem 11.5 (weak Nagaoka, effective one-hole sector)**: there exist `N+1 = 2 S_max+1` linearly independent `Ĥ_eff`-eigenvectors at the maximal-spin sector minimum energy, all with `S_tot = S_max = N/2`; the ground state is the all-up state from a minimum eigenvector of the all-up block `M_↑` (no Perron–Frobenius). | `Fermion/JordanWigner/Hubbard/WeakNagaokaGroundState.lean` |
| `weakNagaoka_theorem_11_5_global` | **Tasaki Theorem 11.5 (global form)**: for `t ≥ 0` symmetric, the all-up minimum equals the global one-hole minimum (`hermitianMinEigenvalue M_↑ = hermitianMinEigenvalue M`, via the Schwarz bound (11.2.9) ferromagnetization on the real Tasaki matrix), so the `N+1` degenerate eigenvectors are genuine **ground states** with `S_tot = S_max` | `Fermion/JordanWigner/Hubbard/WeakNagaokaGlobalMin.lean` |
| `mulVec_eq_smul_of_rayleighOnVec_eq_min` | Hermitian variational equality: a nonzero vector attaining the minimum-eigenvalue Rayleigh bound is a minimum eigenvector (companion to the variational lower bound) | `Quantum/SpinS/HermitianVariationalEquality.lean` |

| Lean name | Statement | File |
|---|---|---|
| `hubbardKineticOnGraph N G J` | spinful Hubbard kinetic operator from a `SimpleGraph G` and edge weight `J` | `Fermion/JordanWigner.lean` |
| `hubbardKineticOnGraph_commute_fermionTotalNumber` / `hubbardKineticOnGraph_isHermitian` | charge conservation always; Hermiticity for real `J` | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardHamiltonianOnGraph N G J U` | full Hubbard Hamiltonian from a graph + on-site coupling | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonianOnGraph_commute_fermionTotalNumber` / `hubbardHamiltonianOnGraph_isHermitian` | charge conservation; Hermiticity for real `J` and real `U` | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardChainHamiltonian N J U` | the canonical 1D nearest-neighbour Hubbard chain `−J Σ_{σ,⟨i,j⟩} c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}` (built from `pathGraph (N+1)`) | `Fermion/JordanWigner.lean` |
| `hubbardChainHamiltonian_isHermitian` / `hubbardChainHamiltonian_commute_fermionTotalNumber` | Hermiticity (real `J, U`) and charge conservation | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardHamiltonianOnGraph_mulVec_vacuum` / `hubbardChainHamiltonian_mulVec_vacuum` | both graph-built Hubbard Hamiltonians annihilate the JW vacuum | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardChainGibbsState N β J U` | Gibbs state of the 1D Hubbard chain | `Fermion/JordanWigner.lean` |
| `hubbardChainGibbsState_isHermitian` / `hubbardChainGibbsState_commute_hamiltonian` | Hermiticity (real `J, U`) and commute with the Hamiltonian | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardCycleGibbsState_commute_hamiltonian` | the periodic Hubbard Gibbs state commutes with the periodic Hubbard Hamiltonian (companion of the open-chain version, free corollary of `gibbsState_commute_hamiltonian`) | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardChainGibbsExpectation_zero` / `_im_of_isHermitian` / `_commutator_hamiltonian` / `_hamiltonian_im` / `_hamiltonian_pow_im` / `hubbardChain_partitionFn_im` / `_ofReal_re_eq` / `hubbardChainGibbsState_pow_trace` | open-chain Hubbard expectation companions (β = 0 closed form, Hermitian-observable real, conservation, energy / energy-power expectations real, partition function real, real-cast, Rényi-n trace) | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardCycleGibbsExpectation_zero` / `_im_of_isHermitian` / `_commutator_hamiltonian` / `_hamiltonian_im` / `_hamiltonian_pow_im` / `hubbardCycle_partitionFn_im` / `_ofReal_re_eq` / `hubbardCycleGibbsState_pow_trace` | periodic Hubbard chain expectation companions (same family as the open chain) | `Fermion/JordanWigner/Hubbard/Graph.lean` |

#### Nagaoka's theorem on a magnetization sector (Tasaki §11.2.2, Theorem 11.7 / Lemma 11.9)

| Lean name | Statement | File |
|---|---|---|
| `tasakiEffReMatrixOnSector_ground_finrank_le_one` | **Theorem 11.7 core** (Tasaki, 1st ed. (2020), §11.2.2, Theorem 11.7, p. 385; PR #5149): on a non-empty magnetization sector whose Perron–Frobenius companion `nagaokaPFMatrixOnSector` is irreducible (the per-sector instance of the Definition 11.6 connectivity condition `nagaokaConnectivity`), the sector effective matrix `tasakiEffReMatrixOnSector` has a strictly positive eigenvector at the eigenvalue `−μ` (`μ` = the Perron eigenvalue of the negated matrix) and that eigenspace has `finrank ≤ 1`. Since `−μ = min spec M\|_sector`, this is the non-degeneracy of the sector ground state that Nagaoka's theorem asserts | `Fermion/JordanWigner/Hubbard/NagaokaMagnetizationSector.lean` |
| `reachSwapOff_of_exchangeReachable` | **Lemma 11.9: spin-swap generation along exchange bonds** (Tasaki §11.2.2, proof of Lemma 11.9 and footnote 13, p. 387; PR #5149): if `x ≠ y` are joined in the exchange-bond graph of `nagaokaBondGraph`, then the transposition `{x, y}` is reachable off a finite site set — from every hole position avoiding the support of the connecting exchange-bond walk, `(p, σ)` reaches `(p, swap_{x,y} σ)`. Under `ConnectedByExchangeBonds` the hypothesis holds for every pair, which is exactly the step "we can generate any permutation of spin configurations by successive exchanges on the exchange bonds" that Tasaki's footnote 13 defers to the property (iii) of p. 41 | `Fermion/JordanWigner/Hubbard/NagaokaStateQuiverReach.lean` |

#### General flat-band ground states: the annihilation peel behind eq. (11.3.46) (Tasaki §11.3.4)

| Lean name | Statement | File |
|---|---|---|
| `spinfulAnnihilation_rangeT_mulVec_eq_zero_of_mem_groundSubmodule` | **Range-`T` annihilation of a ground-submodule vector** (Tasaki, 1st ed. (2020), §11.3.4, premise of eq. (11.3.46), p. 412; PR #5149): for PSD hopping `T` and `U > 0`, every `Φ` in `generalFlatBandGroundSubmodule T U` is killed by every smeared annihilator built from the rows of a factorisation `T = Cᴴ · C`, i.e. `Ĉ_σ(∑_k a_k C_k) Φ = 0` for all coefficient vectors `a`. This is the ground-submodule packaging of the `Ĥ_hop Φ_GS = 0` step from which Tasaki concludes that a ground state is written only in terms of the `â†` operators | `Fermion/JordanWigner/Hubbard/GeneralFlatBandGroundAnnihilation.lean` |
| `site_annihilation_mulVec_generalFlatBandSlaterState` | **Site annihilator kills a Slater state vanishing at that site** (Tasaki §11.3.4, peel step toward eq. (11.3.46), p. 412; PR #5149): if `μ_q(z) = 0` for every mode `q` in the list, then `ĉ_{z,σ}` anticommutes through every `â†` factor of `generalFlatBandSlaterState μ qs` (site-dual CAR with vanishing pairing) and annihilates the vacuum. On the index set `I` this is the biorthogonality statement for `z ∈ I` not among the listed modes | `Fermion/JordanWigner/Hubbard/GeneralFlatBandOperators.lean` |

<!-- legacy-source:end:2605:2731 -->

---

[← Multi-mode fermion via Jordan–Wigner (P2 backbone)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/) · [Catalogue](/lattice-system/formalization/legacy/) · End →
