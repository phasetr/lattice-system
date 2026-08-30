---
layout: page
title: "Legacy catalogue: Multi-mode fermion via Jordan–Wigner (P2 backbone) (part 1 of 9)"
permalink: /formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-01/
---

<a id="legacy-catalogue-multi-mode-fermion-via-jordanwigner-p2-backbone-part-1-of-4"></a>
# Legacy catalogue: Multi-mode fermion via Jordan–Wigner (P2 backbone) (part 1 of 9)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Fermions and Hubbard models](/lattice-system/formalization/legacy/#group-fermions-hubbard)

<!-- legacy-source:start:2246:2345 -->
### Multi-mode fermion via Jordan–Wigner (P2 backbone)

| Lean name | Statement | File |
|---|---|---|
| `jwString N i` | `∏_{j.val < i.val} σ^z_j` (noncomm-product, pairwise commutativity from `onSite_mul_onSite_of_ne`) | `Fermion/JordanWigner.lean` |
| `jwString_zero` | `jwString N 0 = 1` (empty product) | `Fermion/JordanWigner/String.lean` |
| `fermionMultiAnnihilation N i` | `c_i = jwString_i · σ^+_i` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation N i` | `c_i† = jwString_i · σ^-_i` | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_zero` | `c_0 = σ^+_0` (no JW string at the leftmost site) | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiCreation_zero` | `c_0† = σ^-_0` | `Fermion/JordanWigner/Operators.lean` |
| `jwString_commute_onSite` | `Commute (jwString N i) (onSite i A)` (string commutes past same-site operators) | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiAnnihilation_sq` | `c_i² = 0` (Pauli exclusion) | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiCreation_sq` | `(c_i†)² = 0` | `Fermion/JordanWigner/Operators.lean` |
| `jwString_isHermitian` | `(jwString N i)ᴴ = jwString N i` (product of pairwise-commuting Hermitian σ^z is Hermitian) | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiAnnihilation_conjTranspose` | `(c_i)ᴴ = c_i†` | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiCreation_conjTranspose` | `(c_i†)ᴴ = c_i` | `Fermion/JordanWigner/Operators.lean` |
| `jwString_sq` | `(jwString N i)² = 1` | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiNumber N i` | `n_i := c_i† · c_i` (site-occupation number operator) | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_eq_onSite` | `n_i = onSite i (σ^- · σ^+)` (JW strings cancel via `J² = 1`) | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiNumber_isHermitian` | `n_i` is Hermitian | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiNumber_sq` | `n_i² = n_i` (idempotent, eigenvalues 0, 1) | `Fermion/JordanWigner/Operators.lean` |
| `fermionMultiAnticomm_self` | `c_i · c_i† + c_i† · c_i = 1` (same-site CAR) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiNumber_commute` | `Commute (n_i) (n_j)` for any sites (simultaneously diagonal) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionTotalNumber N` | `N̂ := Σ_i n_i` (total particle-number operator) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_isHermitian` | `N̂` is Hermitian | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiAnnihilation_anticomm_two_site_cross` | simplest nontrivial cross-site CAR on `Fin 2`: `c_0 · c_1 + c_1 · c_0 = 0` (JW string at site 1 is `σ^z_0`, combined with `σ^+ σ^z = -σ^+` and `σ^z σ^+ = σ^+`) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiCreation_anticomm_two_site_cross` | adjoint form: `c_0† · c_1† + c_1† · c_0† = 0` on `Fin 2`, obtained by taking `conjTranspose` of the annihilation version | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiAnnihilation_creation_anticomm_two_site_cross` | mixed cross-site: `c_0 · c_1† + c_1† · c_0 = 0` on `Fin 2` (same proof template as the annihilation-only version with `σ^+_1` replaced by `σ^-_1` at site 1) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiCreation_annihilation_anticomm_two_site_cross` | fourth off-diagonal CAR: `c_0† · c_1 + c_1 · c_0† = 0` on `Fin 2` (adjoint of the previous; completes the 2-site off-diagonal CAR relations) | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiAnnihilation_anticomm_zero_one` | generalisation to any chain length: `c_0 · c_1 + c_1 · c_0 = 0` on `Fin (N+1)` for any `N ≥ 1` (the JW string at site 1 is uniformly `σ^z_0` independent of `N`) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiCreation_anticomm_zero_one` | dual: `c_0† · c_1† + c_1† · c_0† = 0` on `Fin (N+1)`, `N ≥ 1` (adjoint of the above) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_one` | mixed: `c_0 · c_1† + c_1† · c_0 = 0` on `Fin (N+1)`, `N ≥ 1` | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_one` | mixed dual: `c_0† · c_1 + c_1 · c_0† = 0` on `Fin (N+1)`, `N ≥ 1` | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `jwString_succ_eq` | recursive factorisation of the JW string: `jwString N ⟨i+1, _⟩ = jwString N i * onSite i pauliZ` (key general lemma for proving jwString at any specific site without raw `Finset.noncommProd` manipulation) | `Fermion/JordanWigner/String.lean` |
| `fermionMultiAnnihilation_anticomm_zero_two_fin_three` | first 3-site cross-site CAR: `c_0 · c_2 + c_2 · c_0 = 0` on `Fin 3` (using `jwString_succ_eq` to factor `jwString 2 2 = σ^z_0 · σ^z_1`) | `Fermion/JordanWigner/CAR/SameSiteCore.lean` |
| `fermionMultiCreation_anticomm_zero_two_fin_three` | dual: `c_0† · c_2† + c_2† · c_0† = 0` on `Fin 3` (adjoint of the previous) | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_two_fin_three` | mixed: `c_0 · c_2† + c_2† · c_0 = 0` on `Fin 3` | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_two_fin_three` | mixed dual: `c_0† · c_2 + c_2 · c_0† = 0` on `Fin 3` (adjoint of the previous) | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiAnnihilation_anticomm_zero_two_general` | generalised to any N ≥ 2: `c_0 · c_2 + c_2 · c_0 = 0` on `Fin (N+1)` | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiCreation_anticomm_zero_two_general` | dual: `c_0† · c_2† + c_2† · c_0† = 0` for any N ≥ 2 (adjoint) | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_two_general` | mixed: `c_0 · c_2† + c_2† · c_0 = 0` for any N ≥ 2 | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_two_general` | mixed dual: `c_0† · c_2 + c_2 · c_0† = 0` for any N ≥ 2 (adjoint) | `Fermion/JordanWigner/CAR/SameSite.lean` |
| `fermionMultiAnnihilation_anticomm_zero_pos` | **general cross-site CAR `{c_0, c_k} = 0`** for every `k : Fin (N+1)` with `0 < k.val` — generalises the `_zero_one` / `_zero_two_general` specialisations. Proof: reduce to the anticommutator `{σ^+_0, jwString N k}`, which vanishes by induction on the string length (base: `{σ^+, σ^z} = 0` at site 0; step: `σ^z_{k-1}` at site `k-1 ≠ 0` commutes past `σ^+_0`). | `Fermion/JordanWigner/CAR/StringFactorization.lean` |
| `fermionMultiCreation_anticomm_zero_pos` | dual `{c_0†, c_k†} = 0` for every `k : Fin (N+1)` with `0 < k.val` (adjoint of the above) | `Fermion/JordanWigner/CAR/StringFactorization.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_pos` | mixed `{c_0, c_k†} = 0` for every `k : Fin (N+1)` with `0 < k.val` — same inductive argument on the JW string anticommutator (the site-`k` factor is `σ^-_k` instead of `σ^+_k`; JW-string part is unchanged) | `Fermion/JordanWigner/CAR/StringFactorization.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_pos` | mixed dual `{c_0†, c_k} = 0` for every `k : Fin (N+1)` with `0 < k.val` (adjoint of the above) | `Fermion/JordanWigner/CAR/StringFactorization.lean` |
| `jwStringExceptAt` / `jwString_eq_onSite_mul_jwStringExceptAt` / `jwStringExceptAt_commute_onSite` | private factorisation helpers for the Jordan-Wigner string at an interior site (#210): for `i.val < j.val`, `jwString N j = onSite i pauliZ * jwStringExceptAt N j i`, and `jwStringExceptAt N j i` commutes with every single-site operator at site `i` | `Fermion/JordanWigner/CAR/StringFactorizationCore.lean` |
| `jwString_anticomm_onSite_pos_spinHalfOpPlus` | operator-level anticommutator `{σ^+_i, jwString N j} = 0` for every `i j : Fin (N+1)` with `i.val < j.val` — generalises `jwString_anticomm_onSite_zero_spinHalfOpPlus` (i = 0 case) to arbitrary interior `i`; building block for the fully general cross-site CAR `{c_i, c_j} = 0` (#210) | `Fermion/JordanWigner/CAR/StringFactorizationCore.lean` |
| `jwString_anticomm_onSite_pos_spinHalfOpMinus` | companion `{σ^-_i, jwString N j} = 0` for every `i < j` (via `conjTranspose` of the `σ^+` version) | `Fermion/JordanWigner/CAR/StringFactorizationCore.lean` |
| `jwString_commute_jwString` | any two Jordan-Wigner strings `jwString N i` and `jwString N j` commute (both are noncommutative products of `σ^z` over distinct sites) | `Fermion/JordanWigner/CAR/StringFactorizationCore.lean` |
| `fermionMultiAnnihilation_anticomm_lt` | **fully general cross-site CAR `{c_i, c_j} = 0` for `i < j`** (#210) on `Fin (N + 1)`. Proof: reduce via `jwString_anticomm_onSite_pos_spinHalfOpPlus` to an identity involving `JW_i · JW_j = JW_j · JW_i` (via `jwString_commute_jwString`), which makes the sum collapse | `Fermion/JordanWigner/CAR/CrossSite.lean` |
| `fermionMultiCreation_anticomm_lt` | dual `{c_i†, c_j†} = 0` for `i < j` (adjoint of the above) | `Fermion/JordanWigner/CAR/CrossSite.lean` |
| `fermionMultiAnnihilation_creation_anticomm_lt` | mixed `{c_i, c_j†} = 0` for `i < j` — same structure as `_anticomm_lt` but with `σ^-_j` at site `j` | `Fermion/JordanWigner/CAR/CrossSite.lean` |
| `fermionMultiCreation_annihilation_anticomm_lt` | mixed dual `{c_i†, c_j} = 0` for `i < j` (adjoint of the above) | `Fermion/JordanWigner/CAR/CrossSite.lean` |
| `spinHalfOpPlus_mul_self` / `spinHalfOpPlus_mul_spinHalfOpMinus_mul_spinHalfOpPlus` | Pauli helper identities `σ^+ σ^+ = 0` and `σ^+ σ^- σ^+ = σ^+` | `Quantum/SpinHalfBasis.lean` |
| `fermionMultiNumber_commutator_fermionMultiAnnihilation_self` | `[n_i, c_i] = -c_i` (number / annihilation commutator) | `Fermion/JordanWigner/Number.lean` |
| `fermionMultiNumber_commutator_fermionMultiCreation_self` | `[n_i, c_i†] = c_i†` (number / creation commutator, dual via adjoint) | `Fermion/JordanWigner/Number.lean` |
| `spinHalfOpMinus_mul_spinHalfOpPlus_commute_pauliZ` | matrix identity: `Commute (σ^- σ^+) σ^z` (both diagonal in the computational basis) | `Quantum/SpinHalfBasis.lean` |
| `fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne` | `Commute (n_i) (c_j)` for `i ≠ j` — the number operator at site `i` commutes with any annihilation at a different site, via the `n σ^z = σ^z n` matrix commutativity absorbing the JW-string `σ^z_i` factor | `Fermion/JordanWigner/Number.lean` |
| `fermionMultiNumber_commute_fermionMultiCreation_of_ne` | dual: `Commute (n_i) (c_j†)` for `i ≠ j` via adjoint | `Fermion/JordanWigner/Number.lean` |
| `fermionTotalNumber_commutator_fermionMultiAnnihilation` | `[N̂, c_j] = -c_j` — the total particle-number operator shifts annihilation down by one (sum of diagonal `[n_j, c_j] = -c_j` with vanishing off-diagonal terms) | `Fermion/JordanWigner/Number.lean` |
| `fermionTotalNumber_commutator_fermionMultiCreation` | dual: `[N̂, c_j†] = c_j†` (via adjoint) | `Fermion/JordanWigner/Number.lean` |
| `fermionTotalNumber_commute_hopping` | `Commute N̂ (c_i† · c_j)` — the hopping operator preserves total particle number (shifts cancel: `[N̂, c_i†] = c_i†` and `[N̂, c_j] = -c_j`) | `Fermion/JordanWigner/Number.lean` |
| `fermionMultiNumber_commute_fermionTotalNumber` | `Commute (n_i) (N̂)` — site occupation commutes with the total particle number (sum of pairwise commuting `[n_i, n_j] = 0`) | `Fermion/JordanWigner/Number.lean` |
| `fermionDensityDensity_commute_fermionTotalNumber` | `Commute (n_i · n_j) (N̂)` — the density-density operator preserves total particle number, foundational for Hubbard-style on-site interactions | `Fermion/JordanWigner/Number.lean` |
| `fermionHopping`, `fermionHopping_commute_fermionTotalNumber` | the general single-particle hopping `H_hop = Σ_{i,j} t_{i,j} c_i† c_j` and the proof that it commutes with `N̂` (charge conservation of the kinetic Hamiltonian) | `Fermion/JordanWigner/Number.lean` |
| `fermionDensityInteraction`, `fermionDensityInteraction_commute_fermionTotalNumber` | the general density–density interaction `V_int = Σ_{i,j} V_{i,j} n_i n_j` and the proof that it commutes with `N̂` (paired with `H_hop` this gives charge conservation for any Hubbard-type Hamiltonian) | `Fermion/JordanWigner/Number.lean` |
| `fermionGenericHamiltonian`, `fermionGenericHamiltonian_commute_fermionTotalNumber` | the canonical charge-conserving fermion Hamiltonian `H = H_hop + V_int` and the proof that `[H, N̂] = 0`, the unified statement of charge conservation for single-species Hubbard / extended Hubbard models | `Fermion/JordanWigner/Number.lean` |
| `fermionMultiNumber_mul_isHermitian` | `(n_i · n_j)` is Hermitian for any sites (commuting Hermitian factors) | `Fermion/JordanWigner/Number.lean` |
| `fermionDensityInteraction_isHermitian` | `V_int = Σ V_{ij} n_i n_j` is Hermitian when every coupling entry is real (`star V_{ij} = V_{ij}`) | `Fermion/JordanWigner/Number.lean` |
| `fermionHoppingTerm_conjTranspose` | `(c_i† · c_j)ᴴ = c_j† · c_i` (single hopping term) | `Fermion/JordanWigner/Number.lean` |
| `fermionHopping_isHermitian` | `H_hop = Σ t_{ij} c_i† c_j` is Hermitian when `t` is Hermitian (`star (t i j) = t j i`); proved via term-wise conjTranspose + `Finset.sum_comm` for the index swap | `Fermion/JordanWigner/Number.lean` |
| `fermionGenericHamiltonian_isHermitian` | `H = H_hop + V_int` is Hermitian when `t` is Hermitian and `V` is entry-wise real; one-line corollary of the two summand Hermiticities via `Matrix.IsHermitian.add` | `Fermion/JordanWigner/Number.lean` |
| `fermionGenericGibbsState N β t V` | Gibbs state `gibbsState β (H_hop + V_int)` for the Hubbard-skeleton Hamiltonian | `Fermion/JordanWigner.lean` |
| `fermionGenericGibbsState_isHermitian` | Hermiticity (when `t` is Hermitian and `V` is real) | `Fermion/JordanWigner/Number.lean` |
| `fermionGenericGibbsState_commute_hamiltonian` | `Commute ρ_β H` (always true for the Gibbs state of any operator with itself) | `Fermion/JordanWigner/Number.lean` |
| `fermionMultiVacuum N` | the JW vacuum on `Fin (N+1)` modes — the all-up many-body basis vector `|↑↑…↑⟩` | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_mulVec_vacuum` | every annihilation operator kills the vacuum: `(c_i).mulVec (fermionMultiVacuum N) = 0` | `Fermion/JordanWigner/Number.lean` |
| `fermionMultiNumber_mulVec_vacuum` | each `n_i · |vac⟩ = 0` (since `n_i = c_i† c_i` and `c_i |vac⟩ = 0`) | `Fermion/JordanWigner/Number.lean` |
| `fermionTotalNumber_mulVec_vacuum` | the vacuum is an `N̂`-eigenstate of eigenvalue 0 | `Fermion/JordanWigner/Number.lean` |
| `fermionHopping_mulVec_vacuum` | `H_hop · |vac⟩ = 0` (each `c_i† c_j |vac⟩ = c_i† 0 = 0`) | `Fermion/JordanWigner/Number.lean` |
| `fermionDensityInteraction_mulVec_vacuum` | `V_int · |vac⟩ = 0` (each `n_i n_j |vac⟩ = n_i 0 = 0`) | `Fermion/JordanWigner/Number.lean` |
| `fermionGenericHamiltonian_mulVec_vacuum` | `H · |vac⟩ = 0` for the full Hubbard skeleton (linearity) | `Fermion/JordanWigner/Number.lean` |
| `fermionTotalNumber_mulVec_singleParticle` | `c_i† |vac⟩` is an `N̂`-eigenstate of eigenvalue 1 (uses `[N̂, c_i†] = c_i†` and `N̂ |vac⟩ = 0`) | `Fermion/JordanWigner/Number.lean` |
| `fermionTotalNumber_mulVec_twoParticle` | `c_i† c_j† |vac⟩` is an `N̂`-eigenstate of eigenvalue 2 (Leibniz on the commutator gives `[N̂, c_i† c_j†] = 2 c_i† c_j†`) | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `fermionTotalNumber_mulVec_eigenstate_of_commute` | generic charge-eigenstate helper: if `[N̂, X] = α X` and `N̂ v = 0` then `N̂ (X v) = α (X v)`; abstracts the single- and two-particle constructions | `Fermion/JordanWigner/Number.lean` |
| `spinfulIndex N i σ` | bijection `(i, σ : Fin 2) ↦ 2 * i + σ ∈ Fin (2*N+2)`, embedding two-species data into a single-species JW chain | `Fermion/JordanWigner.lean` |
| `spinfulIndex_eq_iff`, `exists_spinfulIndex` | shared injectivity (`spinfulIndex N a r = spinfulIndex N b s ↔ a = b ∧ r = s`) and decomposition (`∃ a r, k = spinfulIndex N a r`) of the spinful index | `Fermion/JordanWigner/Hubbard.lean` |
| `fermionUpAnnihilation`, `fermionDownAnnihilation`, `fermionUpCreation`, `fermionDownCreation` | spinful annihilation / creation operators as wrappers around the underlying single-species operators at `2i` (up) and `2i+1` (down) | `Fermion/JordanWigner/Hubbard.lean` |
| `fermionUpNumber`, `fermionDownNumber` | spinful site-occupation numbers `n_{i,↑}`, `n_{i,↓}` | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardOnSiteInteraction N U` | the on-site Hubbard interaction `H_int = U Σ_i n_{i,↑} · n_{i,↓}` | `Fermion/JordanWigner.lean` |
| `hubbardOnSiteInteraction_commute_fermionTotalNumber` | `[H_int, N̂] = 0` (charge conservation) | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardOnSiteInteraction_isHermitian` | `H_int` is Hermitian when `U` is real (`star U = U`) | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardKinetic N t` | the spinful tight-binding kinetic operator `T = Σ_{σ} Σ_{i,j} t_{i,j} c_{i,σ}† c_{j,σ}` | `Fermion/JordanWigner.lean` |
| `hubbardKinetic_commute_fermionTotalNumber` | `[T, N̂] = 0` (charge conservation of the kinetic operator) | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardKinetic_isHermitian` | `T` is Hermitian when `t` is a Hermitian matrix (`star (t i j) = t j i`) | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardHamiltonian N t U` | the canonical (single-band) Hubbard Hamiltonian `H = T + U Σ n_{i↑} n_{i↓}` on `Fin (2N+2)` | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonian_commute_fermionTotalNumber` | `[H, N̂] = 0` (charge conservation) | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardHamiltonian_isHermitian` | `H` is Hermitian when `t` is Hermitian and `U` is real | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardGibbsState N β t U` | the Hubbard Gibbs state `gibbsState β H_Hubbard` | `Fermion/JordanWigner.lean` |
<!-- legacy-source:end:2246:2345 -->

---

[← Single-mode fermion (P2 skeleton)](/lattice-system/formalization/legacy/29-single-mode-fermion-p2-skeleton/) · [Catalogue](/lattice-system/formalization/legacy/) · [Multi-mode fermion via Jordan–Wigner (P2 backbone) →](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)
