---
layout: page
title: "Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 2"
permalink: /formalization/legacy/details/group-spin-models-part-02/
---

# Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 2

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-621"></a>
## Record from former line 621

**Lean name:** <!-- legacy-detail-lean:start:621 -->`ringBondSquareConst_reindexCyclic` / `ringBondSquareLinField_reindexCyclic` / `ringBondSquareFieldPartitionRe_pos` / `ringBondSquareFieldPartitionRe_reindexCyclic` / `ringBondSquareFieldPartition_gaussianDomination`<!-- legacy-detail-lean:end:621 -->

**File:** <!-- legacy-detail-file:start:621 -->`Quantum/SpinS/RingReflectionBondSquareGaussianDomination.lean`<!-- legacy-detail-file:end:621 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:621 -->
**Bond-square chessboard Gaussian-domination capstone**
(`RingReflectionBondSquareGaussianDomination.lean`, Tasaki §4.1 Lemma 4.5 + Theorem 4.2
(4.1.55)–(4.1.57) + (4.1.51), book pp. 87–90, bond-square chessboard Gaussian-domination / PR
#4998): the **finite-β chessboard Gaussian-domination bound** `Z^{BS}_β(h)^{2n} ≤ ∏_j Z^{BS}_β(fun _
=> h j)` (Tasaki §4.1 Theorem 4.2, pp. 85–90;

chessboard estimate Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88), obtained by applying the **classical
cyclic averaging inequality** (`reflectionPositivity_averaging`, Tasaki Lemma 4.5,
(4.1.55)–(4.1.57), pp. 87–88) **directly** to the plain functional `F g = −log Z^{BS}_β(g)` — no
staggered-relabel bridge needed, since PR-BS8b already delivers the reflection step on the sign-free
classical mirrors. **Cyclicity hypothesis (★★ hcyc) (4.1.55)**
`ringBondSquareFieldPartitionRe_reindexCyclic` (PR-BS9,
`RingReflectionBondSquareFieldPartition.lean`): `Z^{BS}_β(reindexCyclic n g) = Z^{BS}_β(g)`, proved
from the **scalar-shift reduction `(★★)` (`ringBondSquareFieldPartitionRe_eq_scaled`)**. The scalar
constant `C(h)` is translation-invariant **(A)** `ringBondSquareConst_reindexCyclic` (PR-BS9,
`RingReflectionBondSquareField.lean`);

the linear field covariance `kOf(reindexCyclic h) = −kOf(h)` **(B)**
`ringBondSquareLinField_reindexCyclic` (PR-BS9, `RingReflectionBondSquareField.lean`), a sign flip
absorbed by spin-flip invariance `ringFieldPartitionRe_neg` and translation symmetry
`ringFieldPartitionRe_translate` of the linear-core partition. **Positivity domain (4.1.56)**
`ringBondSquareFieldPartitionRe_pos` (PR-BS9, `RingReflectionBondSquareFieldPartition.lean`, strict
positivity `0 < Z^{BS}_β(h)`) is required for the `−log` functional;

follows from the scalar-shift reduction and positivity of both factors. **Reflection bound
(4.1.56)**: the one reflection step (PR-BS8b) `Z^{BS}_β(g)² ≤ Z^{BS}_β(reflectLeft n
g)·Z^{BS}_β(reflectRight n g)` on classical mirrors, combined with positivity. **Averaging
computation**: applying `reflectionPositivity_averaging` yields `(1/2n) Σ_j (−log Z^{BS}_β(fun _ =>
h j)) ≤ −log Z^{BS}_β(h)`. Exponentiating and rearranging gives the product bound. **Forward to
PR-BS10**: PR-BS10 collapses each constant-field factor to `Z^{BS}_β(0)`, yielding the uniform-field
bound `Z^{BS}_β(h) ≤ Z^{BS}_β(0)` (Tasaki (4.1.49)/(4.1.52), pp. 85–86). This is PR-BS9 of the
bond-square route toward the reflection-positivity infrastructure for Theorem 4.2.
<!-- legacy-detail:end:621 -->

<a id="record-653"></a>
## Record from former line 653

**Lean name:** <!-- legacy-detail-lean:start:653 -->`staggeredCasimirOpS` / `shenQiuTian_ferrimagnetic_lro`<!-- legacy-detail-lean:end:653 -->

**File:** <!-- legacy-detail-file:start:653 -->`Quantum/SpinS/FerrimagneticLROUniversalFinal.lean` + `…UniversalFinalCore.lean` + `FerrimagneticLRO.lean` + `…ComponentAlgebra.lean` + `…CrossTerm.lean` + `…TotalSpin.lean` + `…TotalSpinCore.lean` + `…Capstone.lean` + `…Universal.lean`<!-- legacy-detail-file:end:653 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:653 -->
**Theorem 4.4** (§4.1, Shen–Qiu–Tian, PROVED axiom-free;

eqs. (4.1.12)–(4.1.13)): ferrimagnetic LRO on an asymmetric bipartite lattice. The SU(2)-invariant
squared staggered operator `(Ô_Λ)² = Σ_{x,y} ε_x ε_y Ŝ_x·Ŝ_y`, and the bound `S²(\|A\|−\|B\|)² ≤
⟨Φ_GS\|(Ô_Λ)²\|Φ_GS⟩` for any normalized ground state of the connected bipartite AFM model (same
hypotheses as Thm 2.3). **PROVED axiom-free** (Issues #4604/#4617 CLOSED;

book proof = chain (4.1.16): (4.1.15) cross-term + Lieb–Mattis Thm 2.3 total spin + Casimir). PR1
(#4605) formalizes the **operator-algebra core** in
`Quantum/SpinS/FerrimagneticLROComponentAlgebra.lean`: `staggeredTransverseCasimirOpS` (transverse
part of `(Ô_Λ)²`), `(Ô_Λ)² = transverse + (Ô_Λ^(3))²`, the PSD drop `⟨transverse⟩ ≤ ⟨(Ô_Λ)²⟩`,
`(Ŝ_tot^(α))² = Σ_{x,y} Ŝ_x^(α)Ŝ_y^(α)`, the Casimir identity
`Σ_{x,y}(Ŝ_x^(1)Ŝ_y^(1)+Ŝ_x^(2)Ŝ_y^(2)) = (Ŝ_tot)² − (Ŝ_tot^(3))²`, and the M=0 reduction
`⟨(Ŝ_tot)²⟩ = ⟨transverse⟩`. PR2 (#4606) adds the **cross-term inequality (4.1.15)** in
`Quantum/SpinS/FerrimagneticLROCrossTermCore.lean` (transverse correlation + ladder positivity +
per-pair sign) + `Quantum/SpinS/FerrimagneticLROCrossTerm.lean` (the summed cross-term inequality,
split for build speed): the transverse correlation `⟨Φ,T_xy Φ⟩` (`T_xy = ½(Ŝ_x^+Ŝ_y^- +
Ŝ_x^-Ŝ_y^+)`), its non-positivity for cross-sublattice pairs on a Marshall-positive sector ground
state (`marshallSignS·c`, `c>0`), and the summed dominance `⟨Φ,(Σ_{x,y}T_xy)Φ⟩.re ≤
⟨Φ,staggeredTransverseCasimirOpS Φ⟩.re`. PR3 (#4607) adds the **total-spin value** in
`Quantum/SpinS/FerrimagneticLROTotalSpin.lean` (coupling-agnostic via a `tasaki_2_5_theorem_2_3`
hypothesis): `exists_centered_groundState_predictedCasimir_of_tasaki23` produces a centered (`Ŝ³_tot
Φ⁰=0`) Marshall ground state with `(Ŝ_tot)² Φ⁰ = S_tot(S_tot+1)·Φ⁰` (`S_tot=(\|A\|−\|B\|)N/2`),
reusing `tasaki23_pf_groundState_casimir_eq_predicted_sector` + the extremal-Casimir machinery. PR4
(#4608) proves the **capstone** `ferrimagnetic_lro_completeBipartite_centered` in
`Quantum/SpinS/FerrimagneticLROCapstone.lean`: assembling chain (4.1.16) on the centered ground
state, `(N/2)²(\|A\|−\|B\|)²·⟨Φ⁰,Φ⁰⟩.re ≤ ⟨Φ⁰,(Ô_Λ)²Φ⁰⟩.re` (existence form, coupling-agnostic via
`tasaki_2_5_theorem_2_3`;

sorry-free, axiom-clean, independent of the `shenQiuTian_ferrimagnetic_lro` axiom;

that axiom is now itself proved in UniversalFinal). For build speed the proof's private
Rayleigh-ratio helpers and the per-sector oriented bound
`staggeredCasimir_weightComponent_bound_oriented` (now module-public: `S_tot²·‖Φ_M‖² ≤
⟨Φ_M,(Ô_Λ)²Φ_M⟩.re` for each magnetization weight component `Φ_M` of a ground state) live in the
companion `…UniversalFinalCore.lean`, with the sum assembly + the public
`shenQiuTian_ferrimagnetic_lro` kept in `…UniversalFinal.lean`.
<!-- legacy-detail:end:653 -->

<a id="record-654"></a>
## Record from former line 654

**Lean name:** <!-- legacy-detail-lean:start:654 -->`raiseLowerReachableS_of_connected`<!-- legacy-detail-lean:end:654 -->

**File:** <!-- legacy-detail-file:start:654 -->`Quantum/SpinS/ConnectedRaiseLower.lean` + `…ConnectedDressedPF.lean` + `…ConnectedSectorIrreducible.lean` + `…ConnectedTheorem23Core.lean` + `…ConnectedTheorem23.lean` + `…ConnectedFerrimagneticLRO.lean` + `…StaggeredCasimirSU2Invariance.lean` + `…SU2ExpectationLadderInvariant.lean` + `…SU2ExpectationLadderIterated.lean` + `…ConnectedSectorFinrankLeOne.lean` + `…WeightPreservingExpectationSum.lean` + `…StrictHOutsideFerrimagnetic.lean` + `…StrictHOutsideFerrimagneticCore.lean` + `…FerrimagneticLROUniversal.lean`<!-- legacy-detail-file:end:654 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:654 -->
**Connected-graph spin-config reachability** (§2.5, PROVED; Issue #4609, prereq for the connected
Marshall–Lieb–Mattis extension / Thm 4.4 axiom): on a connected graph `G`, any two
equal-magnetization configs are raise/lower reachable — `G.Connected → magSumS σ = magSumS σ' →
RaiseLowerReachableS G σ σ'`. Discharged axiom-free by strong induction on the `configDistS`
mismatch (surplus/deficit sites + connected-graph walk) with overflow-safe single-quantum path
transport (`transportOne`; at each edge push the quantum forward when the next vertex has room, else
recurse first to make room). Generalizes the complete-bipartite
`raiseLowerReachableS_bipartiteCompleteGraph` to arbitrary connected graphs — the combinatorial core
of extending Theorem 2.3 to connected couplings (PR #4610). **PR2 (#4611)** lifts this to the
dressed-matrix per-sector Perron–Frobenius positivity for a general connected bipartite `G` in
`Quantum/SpinS/ConnectedDressedPF.lean`: `exists_matrixPow_pos_of_magConfigS_connected` (`∃ k, 0 <
(shiftedDressedSReMatrixOnMagSector A J N c M)^k σ' σ`) from `G.Connected` + `hGbip` +
edge-positivity `hJ_pos_G : G.Adj x y → 0 < (J x y).re` (not complete-bipartite positivity), via the
graph-agnostic edge-local witness
`neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_witness` + the connected reachability —
generalizing `exists_matrixPow_pos_of_magConfigS_bipartite`. **PR3 (#4612)** assembles **Theorem 2.3
itself for connected couplings**: `isIrreducible_shiftedDressedSReMatrixOnMagSector_connected`
(ConnectedSectorIrreducible.lean) + 20 `_of_irreducible` chain variants parameterizing the
PF-consuming Marshall–Lieb–Mattis chain by the irreducibility result (graph-agnostic) + the capstone
`tasaki_2_5_theorem_2_3_data_of_connected` (ConnectedTheorem23Core.lean, ConnectedTheorem23.lean):
the per-magnetization-sector Marshall-positive ground states + global minimality of Theorem 2.3 hold
for ANY connected bipartite `J` (`G.Connected` + `hGbip` + edge-positivity `hJ_pos_G`), not just
complete-bipartite — the `hOutside`/lower-bound side reuses
`tasaki23_general_hOutside`/`tasaki23_eigenvalue_ge_common` (which need only `hJ_nn`). This is the
connected-coupling extension of Marshall–Lieb–Mattis (Lieb–Mattis 1962). **PR4 (#4613)** assembles
the **connected-coupling ferrimagnetic LRO bound (existence form)**
`ferrimagnetic_lro_connected_centered` (ConnectedFerrimagneticLRO.lean): for any connected bipartite
AFM coupling (`G.Connected` + `hGbip` + `hJ_pos_G`), there is a centered ground state `Φ⁰` with
`(N/2)²(\|A\|−\|B\|)²·⟨Φ⁰,Φ⁰⟩.re ≤ ⟨Φ⁰,(Ô_Λ)²Φ⁰⟩.re` — Tasaki's chain (4.1.16) for the genuine
connected (non-complete) coupling, built from the connected Theorem 2.3 data + connected
irreducibility Casimir value + the PR1/PR2 operator-algebra (all graph-agnostic). **PR5 (#4614)**
proves the **`SU(2)` invariance of `(Ô_Λ)²`** in `Quantum/SpinS/StaggeredCasimirSU2Invariance.lean`:
`staggeredCasimirOpS_commute_totalSpinSOp{1,2,3}` + `…OpPlus`/`…OpMinus` (the squared staggered
order operator commutes with every total-spin operator), immediate from the per-pair
`spinSDot_commutator_totalSpinSOp*` vanishing — ingredient (a) of the universal-form transfer. **PR6
(#4615)** proves the **core of ingredient (b)** in
`Quantum/SpinS/SU2ExpectationLadderInvariant.lean`: `su2_expectationRatioRe_ladder_invariant` — for
an SU(2)-invariant operator `O` (commuting with `Ŝ^±_tot`) and a joint `Ŝ³_tot`/Casimir eigenvector
`v`, the real expectation ratio `⟨w,Ow⟩.re/⟨w,w⟩.re` is unchanged under lowering `w ↦ Ŝ⁻_tot v`
(both numerator and denominator scale by the same `Ŝ⁺Ŝ⁻ = Casimir − (Ŝ³)² + Ŝ³` eigenvalue). This is
the ladder step that makes `(Ô_Λ)²`'s expectation constant across the spin-`S_tot` multiplet;

**PR7 (#4616)** iterates it to `(Ŝ⁻_tot)^k` (`su2_expectationRatioRe_ladder_iterate_invariant`,
`Quantum/SpinS/SU2ExpectationLadderIterated.lean`), so every member of the lowering tower shares the
centered ratio. The **stated** `shenQiuTian_ferrimagnetic_lro` axiom (universal over *all* ground
states) now remains pending only the final assembly of ingredient (b): the ground-state weight
decomposition + the **ground-eigenspace classification** (any global-min eigenvector's nonzero
`Ŝ³`-weight components lie in the admissible sectors — needs strict energy separation, the hard
remaining gate) (#4604). **PR8 (#4618)** adds step 1 of that dimension bound:
`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected`
(`Quantum/SpinS/ConnectedSectorFinrankLeOne.lean`) — connected-coupling per-sector ground-state
uniqueness (`finrank ≤ 1`), the connected-irreducibility mirror of the complete-graph lemma (Issue
#4617). **PR9 (#4619)** adds step 3: `weightPreserving_expectation_eq_sum_sector`
(`Quantum/SpinS/WeightPreservingExpectationSum.lean`) — for any operator commuting with `Ŝ³_tot`,
`⟨Φ,OΦ⟩ = Σ_M ⟨Φ_M,OΦ_M⟩` over the `Ŝ³`-weight sector components (cross terms vanish by
`Ŝ³_tot`-eigenvalue orthogonality; no Hermiticity of `O` needed), the block-diagonal decomposition
for `(Ô_Λ)²`'s expectation. **PR10 (#4620)** clears the hard gate (step 2):
`tasaki23_strict_hOutside_of_connected` (`Quantum/SpinS/StrictHOutsideFerrimagnetic.lean`; for build
speed the per-sector ferrimagnetic foundation `tasaki23_strict_hOutside_ferrimagnetic` and its
Casimir-obstruction helpers live in the companion `…StrictHOutsideFerrimagneticCore.lean`) —
**strict** energy separation, `μ < μM` for any non-admissible sector `M ∉ [min·N, max·N]` (the
connected ferrimagnetic generalization of the balanced
`tasaki23_strict_hOutside_of_card_eq_zero_casimir_ladder_obstruction`, via the Casimir
equality-obstruction: ladder a hypothetical non-admissible μ-eigenvector to the admissible band
edge, pull back the predicted Casimir `S_tot(S_tot+1)` through the ladder, contradict the abs
Casimir lower bound `|center−M|(|center−M|+1) > S_tot(S_tot+1)`). This is the strict Lieb–Mattis
level ordering for the connected AFM Heisenberg — the last gate; only the final weight-decomposition
assembly remains to discharge `shenQiuTian_ferrimagnetic_lro` (#4617). **PR11 (#4621)** adds the
universal-form assembly infra in `Quantum/SpinS/FerrimagneticLROUniversal.lean`:
`chain_bound_marshall_sector` (Tasaki's chain (4.1.16) at an arbitrary-weight Marshall sector
vector: `(γ − m²)‖w‖² ≤ ⟨w,(Ô_Λ)²w⟩.re`), `star_dotProduct_self_eq_sum_sector` (`‖Φ‖² = Σ_M
‖Φ_M‖²`), `heisenbergHamiltonianS_magSectorProjection_eigen` (a weight component of an H-eigenvector
is an H-eigenvector), the diagonal-shift `c` existence, and the global-flip / weight-commute
helpers. The remaining step to remove the axiom is the SU(2) Rayleigh-ratio constancy across the
spin-`S_tot` multiplet (transfer the per-sector bound from a near-central admissible sector to all
sectors via the merged iterated ladder-invariance) (#4617)
<!-- legacy-detail:end:654 -->

<a id="record-664"></a>
## Record from former line 664

**Lean name:** <!-- legacy-detail-lean:start:664 -->`orderSum_pow_two_denom_close` / `staggeredPhatS_manyBodyOperatorNormS_le` / `phatMoment_succ_le_normSq` / `orderSum_pow_phat_insert_close` / `tanakaOrderSecond2_eq_half_sum` / `tanaka_delta_eq` / `tanaka_delta_le` / `tanakaOrderSecond2_le`<!-- legacy-detail-lean:end:664 -->

**File:** <!-- legacy-detail-file:start:664 -->`Quantum/SpinS/AndersonTowerEnergyBound.lean`, `Quantum/SpinS/AndersonTowerTanakaFluctuation.lean`<!-- legacy-detail-file:end:664 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:664 -->
**Theorem 4.9 axis-2 transverse fluctuation decay** (§4.2.2, Tasaki Theorem 4.9 discharge PR4,
#4971;

eqs. (4.2.15)/(4.2.33)/(4.2.34)/(4.2.49)–(4.2.55)): the Tanaka state vanishes in the **axis-2
direction** (transverse to axis-1 SSB). The mechanism (the tower `u_k` is built from the axis-1
operator `Ô_L^{(1)} = (V/2) Ã`, `Ã = ô⁺ + ô⁻`, while the measured transverse observable is
`(ô^{(2)})²` with `ô^{(2)} = (2i)⁻¹(ô⁺ − ô⁻)`): per-site transverse fluctuation `δ_k := ⟨u_k|
(ô^{(2)})² |u_k⟩ = Q_k − R_k` with `Q_k = E_k/D_k` (single p̂-insertion, numerator `E_k = ⟨Φ, Ã^k p̂
Ã^k Φ⟩`), `R_k = D_{k+1}/(4D_k)` (ratio of denominators), `D_k = ⟨Φ, Ã^{2k} Φ⟩`. **(F1) Two-sided
denominator closeness** (`orderSum_pow_two_denom_close`, eq. 4.2.42): `|D_{m+1} − C(2(m+1),m+1)
P_{m+1}| ≤ C(2(m+1),m+1) · (m+1)² (N/V) (3/2 P_m)` via balanced-word expansion + fine bound
`orderWord_balanced_re_close_fine` (eq. 4.2.34). **(F2) Numerator closeness with p̂ insertion**
(`orderSum_pow_phat_insert_close`, eq. 4.2.50): `|E_k − C(2k,k) P_{k+1}| ≤ ...` via length-`2(k+1)`
balanced-word expansion with central p̂ + Vandermonde counting. **(Gap2) Rayleigh power ratio**
(`staggeredPhatS_manyBodyOperatorNormS_le`, `phatMoment_succ_le_normSq`): `P_{k+1} ≤ N² P_k` and
`‖p̂ u_k‖² ≤ P_{k+1}`. **(F3) Per-site fluctuation decomposition**
(`tanakaOrderSecond2_eq_half_sum`): `second2 = ½(δ_M + δ_{M+1})` (tower-term average). **(F4) δ_k
bound and capstone** (`tanaka_delta_eq`, `tanaka_delta_le`, capstone `tanakaOrderSecond2_le`): δ_k ≤
P_{k+1}/(D_k·2k+2) ≤ N²/(2k+2) + O(1/V) from Pascal ratio `(k+1) C(2k+2,k+1) = 2(2k+1) C(2k,k)` ⟹
second2 ≤ ε as L→∞. **Lemmas**: `staggeredPhatS_manyBodyOperatorNormS_le` (p̂ norm),
`phatMoment_succ_le_normSq` (ratio). **Status**: the section tip `tanakaOrderSecond2_le` is a
**proved theorem** (all of F1–Gap2–F3–F4 discharged axiom-free);

the overall Theorem 4.9 (`tanakaSSB_full_symmetry_breaking`) is now itself a **proved theorem**,
discharged in PR5 (#4972) by assembling this finite-`L` bound with the explicit tower sequence `M(L)
= ⌊L^{d/4}⌋` (see the Theorem 4.9 capstone row)
<!-- legacy-detail:end:664 -->

<a id="record-687"></a>
## Record from former line 687

**Lean name:** <!-- legacy-detail-lean:start:687 -->`stagOpVec_commutator_eq` / `totalSpinSOpVec_mul_cartWord_eq` / `totalSpinSOpVec_mulVec_cartWord_singlet` / `orderComm_mulVec_cartWord_singlet` / `cartWord_swap_dotProduct_eq`<!-- legacy-detail-lean:end:687 -->

**File:** <!-- legacy-detail-file:start:687 -->`Quantum/SpinS/AndersonTowerTelescoping.lean`<!-- legacy-detail-file:end:687 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:687 -->
**Cartesian order-word swap-band telescoping** (Tasaki §4.2.2, Prop 4.10;

**PROVED axiom-free**, Issue #4974, PR #5018): the three-part telescoping crux (push-through +
singlet boundary erasure + single-swap expectation identity) that resolves Cartesian order-word
contraction in Proposition 4.10's sphere-average argument. **Uniform order×order commutator**
(`stagOpVec_commutator_eq`): merges six off-diagonal and three diagonal commutators into `[ô^{(α)},
ô^{(β)}] = i Σ_γ ε_{αβγ} Ŝ^{(γ)}_tot`, feeding the swap-diff factorization `cartWord_swap_diff_eq`.
**Operator telescoping identity** (`totalSpinSOpVec_mul_cartWord_eq`): pushing total-spin generator
`Ŝ^{(γ)}_tot` through Cartesian order word `ô^{w}` via the uniform commutator yields the
length-preserving identity `Ŝ^{(γ)}_tot · ô^{w} = ô^{w} · Ŝ^{(γ)}_tot + i Σ_k Σ_δ ε_{γ w_k δ} ô^{w[k
↦ δ]}`, where `w[k ↦ δ]` is the word with its k-th letter rotated. **Singlet corollary**
(`totalSpinSOpVec_mulVec_cartWord_singlet`): on a total-spin singlet `Φ` (annihilated by `Ŝ³_tot`
and `Ŝ¹_tot`, hence by `Ŝ²_tot` via `totalSpinSOp2_mulVec_eq_zero_of_singlet`), the leading term
vanishes, leaving the pure rotation sum `Ŝ^{(γ)}_tot (ô^{w} Φ) = i Σ_k Σ_δ ε_{γ w_k δ} (ô^{w[k ↦ δ]}
Φ)` — the boundary erasure that allows Prop 4.10 to survive. **Intermediate helper**
(`orderComm_mulVec_cartWord_singlet`): combines the uniform order×order commutator with the singlet
corollary to produce the three-index signed sum `[ô^{(α)}, ô^{(β)}] (ô^{suf} Φ) = Σ_γ Σ_k Σ_δ (i
ε_{αβγ})(i ε_{γ suf_k δ}) (ô^{suf[k ↦ δ]} Φ)`. **Single-swap expectation identity**
(`cartWord_swap_dotProduct_eq`): the Cartesian analogue of Theorem 4.9's
`orderWordProd_swap_dotProduct_eq` (Bool eigenvalue telescoping). For a singlet `Φ`, one adjacent
transposition of order-word letters expands as a signed triple sum over shorter charge-removed
words: `⟨Φ, ô^{pre α β suf} Φ⟩ − ⟨Φ, ô^{pre β α suf} Φ⟩ = Σ_γ Σ_k Σ_δ (i ε_{αβγ})(i ε_{γ suf_k δ})
⟨Φ, ô^{pre ++ suf[k ↦ δ]} Φ⟩`. Equalities only; real-part band, operator-norm bound, and `O(1/V)`
estimate are PR-3.3 (Prop 4.10 capstone).
<!-- legacy-detail:end:687 -->
