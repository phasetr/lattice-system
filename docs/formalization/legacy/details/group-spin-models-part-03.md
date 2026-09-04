---
layout: page
title: "Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 3"
permalink: /formalization/legacy/details/group-spin-models-part-03/
---

# Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 3

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-689"></a>
## Record from former line 689

**Lean name:** <!-- legacy-detail-lean:start:689 -->`mulVec_toLp_norm_le` / `sqrt_vecNormSqRe_eq_toLp_norm` / `sqrt_vecNormSqRe_mulVec_le` / `totalSpinSOp1_manyBodyOperatorNormS_le` / `totalSpinSOp2_manyBodyOperatorNormS_le` / `stagOpVec_commutator_manyBodyOperatorNormS_le` / `cartWord_adjSwap_manyBodyOperatorNormS_diff_le` / `cartWord_swapChain_manyBodyOperatorNormS_diff_le`<!-- legacy-detail-lean:end:689 -->

**File:** <!-- legacy-detail-file:start:689 -->`Quantum/SpinS/ManyBodyOperatorNorm.lean` / `Quantum/SpinS/AndersonTowerCartWordReBand.lean`<!-- legacy-detail-file:end:689 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:689 -->
**Operator-norm → mulVec vector bound infrastructure** (Tasaki §4.2.2, Prop 4.10 arc PR-6b-i;

**PROVED axiom-free**, Issue #4974, PR #5040, p. 108): the **generic linear-algebra and
operator-norm bridge** converting operator-norm bounds into vector-norm bounds, feeding the Bochner
solid-angle interchange (`sphereAverage_directionStaggeredOp_pow_mulVec`, PR-L3) and sphere-average
vector assembly (PR-6b/6c). Three-level hierarchy: **(1) Generic L²-operator-norm → mulVec bound**
in `ManyBodyOperatorNorm.lean`: `mulVec_toLp_norm_le` establishes `‖G.mulVec v‖ ≤ ‖G‖·‖v‖` via
continuous-linear-map `toEuclideanCLM`; the real-norm wrapper `sqrt_vecNormSqRe_mulVec_le` combines
with `sqrt_vecNormSqRe_eq_toLp_norm` to express vector norms in square-root form for moment
inequalities. **(2) Spin-operator-norm scale** in `AndersonTowerCartWordReBand.lean`:
`totalSpinSOp{1,2,3}_manyBodyOperatorNormS_le` bound the three Cartesian total-spin generators by
`(V·N/2)` (diagonal) or `V·N` (off-diagonal), with per-site ladder norm `N`. **(3) Cartesian
order-word operator-norm band** (`stagOpVec_commutator_manyBodyOperatorNormS_le`,
`cartWord_adjSwap_manyBodyOperatorNormS_diff_le`,
`cartWord_swapChain_manyBodyOperatorNormS_diff_le`): operator-norm analogs of the scalar band
(PR-3.3a), bounding order-word commutators and swap chains by `k·(V·N)^{n−1}` (single-swap cost
`(V·N)` per length-`n` word, without the scalar singlet-Cauchy–Schwarz squaring). **(Scope)**:
L²-vector bounds and extended operator-norm infrastructure; the pinch capstone
(`cartWord_sphereAverage_pinch`, PR-3.3b) and later sphere-average assembly steps remain deferred.
<!-- legacy-detail:end:689 -->

<a id="record-735"></a>
## Record from former line 735

**Lean name:** <!-- legacy-detail-lean:start:735 -->`xyChemicalPotentialHamiltonianS` / `IsBECTowerConstantsHalfFilling` / `tasaki_5_2_bec_tower_half_filling` / `tasaki_5_2_bec_tower`<!-- legacy-detail-lean:end:735 -->

**File:** <!-- legacy-detail-file:start:735 -->`Quantum/SpinS/BoseEinsteinCondensate.lean`, `Quantum/SpinS/BoseEinsteinCondensateAlgebra.lean`, `Quantum/SpinS/BoseEinsteinCondensateMoment.lean`, `Quantum/SpinS/BoseEinsteinCondensateDenominator.lean`, `Quantum/SpinS/BoseEinsteinCondensateXYNumerator.lean`, `Quantum/SpinS/BoseEinsteinCondensateTower.lean`<!-- legacy-detail-file:end:735 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:735 -->
**Theorem 5.2** (§5.3, eqs. (5.3.2)–(5.3.4), footnote 8, p. 141): **low-lying tower states of
hard-core bosons** — **half-filling kernel PROVED axiom-free (`tasaki_5_2_bec_tower_half_filling`,
std3 only, PR #5060);

general-`μ` documented AXIOM (`tasaki_5_2_bec_tower`) retained**. The chemical-potential boson
Hamiltonian `Ĥ_μ = Ĥ − μ N̂` (spin form `2·xyHamiltonianS − μ·totalSpinSOp3`, since `Ĥ = 2 Ĥ_XY` and
`N̂ ↔ Ŝ_tot^(3)+L^d/2`, eq. 5.3.2;

the factor 2 keeps the documented `μ` equal to Tasaki's chemical potential, half filling `μ=0`).
Given a ground state `Φ_GS` of `Ĥ_μ` exhibiting ODLRO with `q₀ > 0` (Theorem 5.1), there are `C₁,C₂
> 0` (depending on `d`, the density selected by `μ`, and `q₀`) such that the bosonic tower states
`Γ_M = (Ô_L^{sgn M})^{\|M\|} Φ_GS` (`\|M\| ≤ C₁L^{d/2}`) are **nonvanishing and** low-lying — both
stated as conclusions (faithful to 5.2, which asserts `Γ_M` is nonvanishing) — with the **cubic**
energy increment `towerState ≠ 0 ∧ ⟨Γ_M,Ĥ_μ Γ_M⟩/⟨Γ_M,Γ_M⟩ ≤ E₀ + C₂\|M\|³/L^d` (eq. 5.3.4;

cubic, vs the quadratic `M²` of the Anderson-tower Theorem 4.6). Conditional on ODLRO (`q₀>0`);

P̂_hc = identity for spin-½. Proof: Koma–Tasaki [21]. **Half-filling discharge (`μ=0`,
axiom-free)**: the predicate `IsBECTowerConstantsHalfFilling` is the `μ=0` kernel of
`IsBECTowerConstants` with an inner premise conjunct `Ŝ_tot^(3) Φ=0` (the Theorem 5.1 half-filling
sector). Its foundations: `Ĥ_μ` Hermiticity (`xyChemicalPotentialHamiltonianS_isHermitian`,
`Quantum/SpinS/BoseEinsteinCondensateAlgebra.lean`) with the shared `rpow`–`sqrt` window bridge
`L^{d/2}=√(L^d)` (`LatticeSystem.Math.Ldhalf_bridge`, `Math/Analysis/RealRpowNatSqrt.lean`);

the U(1)-planar `p̂`-moment base entry `2q₀‖Φ‖² ≤ ⟨Φ,p̂Φ⟩` (`phatMoment_one_ge_of_planar_lro`,
`Quantum/SpinS/BoseEinsteinCondensateMoment.lean`), driven directly by the two XY-plane ODLRO
hypotheses (α=1,2) in place of the SU(2) singlet/isotropy base of Theorem 4.6;

the tower denominator geometric lower bound and non-vanishing `½(2q₀)^{\|M\|}·m₀ ≤
⟨Φ,(ô^∓)^{\|M\|}(ô^±)^{\|M\|}Φ⟩ = ‖(ô^±)^{\|M\|}Φ‖²`
(`becTowerDenominator_geom_lower_raising`/`_lowering`, `becTowerState_ne_zero_of_planar_lro`,
`Quantum/SpinS/BoseEinsteinCondensateDenominator.lean`), needing **only** the half-filling
`Ŝ_tot^(3)Φ=0` sector;

and the XY-planar variational numerator bound
(`Quantum/SpinS/BoseEinsteinCondensateXYNumerator.lean`) via the definitional split `Ĥ_XY = Ĥ_Heis −
Ĥ_ZZ` (`xyHamiltonianS_eq_heisenberg_sub_zz`, from `spinSDotXXZ_eq_spinSDot_add` at λ=0), splitting
`⟨Φ,[Aᴴ,[2 Ĥ_XY,A]]Φ⟩` into `2·(Heisenberg numerator) − 2·(ZZ numerator)`: the Heisenberg term
reuses `tower_numerator_bound` verbatim and the residual ZZ term is bounded by
`zz_tower_numerator_bound` (same `24 d N³`/`96 d N⁴/V` aggregates), yielding the `O(M²/V)`
`xy_tower_numerator_bound`. The **axiom-free** assembly
(`Quantum/SpinS/BoseEinsteinCondensateTower.lean`): at `μ=0` the Hamiltonian collapses to `Ĥ_0 = 2
Ĥ_XY` (`xyChemicalPotentialHamiltonianS_zero`), so the variational gap
(`variational_gap_le_double_commutator`) is bounded by `xy_tower_numerator_bound` (no residual
first-order `μ`-term), and the denominator `½ P_M ≤ ‖(ô^±)^M Φ‖²` (`tower_denominator_lower_bound`)
cancels the `P_M`, giving the quadratic trial bound `E₀ + 8·towerEnergyCoeff`
(`becTowerState_pos/neg_rayleigh_bound_halfFilling`);

`towerEnergyCoeff_le` sharpens it to `O(M²/L^d)` and the rounding `M² ≤ |M|³` (`|M| ≥ 1`) casts into
the faithful cubic `C₂|M|³/L^d` (eq. 5.3.4, footnote 8);

`becTowerConstantsHalfFilling_of_planar_lro` constructs explicit `C₁,C₂ > 0`, and
`tasaki_5_2_bec_tower_half_filling` closes the existential (`#print axioms` =
propext/Classical.choice/Quot.sound only). **Only the half-filling kernel is discharged
axiom-free**;

the general-`μ` `tasaki_5_2_bec_tower` stays a documented axiom because at `μ≠0` a ground state has
`Ŝ_tot^(3)Φ=s₀≠0`, so the reused half-filling bricks no longer close and the bound rests on the
Koma–Tasaki [21] `d`-dimensional reflection-positivity/infrared machinery, the same
RP-intractability exception as Theorem 5.1
<!-- legacy-detail:end:735 -->

<a id="record-736"></a>
## Record from former line 736

**Lean name:** <!-- legacy-detail-lean:start:736 -->`becCoherentState` / `IsBECCoherentSSBConstants` / `tasaki_5_3_bec_u1_ssb` / `IsBECCoherentSSBConstantsHalfFilling` / `becCoherentState_dotProduct_mulVec` / `becCoherent_complexMoment_raising` / `becCoherent_complexMoment_lowering` / `becCoherent_secondMoment1_eq` / `becCoherent_secondMoment2_eq`<!-- legacy-detail-lean:end:736 -->

**File:** <!-- legacy-detail-file:start:736 -->`Quantum/SpinS/BoseEinsteinCondensate.lean`, `Quantum/SpinS/BoseEinsteinCondensateSector.lean`, `Quantum/SpinS/BoseEinsteinCondensateCoherentMatrixElement.lean`, `Quantum/SpinS/BoseEinsteinCondensateCoherentMoment.lean`, `Quantum/SpinS/BoseEinsteinCondensateCoherentConcentration.lean`, `Quantum/SpinS/BoseEinsteinCondensateCoherentSecondMoment.lean`, `Quantum/SpinS/BoseEinsteinCondensateCoherentSecondMomentConcentration.lean`, `Quantum/SpinS/BoseEinsteinCondensateCoherentAssembly.lean`<!-- legacy-detail-file:end:736 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:736 -->
**Theorem 5.3** (§5.3, AXIOM; eqs. (5.3.5)–(5.3.8)): **U(1) symmetry-breaking states of hard-core
bosons** — the BEC counterpart of the Tanaka Theorem 4.9. The phase-`θ` **coherent state** `Ξ_θ =
(2M_max+1)^{−1/2} Σ_{M=−M_max}^{M_max} e^{−iMθ} Γ_M` (eq. 5.3.5; `Γ_M` = normalized tower state),
with a slow window `M_max(L)` (`IsSlowBECWindow`: monotone, → ∞, `≤ C₁L^{d/2}` eventually). For
every `θ` and realizing ground-state family (eventual GS of `Ĥ_μ` with ODLRO `q₀`, nonvanishing
tower states over `\|M\| ≤ C₁L^{d/2}`), **there exists a sufficiently slowly diverging** `M_max`
(existential, matching Tasaki's "if `M_max` diverges not too rapidly" and Theorem 4.9's `∃ M`) for
which `Ξ_θ` fully breaks U(1): **(5.3.7)** `⟨Ô_L^(1)⟩/L^d → m\*cosθ`, `⟨Ô_L^(2)⟩/L^d → m\*sinθ`;

**(5.3.8)** `⟨(Ô_L^(α))²⟩/(L^d)² → (m\*cosθ)²/(m\*sinθ)²`;

**(5.3.6)** the complex moments (`expectationRatioComplex`) `⟨Ô_L^±⟩/L^d → m\*e^{±iθ}`. The order
parameter obeys `m\* ≥ √(2q₀)` (U(1) `√2`, vs SU(2) `√3` of Theorem 4.11). Limits in the sound
eventual-`ε` form (footnote 9). Conditional on ODLRO; `μ` parametrizes density. Proof: Koma–Tasaki.
**Half-filling kernel DISCHARGED (conditional)** — the theorem `tasaki_5_3_bec_u1_ssb_half_filling`
has `#print axioms` = std3 + `becMStar_ge_sqrt_twoQ` (documented `√2` bound) **and** additionally
requires the explicit hypothesis `hRealizing` (the Koma–Tasaki [66] uniform window-ratio
concentration input, carried as a hypothesis with parity to the SU(2) Prop 4.10's Conjecture 4.12),
tracker #5061, final PR #5069; general-`μ` documented AXIOM (`tasaki_5_3_bec_u1_ssb`) retained.
**Half-filling discharge arc COMPLETE (tracker #5061)**: the `μ=0` kernel is discharged as the
theorem `tasaki_5_3_bec_u1_ssb_half_filling` (predicate `IsBECCoherentSSBConstantsHalfFilling`, the
half-filling kernel of `IsBECCoherentSSBConstants` adding the `Ŝ_tot^(3)Φ=0` sector conjunct,
mirroring Theorem 5.2). **PR-1 (#5062)**: the predicate + the coherent-state Rayleigh numerator
double-sum expansion `becCoherentState_dotProduct_mulVec` (`⟨Ξ_θ,O Ξ_θ⟩ = (2M_max+1)^{−1} Σ_{M',M}
conj(e^{−iM'θ})e^{−iMθ}⟨Γ_{M'},O Γ_M⟩`, the algebraic core of eqs. 5.3.6–5.3.8), std3 only. **PR-2
(#5063)**: the total-`Ŝ³` sector structure that collapses that double sum —
`towerState_totalSpin3_eigenvector` (`Ŝ³_tot Γ_M = M Γ_M` at half filling, eq. 5.3.3),
`towerState_inner_eq_zero_of_ne` (distinct-`M` tower states are orthogonal: Hermitian `Ŝ³_tot`,
distinct real eigenvalues), and `towerState_unitNormalize_inner_eq_zero_of_ne` (the normalized `Γ_M`
`O=1` consumption form), reusing the §4.2 sector commutators `[Ŝ³_tot, Ô^±] = ±Ô^±`; std3 only.
**PR-3 (#5064)**: the off-diagonal matrix elements that survive the sector collapse —
`becOffDiagonal_ne_adjacent_eq_zero` (`⟨Γ_{M'}, Ô^+ Γ_M⟩ = 0` for `M' ≠ M+1`, since `Ô^+ Γ_M` sits
in the `Ŝ³_tot = M+1` sector) and `becOffDiagonal_eq_norm_ratio` (on the raising side `M ≥ 0`, both
tower states nonzero, the single surviving adjacent element is the real norm ratio `⟨Γ_{M+1}, Ô^+
Γ_M⟩ = √(D_{M+1}/D_M)`, `D_M = ‖(Ô^+)^M Φ‖² = vecNormSqRe (towerState … M Φ)`, because there `Ô^+
towerState M Φ = towerState (M+1) Φ` exactly, so `Ô^+ Γ_M ∥ Γ_{M+1}`), plus its lowering-side mirror
`becOffDiagonal_eq_norm_ratio_neg` (for `M ≤ −1` the same `Ô^+`-sandwiched element is the
**inverse** ratio `⟨Γ_{M+1}, Ô^+ Γ_M⟩ = √(D_M/D_{M+1})`, since there the tower is built with `Ô^−`
and `(Ô^+)ᴴ = Ô^−` adjoint reversal + the lowering recursion `Ô^− towerState (M+1) Φ = towerState M
Φ` collapse the sandwich to `‖Γ_M‖²`); std3 only. **PR-4 (#5065)**: the Cesàro window collapse of
both complex moments (eq. 5.3.6 ±) — `becCoherent_complexMoment_raising` gives the exact finite-`L`
representation `⟨Ξ_θ, Ô^+ Ξ_θ⟩ = e^{iθ} (2M_max+1)^{−1} Σ_{M=−M_max}^{M_max−1} ⟨Γ_{M+1}, Ô^+ Γ_M⟩`:
the `becCoherentState_dotProduct_mulVec` double sum is collapsed to the adjacent band `M'=M+1` by
`becOffDiagonal_ne_adjacent_eq_zero`, the surviving phase `conj(e^{−i(M+1)θ})e^{−iMθ}` telescopes to
the common factor `e^{iθ}` (sign-independent), and the `M=M_max` term drops (`M_max+1` is outside
the window); each summand `⟨Γ_{M+1}, Ô^+ Γ_M⟩` is the real nonnegative `r_M` (raising-side
`√(D_{M+1}/D_M)` / lowering-side `√(D_M/D_{M+1})`). Its `Ô^−` mirror
`becCoherent_complexMoment_lowering` gives `⟨Ξ_θ, Ô^− Ξ_θ⟩ = e^{−iθ} (2M_max+1)^{−1}
Σ_{M=−M_max+1}^{M_max} ⟨Γ_{M−1}, Ô^− Γ_M⟩` (collapsed by the adjoint-derived
`becOffDiagonal_lowering_ne_adjacent_eq_zero`, `(Ô^−)ᴴ=Ô^+`), with both-branch lowering norm ratios
`becOffDiagonal_lowering_eq_norm_ratio` (`M ≤ 0`) / `becOffDiagonal_lowering_eq_norm_ratio_pos` (`M
≥ 1`); the window means converge to `m∗` in a later PR; std3 only. **PR-5 (#5066)**: the axis window
means (eq. 5.3.7) — `becCoherent_mean1` gives `⟨Ξ_θ, Ô^(1) Ξ_θ⟩ = cos θ · (2M_max+1)^{−1}
Σ_{M=−M_max}^{M_max−1} ⟨Γ_{M+1}, Ô⁺ Γ_M⟩` and `becCoherent_mean2` the `sin θ` counterpart for
`Ô^(2)`, via the (now public) Cartesian decompositions `staggeredOrderOp1S_eq_half_smul` (`Ô^(1) =
½(Ô⁺+Ô⁻)`) / `staggeredOrderOp2S_eq_smul` (`Ô^(2) = (2i)^{−1}(Ô⁺−Ô⁻)`), the ± complex moments
(PR-4), the lowering→raising window symmetrisation `becCoherent_loweringWindow_eq_raisingWindow`
(reindex `M ↦ M−1`, each lowering element equalling the raising element one step down via
`becOffDiagonal_lowering_shift_eq`), and the Euler identities `½(e^{iθ}+e^{−iθ}) = cos θ` /
`(2i)^{−1}(e^{iθ}−e^{−iθ}) = sin θ`; std3 only. **PR-6 (#5067)**: the order-parameter concentration
lower bound `m∗ ≥ √(2q₀)` (Tasaki §5.3, "As in Theorem 4.11 … we can prove the bound `m∗ ≥ √(2q₀)`.
See (4.2.39)", pp. 141–142), recorded as a **documented axiom** `becMStar_ge_sqrt_twoQ` — the BEC
half-filling counterpart of the SU(2) concentration axiom `orderSqMoment_ratio_le_mStarSq_family`
(Theorem 4.11) and the `p̂`-mirror `mStar_eq_phat_ratio_limit`, with the `U(1)` planar factor `√2`
(two axes `α=1,2`, base ratio `→ 2q₀`) replacing the SU(2) `√3`. Per the 2026-07-12 no-overreach
boundary the Koma–Tasaki [66] concentration mechanism is deferred with parity to those axioms, not
rebuilt. `m∗` is **pinned** to its genuine value by the new predicate `IsRealizingBECCoherentFamily`
(the `U(1)` planar analogue of `IsRealizingTanakaGroundStateFamily`: a **slow window**
`IsSlowBECWindow d C₁ Mwin` (monotone, diverging, eventually `Mwin L ≤ C₁ L^{d/2}` — a bare `Tendsto
Mwin atTop atTop` is **insufficient**: a fast window outrunning `C₁ L^{d/2}` dilutes the
normalization and admits a false witness pinning `m∗` below `√(2q₀)`, an over-quantification defect)
+ eventual `μ=0` half-filling GS with `Ŝ³_tot Φ=0`, two-axis ODLRO `≥ q₀`, nonzero window tower
states, and the **uniform window-ratio pinning** — eventually every one-step ratio `r_M = ⟨Γ_{M+1},
Ô⁺ Γ_M⟩/L^d` in the window is within `ε` of `m∗`, which subsumes the `θ=0` mean limit `⟨Ξ_0, Ô^(1)
Ξ_0⟩/L^d → m∗` (eq. 5.3.7) **and** drives the eq. 5.3.8 second-moment
concentration (`S₂=avg r_M²`, `S₁₁=avg r_M r_{M+1} → m∗²`) axiom-free from one source; axis-1
singlet and reversal invariance are **not** imposed, unlike the SU(2) family, so it is directly
instantiable by the BEC ground state). A free `m∗` would make the bound FALSE (`m∗:=0`, `q₀>0`),
hence the family pinning; the pinned bound is only the "easy half" `m∗² ≥ 2q₀`, never the still-open
equality `m∗²=2q₀`. The axiom is **declared but not yet consumed** (the final discharge that uses it
is a later arc PR), so all PR-6 new declarations remain std3; unsatisfiable in `d=1` (Corollary
4.3), so vacuous there. The general-`μ` `tasaki_5_3_bec_u1_ssb` stays a documented axiom (d-dim
RP-intractability, Koma–Tasaki [21]). **PR-6b (#5068)**: the exact finite-`L` band representation of
the coherent second moments (eq. 5.3.8) —
`becCoherent_secondMoment1_eq`/`becCoherent_secondMoment2_eq` split `⟨Ξ_θ,(Ô^(α))²Ξ_θ⟩` into the
`¼`/`−¼`-weighted four two-step products (`staggeredOrderOp1S_sq_eq`/`_sq_eq`), and the four band
collapses `becCoherent_raisingRaising_collapse`/`_loweringLowering_collapse` (off-diagonal, phases
`e^{±2iθ}`) / `_raisingLowering_collapse`/`_loweringRaising_collapse` (diagonal) collapse the
coherent double sum to the single surviving sector band via the two-step orthogonality
`becBand_ne_eq_zero_of_intEigen` and the generic `becCoherent_band_collapse` (`k=±2`) /
`becCoherent_diagonal_collapse` (`k=0`); entirely axiom-free (std3 only, no concentration axiom).
The band-value reduction (`r_M` products, diagonal `2r_M²`+Lemma 4.14 remainder) and the
`(m∗cosθ)²`/`(m∗sinθ)²` limits are the assembly sequel. **PR-7 (#5069, final discharge)**: the
diagonal `Ô⁻Ô⁺` band collapses to `‖ρ_M‖²` (`M≥0`) and, via the exact commutator `Ô⁺Ô⁻−Ô⁻Ô⁺=2Ŝ³`, to
`‖ρ_{M-1}‖²−2M` (`M≤−1`, the `−2M/(L^d)²` residual uniformly small in the slow window
`M_win≤C₁L^{d/2}`, `L^{d/2}≤L^d`), and the off-diagonal `Ô⁺Ô⁺` band factors to `ρ_{M+1}ρ_M`; each
concentrates on `m∗²`/`e^{2iθ}m∗²` by the uniform window-ratio pinning (generic Cesàro engine
`becWindowAvg_of_termwise`, `O(K)` bad set), giving `becLR_moment_limit`/`becRR_moment_limit`. The
remaining two bands follow from `⟨Ô⁺Ô⁻⟩=⟨Ô⁻Ô⁺⟩` (`becCoherent_RL_eq_LR`, since `⟨Ξ,Ŝ³Ξ⟩=0`) and
`⟨Ô⁻Ô⁻⟩=conj⟨Ô⁺Ô⁺⟩` (`becCoherent_LL_eq_conj_RR`); with `cos²θ=¼(e^{2iθ}+2+e^{−2iθ})` (and its
`sin²` companion) the four bands assemble to the eq. (5.3.8) squared-moment limits, completing all
six SSB conjuncts. **`tasaki_5_3_bec_u1_ssb_half_filling` DISCHARGED (conditional); `#print axioms`
= std3 + `becMStar_ge_sqrt_twoQ`, AND requires the explicit `hRealizing` hypothesis**
(realizing-family existence = Koma–Tasaki [66] uniform window-ratio pinning; same double structure
as Prop 4.10's `#print` + Conjecture 4.12 hypothesis; requires `d≥2`); per-family `∃mStar,∃Mmax`
quantified outside `∀θ` (single order parameter per family); the two orphaned `Ô⁻Ô⁻`/`Ô⁺Ô⁻`
collapses were deleted (bands recovered by the two identities)
<!-- legacy-detail:end:736 -->

<a id="record-744"></a>
## Record from former line 744

**Lean name:** <!-- legacy-detail-lean:start:744 -->`lsmTwistOperator` / `lsm_energy_bound` / `lsm_ground_twist_orthogonal` / `lieb_schultz_mattis_affleck_lieb`<!-- legacy-detail-lean:end:744 -->

**File:** <!-- legacy-detail-file:start:744 -->`Quantum/SpinS/LiebSchultzMattis.lean`, `Quantum/SpinS/LiebSchultzMattisRingGap.lean`, `Quantum/SpinS/LiebSchultzMattisProof.lean`, `Quantum/SpinS/LiebSchultzMattisOrthogonality.lean`<!-- legacy-detail-file:end:744 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:744 -->
**§6.2 Theorem 6.3** (Lieb–Schultz–Mattis, Affleck–Lieb;

**all PROVED, axiom-free**; eqs. (6.2.1)–(6.2.19)): for a **half-odd-integer** spin chain the gap is
`O(1/L)`. The **twist operator** `Û_LSM = exp[−i Σ_x θ_x Ŝ_x^(3)]` (`θ_x = (2π/L)x`, eq.
6.2.2/6.2.3, via `NormedSpace.exp`) and the **trial state** `Φ_LSM = Û_LSM Φ_GS` (eq. 6.2.4) are
defined;

**Lemma 6.1** (`lsm_energy_bound`, eq. 6.2.5;

**PROVED**, axiom-free, in `LiebSchultzMattisProof.lean`): `⟨Φ_LSM,ĤΦ_LSM⟩/⟨Φ_LSM,Φ_LSM⟩ − E_GS ≤
8π²S²/L` for any `S` — via the per-bond symmetrised twist identity `Û†(Ŝ_x·Ŝ_y)Û + Û(Ŝ_x·Ŝ_y)Û† −
2(Ŝ_x·Ŝ_y) = (2cos(θ_x−θ_y)−2)·XY_{xy}` (the longitudinal `Ŝ³Ŝ³` part and the imaginary current
cancel in the `±θ` average), `cos(θ_x−θ_y)=cos(2π/L)` on every bond, `|⟨XY_b⟩.re| ≤ 2S²‖Φ‖²`, and
`1−cos(2π/L) ≤ (2π/L)²/2` summed over the `L` bonds;

**Lemma 6.2** (`lsm_ground_twist_orthogonal`, eq. 6.2.18;

**PROVED**, axiom-free, in `LiebSchultzMattisOrthogonality.lean`): for `N` odd (half-odd-integer
`S`) and the unique GS (`Ŝ_tot^(3)=0`, `huniq` uniqueness), `⟨Φ_GS,Φ_LSM⟩=0` — via the cyclic
**translation operator** `T̂` (config-shift permutation): `T̂` commutes with `Ĥ` so the unique GS is
a translation eigenvector `T̂Φ_GS=cΦ_GS` (`|c|=1`), and the diagonal transformation law `T̂†Û_LSM T̂
= (−1)^{2S} Û_LSM e^{i(2π/L)Ŝ_tot^(3)}` (eq. 6.2.17, reduced to a per-config `lsmPhase` identity
with a `2π` boundary wrap giving `(−1)^N`) forces `⟨Φ_GS,Φ_LSM⟩=(−1)^N⟨Φ_GS,Φ_LSM⟩`, vanishing for
`N` odd;

**Theorem 6.3** (`lieb_schultz_mattis_affleck_lieb`, eq. 6.2.19;

**PROVED**, axiom-free, in `LiebSchultzMattisRingGap.lean`): for `N` odd and even `L`, ∃ a positive
spectral gap (`IsPositiveSpectralGap` from §6.1) `≤ 8π²S²/L` — so a half-odd-integer chain cannot
have both a unique GS and a gap (the rigorous half of the Haldane conjecture). `S=N/2`. **The axiom
is discharged**: ground-state uniqueness of the ring (connected-graph Marshall–Lieb–Mattis,
`ringSym_ground_uniqueness` + `afm_ring_ground_state_data` over
`LiebSchultzMattisRing{Uniqueness,GroundUnique,EigenTransfer,MLMUnique,GroundData}.lean`) gives a
one-dimensional `Ŝ_tot³=0` ground line; the generic Courant–Fischer second-eigenvalue bound
`hermitian_second_eigenvalue_variational` (`HermitianSecondEigenvalue.lean`) with the existence of
an eigenvalue above the ground line (`hermitian_exists_eigenvalue_gt`, `HermitianGapExists.lean`)
defines `E₁`, and Lemma 6.1 (trial energy) + Lemma 6.2 (orthogonality) bound `E₁ ≤ E₀+8π²S²/L`
<!-- legacy-detail:end:744 -->

<a id="record-747"></a>
## Record from former line 747

**Lean name:** <!-- legacy-detail-lean:start:747 -->`IsShortRangeU1Chain` / `tasaki_lemma_6_4_general_trial_energy_bound`<!-- legacy-detail-lean:end:747 -->

**File:** <!-- legacy-detail-file:start:747 -->`Quantum/SpinS/LiebSchultzMattisGeneral.lean`, `Quantum/SpinS/LiebSchultzMattisProof.lean`, `Quantum/SpinS/LiebSchultzMattisGlobalLocalReduction.lean`, `Quantum/SpinS/LiebSchultzMattisGeneratorNorm.lean`, `Quantum/SpinS/LiebSchultzMattisTaylorBound.lean`, `Quantum/SpinS/LiebSchultzMattisGeneralDischarge.lean`, `Math/MatrixAnalysis/HermitianExpUnitary.lean`, `Quantum/SpinS/ManyBodyOperatorNorm.lean`<!-- legacy-detail-file:end:747 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:747 -->
**§6.2 Lemma 6.4** (generalized LSM variational bound;

PROVED, `#print axioms` = std3, PR #5077;

eqs. (6.2.23)–(6.2.24)): Lemma 6.1 generalizes to **any** short-ranged U(1)-invariant chain `Ĥ = Σ_x
ĥ_x`. The class `IsShortRangeU1Chain L N r h₀ h` bundles: each `ĥ_x` is **Hermitian** (so `Σ_x ĥ_x`
is a genuine Hamiltonian), `r`-local (`IsLocalRangeR`, now the **commutant-form `def`**: `ĥ_x`
commutes with every single-site operator farther than `r` from `x`; the general equivalence between
this commutant form and `support ⊆ {y : ringDist x y ≤ r}` is a proved theorem of this repository,
`supportedOnS_iff_commute_onSiteS` (`Quantum/SpinS/OperatorSupport.lean`), though `IsLocalRangeR`
itself has not yet been connected to it;

strong form chosen so the shared §7.1.3 Theorem 7.3 hypothesis stays faithful;

discharge arc **COMPLETE** (axiom-free), PR #5071–#5077), bounded `manyBodyOperatorNormS (ĥ_x) ≤
h₀`, and U(1)-invariant (`Commute (ĥ_x) totalSpinSOp3`). Then ∃ `C>0` (depending only on `S,r,h₀`)
such that for **any** ground state `Φ_GS` (uniqueness not assumed), `⟨Φ_LSM,ĤΦ_LSM⟩/⟨Φ_LSM,Φ_LSM⟩ −
E_GS ≤ C/L` for any `L` (eq. 6.2.24);

`C` is outermost (uniform over `L,ĥ,Φ_GS`). Tasaki remarks that for half-odd-integer `S` +
translation-invariant GS a generalized orthogonality gives `0 ≤ E_1st − E_GS ≤ C/L` (as in Theorem
6.3);

that gap consequence is **not** formalized here (the formal Lemma 6.2 is Heisenberg-chain-specific).
Discharge infrastructure (PR #5072): the **centered local twist generator** `M̂_x = localTwistGen L
N r x := Σ_{y∈W_x} (2π/L)·δ(x,y)·Ŝ_y^{(3)}` (eq. 6.2.27) over the range-`r` window `window L r x =
{y : ringDist x y ≤ r}`, with `δ(x,y) = signedRingDisp L x y` the **ring-distance-centered** signed
displacement (`|δ| = ringDist`, avoiding the `2π` seam jump of the raw angle `θ_y = 2π(y+1)/L` on
wrapping windows);

`M̂_x` is Hermitian (`localTwistGen_isHermitian`), so `exp(±i M̂_x)` are unitary conjugators through
the identities in `Math/MatrixAnalysis/HermitianExpUnitary.lean`. The generic norm lemma
`manyBodyOperatorNormS_unitary_conj` (`‖U Y Uᴴ‖ = ‖Y‖`) is provided by
`Quantum/SpinS/ManyBodyOperatorNorm.lean` for the second-order twist-conjugation bound. PR-3 (PR
#5073): the **outer variational reduction** (eq. 6.2.25) is generalized to an **arbitrary**
Hamiltonian `Ĥ : ManyBodyOpS` — `lsm_energy_diff_symm_sum_general` (the symmetrised twist gap equals
the Rayleigh quotient of `Û†ĤÛ + ÛĤÛ† − 2Ĥ`) and `groundEnergy_le_expectationRatioRe_general` (`E_GS
≤` any Rayleigh quotient of a Hermitian `Ĥ`);

the Heisenberg-chain forms `lsm_energy_diff_symm_sum` / `groundEnergy_le_expectationRatioRe` are now
thin specializations, so the reduction applies verbatim to `Ĥ = Σ_x ĥ_x`. PR-4 (CRUX A, PR #5074):
the **global→local twist reduction** (eq. 6.2.27) `twistConj_eq_localGen` — for a short-ranged
U(1)-invariant chain, `Û_LSM† ĥ_x Û_LSM = exp(+i M̂_x) ĥ_x exp(−i M̂_x)` (with mirror
`twistConj'_eq_localGen`). Both generators are diagonal, so conjugation acts on each `(σ',σ)` entry
by the scalar `exp(±i(φ_σ'−φ_σ))`;

whenever `ĥ_x[σ',σ]≠0` the commutant locality (`IsLocalRangeR` →
`isLocalRangeR_apply_eq_zero_of_far`, using distinct `Ŝ^(3)` eigenvalues) forces `σ'_y=σ_y` off the
window and U(1)-invariance (`commute_totalSpinSOp3_apply_eq_zero_of_mag_ne`) forces equal total
magnetization, so the global and local phase differences agree **modulo 2π** (`twistPhase_gap`): the
mean-angle term drops by U(1) and the residual `2π·(integer)` is the periodic-seam winding
`ringWrap` (spinor two-valued `exp(2πi·m)=1`). PR-5 (PR #5075,
`Quantum/SpinS/LiebSchultzMattisGeneratorNorm.lean`): the **centered generator norm bound**
`localTwistGen_manyBodyOperatorNormS_le` — `‖M̂_x‖ ≤ π r (2r+1) N / L =: B/L` (eq. 6.2.27). By the
finite-sum triangle inequality and scalar homogeneity of `manyBodyOperatorNormS`, `‖M̂_x‖ ≤
Σ_{y∈W_x} |(2π/L)δ(x,y)|·‖Ŝ_y^{(3)}‖`;

each coefficient is `≤ 2πr/L` (the centering gives `|δ| = ringDist ≤ r`,
`natAbs_signedRingDisp_eq_ringDist`, so the raw angle's `2π` seam spread is avoided) and each
`‖Ŝ_y^{(3)}‖ ≤ N/2`, over a window of `≤ 2r+1` sites (`window_card_le`: `δ(x,·)` injects `W_x` into
`{−r,…,r}`, injectivity from `dvd_sub_signedRingDisp`). This uniform `O(1/L)` bound feeds the
`O(‖M̂_x‖²)` second-order twist-conjugation bound (PR-6/PR-7), whose sum over the `L` sites gives
the Lemma 6.4 `C/L`. PR-6 (CRUX B, PR #5076, `Quantum/SpinS/LiebSchultzMattisTaylorBound.lean`): the
**second-order Taylor superoperator norm bound** `symmetricDifference_conj_norm_le` — `‖exp(+iM) X
exp(−iM) + exp(−iM) X exp(+iM) − 2X‖ ≤ 8‖M‖²‖X‖` for Hermitian `M` (eqs. 6.2.28–6.2.30, pp.
164–165). Setting `A = −iM` (anti-Hermitian, `Aᴴ = −A`), the matrix conjugation `f(t) = exp(tA) X
exp(−tA)` (`expConjOp`) has derivative `f'(t) = exp(tA)[A,X]exp(−tA)` (`hasDerivAt_expConjOp`,
product rule + `hasDerivAt_exp_smul_const`), so `f''(t) = exp(tA)[A,[A,X]]exp(−tA)`;

unitary conjugation preserves the L² operator norm (`manyBodyOperatorNormS_expConjOp`, consuming the
PR-2 `manyBodyOperatorNormS_unitary_conj`), whence `‖f''(t)‖ = ‖[A,[A,X]]‖ ≤ 4‖M‖²‖X‖`. The
symmetric combination `F(t) = f(t) + f(−t)` has `F'(0) = 0` and `‖F''‖ ≤ 2‖[A,[A,X]]‖`, so two
applications of the segment mean-value inequality `norm_image_sub_le_of_norm_deriv_le_segment'` give
`‖F(1)−F(0)‖ = ‖f(1)+f(−1)−2f(0)‖ ≤ 8‖M‖²‖X‖`. The `O(‖M‖²)` order (not `O(‖M‖)`) is essential: the
first-order term cancels in the symmetric difference, turning the per-site `O(1/L²)` into the summed
`O(1/L)`. Replaces the book's `ad(M̂_x)` eigen-monomial decomposition (6.2.29) by a
finite-dimensional Taylor remainder (sound weaker constant;

the axiom only needs `C=C(N,r,h₀)`). PR-7 (final discharge, PR #5077,
`Quantum/SpinS/LiebSchultzMattisGeneralDischarge.lean`): the **assembly** turns the former axiom
into the proved theorem `tasaki_lemma_6_4_general_trial_energy_bound` (`#print axioms` = std3). `Δ₊
≤ Δ₊ + Δ₋` (the back-twist difference `Δ₋ ≥ 0` by the variational lower bound
`groundEnergy_le_expectationRatioRe_general`), and the `±θ`-symmetrised sum
(`lsm_energy_diff_symm_sum_general`) equals the Rayleigh quotient of `Û†ĤÛ + ÛĤÛ† − 2Ĥ = Σ_x (Û†ĥ_xÛ
+ Ûĥ_xÛ† − 2ĥ_x)`;

each summand reduces (CRUX A `twistConj_eq_localGen` / `twistConj'_eq_localGen`) to a
local-generator conjugation, bounded (CRUX B `symmetricDifference_conj_norm_le`) by `8‖M̂_x‖²‖ĥ_x‖ ≤
8(B/L)²h₀` (`localTwistGen_manyBodyOperatorNormS_le` + `norm_le`), summing over the `L` sites to
`8B²h₀/L`;

the Rayleigh quotient is `≤ ‖·‖` (`expectationRatioRe_le_manyBodyOperatorNormS`, operator
Cauchy–Schwarz), giving `Δ₊ ≤ C/L` with `C = 8B²|h₀|+1`. The unused operator-form unitarity lemmas
`localTwistOperator_*` were **deleted** (the per-site bound stays in the `exp(±i M̂_x)` form)
<!-- legacy-detail:end:747 -->

**Correction (outside the frozen record above).** The frozen record from former line 747 cites
`dvd_sub_signedRingDisp` for the injectivity used by `window_card_le`; the current source names
that lemma `signedRingDisp_injective` (`Quantum/SpinS/RingDistance.lean`). The
frozen record text above is left unedited to preserve exact historical parity.
