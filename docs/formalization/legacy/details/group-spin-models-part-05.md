---
layout: page
title: "Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 5"
permalink: /formalization/legacy/details/group-spin-models-part-05/
---

# Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 5

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-767"></a>
## Record from former line 767

**Lean name:** <!-- legacy-detail-lean:start:767 -->`bondMaxSpinProjectionS` / `bondMaxSpinProjectionS_comm` / `regularGraphAKLTHamiltonianS` / `IsGeneralGraphVBSGroundState` / `tasaki_theorem_7_7`<!-- legacy-detail-lean:end:767 -->

**File:** <!-- legacy-detail-file:start:767 -->`Quantum/SpinS/GeneralAKLT.lean`<!-- legacy-detail-file:end:767 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:767 -->
**§7.3.2 AKLT model on a general graph** (Theorem 7.7;

eqs. (7.3.6)–(7.3.9)): the graph-centric generalized AKLT model and hexagonal-lattice correlation
decay. `bondCasimirS x y N = (Ŝ_x+Ŝ_y)² = 2S(S+1)·1 + 2Ŝ_x·Ŝ_y`;

`bondMaxSpinProjectionS x y N` = the **concrete** Lagrange/Casimir projector
`∏_{j=0}^{N−1}(Ĉ−j(j+1))/(N(N+1)−j(j+1))` onto the maximal bond total spin `J=N`, with symmetry
`bondMaxSpinProjectionS_comm: P̂_N[Ŝ_x+Ŝ_y] = P̂_N[Ŝ_y+Ŝ_x]` (commutativity in the symmetric
Heisenberg dot product). `regularGraphAKLTHamiltonianS G N = ½ Σ_{x,y} [G.Adj x y] P̂_N[Ŝ_x+Ŝ_y]` =
the **regular (uniform-spin) specialization** of eq. (7.3.7) (single global `S=N/2`, each bond →
`J=N`;

equals eq. 7.3.7 exactly on an `N`-regular graph — site-dependent spins `S̄_x=deg(x)/2` are not
expressible in `ManyBodyOpS Λ N`). On the 3-regular hexagonal lattice (`N=3`) it is `Σ_bonds P̂_3`
(eq. 7.3.8), the setting of Theorem 7.7. **Concrete VBS ground-state predicate:**
`IsGeneralGraphVBSGroundState G N Φ` is a **concrete def**, not a marker: the three conjuncts
`PosSemidef ∧ mulVec Φ = 0 ∧ Φ ≠ 0` state that the Hamiltonian is positive semidefinite, that `Φ` is
annihilated by it (zero-energy), and that `Φ` is nonzero. Correlation decay and infinite-volume
uniqueness are *not* part of this predicate;

they are the content of `tasaki_theorem_7_7`. `tasaki_theorem_7_7` (**DOCUMENTED AXIOM**;

Tasaki Theorem 7.7, §7.3.2, eqs. 7.3.6–7.3.9, pp. 210–212): the documented axiom asserts that for
every hexagonal lattice (`IsHexagonalLatticeAKLT`), there exist **size-independent** constants `C, ξ
> 0` (quantified outside all lattice instances) and a VBS ground state `Φ`
(`IsGeneralGraphVBSGroundState G 3 Φ`) realizing **both** the sign-alternating exponential
correlation decay `0 ≤ (−1)^{D(x,y)}⟨Ŝ_x·Ŝ_y⟩_Φ ≤ C e^{−D/ξ}` (eq. 7.3.9, `D = G.dist`) **and** the
translation-invariant infinite-volume uniqueness (`HasUniqueInfiniteVolumeVBSGroundState G 3`). The
axiom's `∃Φ` witness is not type-fixed;

any state satisfying the predicates may fulfill the existential. **Parallel axiom-free theorem:**
independently, on the specific canonical honeycomb torus `honeycombTorusGraph m` (`m ≥ 2`), the
concrete `honeycombVBSState m` is proven to be a **zero-energy VBS ground state** by the theorem
`honeycombVBSState_isGeneralGraphVBSGroundState` (line 724, `IsGeneralGraphVBSGroundState
(honeycombTorusGraph m) 3 (honeycombVBSState m)` with `#print axioms` = std3);

this theorem provides a genuine axiom-free fact about the canonical torus but **does not discharge
or reduce the axiom's claim** on general hexagons (decay estimates and infinite-volume uniqueness
remain unproven). **Axiom reason (documented):** the correlation decay (eq. 7.3.9) and
infinite-volume uniqueness remain unproven for a general hexagonal lattice due to real
implementation dependency — rigorous 2D honeycomb lattice complex-analysis foundation
(Kennedy–Lieb–Tasaki [41]) is absent from the repo and mathlib. The hexagonal restriction is
essential;

general-graph decay can fail. Capstone: `honeycombVBSState_isGeneralGraphVBSGroundState` (line 724)
<!-- legacy-detail:end:767 -->

<a id="record-768"></a>
## Record from former line 768

**Lean name:** <!-- legacy-detail-lean:start:768 -->`spinThreeHalfVBSBondVec` / `spinThreeHalfVBSBondSubspace` / `spinThreeHalfBondMaxProjection` / `spinThreeHalfVBSBondVec_linearIndependent` / `spinThreeHalfVBSBondVec_annihilated` / `bondMaxSpinProjectionS_three_local_rank` / `finrank_spinThreeHalfBondLocal_ker` / `spinThreeHalfBondLocal_ker_eq_vbsBondSubspace` / `bondMaxSpinProjectionS_three_local_isHermitian` / `bondMaxSpinProjectionS_three_local_idempotent` / `bondMaxSpinProjectionS_three_posSemidef` / `bondMaxSpinProjectionS_three_eq_onEmbS`<!-- legacy-detail-lean:end:768 -->

**File:** <!-- legacy-detail-file:start:768 -->`Quantum/SpinS/SpinThreeHalfBondProjection.lean`; `Quantum/SpinS/SpinThreeHalfBondEmbedding.lean`<!-- legacy-detail-file:end:768 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:768 -->
**§7.3.2 spin-3/2 local VBS bond certificate** (**PROVED**, `#print axioms` = std3, PR #5133;

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed. (Springer, 2020), §7.3.2,
eqs. (7.3.6)–(7.3.8), pp. 210–211): `spinThreeHalfVBSBondVec a b` gives the nine explicit two-site
physical vectors obtained from one normalized virtual singlet and endpoint symmetrization with two
unpaired virtual spin-halves at each endpoint;

the resulting physical vectors are not asserted to have unit norm. `spinThreeHalfVBSBondSubspace` is
their span, and `spinThreeHalfBondMaxProjection = bondMaxSpinProjectionS 0 1 3` is the concrete `16
× 16` Lagrange–Casimir projector onto total bond spin `J = 3`. The nine vectors are linearly
independent and are annihilated by this projector. The projector has rank `7`, its kernel has
dimension `9`, and `spinThreeHalfBondLocal_ker_eq_vbsBondSubspace` identifies that kernel exactly
with the nine-generator VBS bond subspace. The projector is also Hermitian, idempotent, and positive
semidefinite (`bondMaxSpinProjectionS_three_posSemidef`). `bondMaxSpinProjectionS_three_eq_onEmbS`
transports the local projector to any ordered pair via the block embedding. Proof: an explicit
seven-sector matrix certificate, followed by the rank–nullity comparison `7 + 9 = 16`. **Gate L
scope:** this local certificate did not itself construct a finite-volume honeycomb VBS state. The
subsequent finite-state slice does so and proves nonzeroness and global frustration-freeness, but
finite-volume uniqueness, the correlation estimate (7.3.9), and infinite-volume uniqueness remain
pending;

`tasaki_theorem_7_7` remains an axiom.
<!-- legacy-detail:end:768 -->
