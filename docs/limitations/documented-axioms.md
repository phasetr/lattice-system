---
layout: page
title: "Documented-axiom status and axiomatization policy"
permalink: /limitations/documented-axioms/
---

# Documented-axiom status and axiomatization policy

> This current policy text was moved losslessly from the former monolithic index. Declaration-level status remains authoritative in the interim legacy catalogue until #5228.

<!-- legacy-source:start:155:216 -->
### Appendix A: status and axiomatization policy

Tasaki's **Appendix A is fully formalized in book order (A.1–A.28)**, and the
entire Tasaki text up to and including Chapter 11 (§11.5) plus this appendix is
now covered. The appendix splits into two kinds of items:

- **Proved (axiom-free)** — the linear-algebra and angular-momentum core that
  `mathlib` supports directly: **A.1** (the Lie product / Trotter formula, proved
  from scratch in a complete normed `ℝ`-algebra), **A.12** (the strong-coupling
  effective Hamiltonian limit, by the `v⁻¹`-squeeze + kernel-pairing continuity
  argument), **A.4–A.6**
  (positive-semidefinite basics + unique
  PSD square root), **A.7–A.8** (Weyl eigenvalue monotonicity via Courant–Fischer,
  and the trace-exp monotonicity through the spectral mapping for `exp`),
  **A.9–A.11** (frustration-free Hamiltonians, energy-form
  kernels), **A.13–A.16** (angular-momentum quantization `J = n/2`, the ladder,
  and SU(2)-multiplet degeneracy), **A.17** (spin-0/half sector via the common
  eigenvector of commuting Hermitians), **A.18** (Perron–Frobenius for a real
  symmetric matrix, via the project's Collatz–Wielandt development and the
  variational `|w|`-argument), and **A.19–A.20** (polar + singular-value
  decompositions from the spectral theorem).
- **Documented axioms (faithful statements, deferred proofs)** — the
  operator-algebraic **A.21–A.28** (Wigner's
  theorem, states, Banach–Alaoglu, ground states of infinite systems, the GNS
  construction).

**Value judgment / policy.** The documented axioms above are kept as *faithful,
book-order statements* — they record exactly what Tasaki proves — but they are
**not active proof targets** of this project. They fall into two categories:

- **Operator-algebraic results** (Appendix A.21–A.28): the heavy functional-analytic and
operator-algebraic structures (states on the quasi-local C\*-algebra, weak-∗
compactness, ground states, GNS, Wigner) belong to a dedicated operator-algebra /
functional-analysis development; such a development may well be carried out
**separately** (for instance contributed to `mathlib`), and these axioms simply
**wait for that implementation**.

- **Perturbation-theoretic results** (e.g., **Lemma 10.1** (Tasaki §10.1, degenerate
perturbation theory) and singular-perturbation arguments in Chapter 10): the analytic
proofs of weak-coupling continuation and adiabatic following for eigenstate families
are **not undertaken** as an active project goal; such techniques naturally belong to
a separate analytic-perturbation development. **Theorem 10.4** (Lieb's repulsive-Hubbard
half-filling ground state) currently has its entire content axiomatized: the global minimum
energy, ground-state degeneracy, and total-spin values are all undischarged. (The fixed-Ŝ³-sector
ground-state uniqueness has been proved; full theorem discharge is tracked in Issue #5004.)

- **Book theorems that Tasaki states without proof** (results he quotes from the
external literature rather than proving in the text): **Theorem 10.11** (Kubo–Kishi
finite-temperature charge/pairing susceptibility bound, Tasaki §10.2.5, citing
Kubo–Kishi, *Phys. Rev. B* **41**, 4866 (1990)) and **Theorem 11.13** (Mielke's
flat-band ferromagnetism, `mielke_theorem_11_13`) are recorded as **faithful documented
axioms** on the concrete finite-volume operators (here the Duhamel susceptibilities),
matching the "Tasaki states it without proof" policy — the reproving of the cited
external work is not an active project goal.

Accordingly the project's policy is to **axiomatize only the appendix and
perturbation-theory results that Tasaki's formalized main development actually uses**,
to **prove** the remaining ones where `mathlib` provides the tools, and otherwise to
leave a faithful axiom in place rather than invest in large bespoke developments whose
natural home is elsewhere. The `#print axioms` of every theorem in the repository makes
the precise dependency on these documented axioms auditable.

<!-- legacy-source:end:155:216 -->

## Theorem 7.7 (hexagonal AKLT correlation decay and infinite-volume uniqueness)

**Tasaki §7.3.2, Theorem 7.7** (eqs. (7.3.6)–(7.3.9), pp. 210–212) is a **documented
axiom**, `tasaki_theorem_7_7` (`LatticeSystem/Quantum/SpinS/GeneralAKLT.lean`, doc
comment lines 130–174, declaration lines 175–183). This section records this
non-Appendix documented axiom alongside the Appendix A entries above.

- **Proved (axiom-free):** the finite honeycomb-torus VBS ground state exists and is
  zero-energy and frustration-free — `honeycombVBSState_isGeneralGraphVBSGroundState`
  (`LatticeSystem/Quantum/SpinS/HoneycombAKLTZeroEnergy.lean`, PR #5133, `#print axioms`
  = std3), for the canonical graph `honeycombTorusGraph m` with `m ≥ 2`.
- **What the axiom statement literally asserts:** two conjuncts, quantified as `∃ C ξ,
  0 < C ∧ 0 < ξ ∧ ∀ (hexagonal G), (…) ∧ (…)`:
  1. For every hexagonal lattice `G` (`IsHexagonalLatticeAKLT G`), *some* zero-energy VBS
     ground state `Φ` exists (`∃ Φ, IsGeneralGraphVBSGroundState G 3 Φ ∧ …`) whose spin
     correlation is sign-alternating and exponentially decaying with the single pair
     `C, ξ` uniform over all hexagon sizes (eq. (7.3.9)). The axiom does **not** assert
     that this ground state is the *only* one at finite volume — an existential `∃ Φ`,
     not a universal `∀ Φ`, is what is axiomatized (see below).
  2. `HasUniqueInfiniteVolumeVBSGroundState G 3` holds. This is itself a **separate
     uninterpreted marker axiom** (`axiom HasUniqueInfiniteVolumeVBSGroundState (G :
     SimpleGraph Λ) (N : ℕ) : Prop`, `GeneralAKLT.lean:128`) with no mathematical
     content of its own — it is an opaque `Prop`-valued declaration, not a proved
     predicate. There are currently zero consumers of `tasaki_theorem_7_7` in the
     repository; `#print axioms` on a hypothetical consumer would show the standard
     three (`std3` = `propext`, `Classical.choice`, `Quot.sound`) plus the two project
     axioms `HasUniqueInfiniteVolumeVBSGroundState` and `tasaki_theorem_7_7` itself —
     five names in total, one of which (`HasUniqueInfiniteVolumeVBSGroundState`)
     carries no formalized statement at all.
- **Not yet formalized (the *proof*, not the axiom's existential assertion):** per the
  catalogue's own language (`docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`,
  rows for `honeycombVBSState` and `honeycombVBSState_isGeneralGraphVBSGroundState`),
  finite-volume ground-state uniqueness, a spectral gap, and (for a general hexagon)
  the finite-volume analytic/KLT ingredients that would *prove* the correlation-decay
  bound all "remain unproved." The axiom statement itself does existentially assert the
  decay bound (see the first bullet above) — what is absent from the formalization is
  the underlying proof of that bound for a general hexagon, not the assertion, and the
  axiom does not assert uniqueness or a gap at finite volume at all.
- **Witness is not fixed to the transported canonical state:** the `∃ Φ` conjunct is
  satisfied by *any* `Φ` meeting the predicates — the axiom does not type-fix or
  require `Φ` to be the canonical VBS state `honeycombVBSState m` transported along the
  isomorphism `G ≃g honeycombTorusGraph m` supplied by `IsHexagonalLatticeAKLT G`. The
  *intended* mathematical witness is that transported canonical state (per the KLT
  analysis), and the parallel axiom-free theorem above proves the ground-state property
  only for the canonical state on the canonical torus itself — but this is not proved or
  required by the axiom statement for a general hexagon; it is only the informal
  motivation for why the existential is expected to be witnessable.
- **Axiom reason (documented):** the rigorous 2D honeycomb correlation-decay proof
  requires Kennedy–Lieb–Tasaki, *J. Stat. Phys.* **53**, 383–415 (1988),
  DOI [10.1007/BF01011563](https://doi.org/10.1007/BF01011563) ("KLT [41]"), which is a
  real implementation dependency with **no open-access or author-hosted copy found (as
  of 2026-08-16, via OpenAlex/Unpaywall/author-homepage checks; institutional/
  subscription access was not attempted, and general-search-engine lookup was not
  attempted either since it is bot-blocked in this environment)**: OpenAlex work
  `W2092140400` reports `oa_status = closed` with no repository fulltext; Unpaywall
  confirms `is_oa = false`; none of Kennedy, Lieb, or Tasaki self-host a copy (Kennedy's
  own publication page links only to a dead `springerlink.com` URL). Open-access status
  is time-varying and this claim should be re-checked, not assumed permanent.
- **Re-check condition:** the disposition would change if either (a) a legitimate copy
  of KLT [41] is obtained (e.g. via institutional library/Springer subscription access,
  since no confirmed open-access route exists) and a math-before-code transcription of
  its finite-volume uniqueness proof and its proof of eq. (7.3.9) is completed, or (b)
  an independent formalized proof of eq. (7.3.9) not relying on [41], should one become
  available.
- **Tracking:** Issue #5132 (Theorem 7.7 discharge status) — **closed as not planned**
  (2026-08-16); master tracker #4718 remains open. Reopen #5132 if either re-check
  condition above is met (KLT [41] obtained and transcribed, or an independent
  [41]-free proof of eq. (7.3.9) becomes available).
  Catalogue rows: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the
  `tasaki_theorem_7_7` declaration row (grouped detail record #767) and the two inline
  `honeycombVBSState` / `honeycombVBSState_isGeneralGraphVBSGroundState` rows (not
  grouped detail records) that state the "remain unproved" items cited above.
  Note: detail record #767 is a frozen baseline archival copy (whitespace-normalized
  exact parity per `scripts/check_docs_hierarchy.py` against `docs/index.md` at the
  tracked baseline commit `6519099`) and so still shows its original `(line 724, …)`
  citation, which was already stale even at the time the record was frozen; the actual
  declaration, `honeycombVBSState_isGeneralGraphVBSGroundState`, lives in
  `LatticeSystem/Quantum/SpinS/HoneycombAKLTZeroEnergy.lean`.

## Theorem 7.2 (AKLT infinite chain: unique ground state with a nonzero gap)

**Tasaki §7.1.3, Theorem 7.2** (p. 179) is a **documented axiom** carried by two
declarations in `LatticeSystem/Quantum/SpinS/AKLTInfiniteChain.lean`:
`IsAKLTChainDynamics` (doc comment lines 43–48, declaration line 49) and
`aklt_theorem_7_2` (doc comment lines 51–61, declaration lines 62–65).

- **Proved (axiom-free):** the finite-volume counterpart, Tasaki Theorem 7.1, is a
  theorem — `aklt_theorem_7_1` (`LatticeSystem/Quantum/SpinS/AKLTTheorem71.lean`, line
  49), recorded in the catalogue with the standard three axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Only the passage to the infinite chain is
  axiomatized.
- **What the axiom statement literally asserts:** for a one-dimensional
  `InfiniteSpinSystem 1 A` over a C*-algebra `A` and a dynamics `δ : A → A` satisfying
  the marker, there exists `ω : WeakDual ℂ A` with `IsState ω`, `IsGroundState ω δ`
  (Definition A.25: `0 ≤ ω (star a * δ a)` for all `a`), uniqueness among states
  (`∀ ω', IsState ω' → IsGroundState ω' δ → ω' = ω`), and `∃ γ, HasNonzeroGap ω δ γ`
  (Definition A.27, whose first conjunct is `0 < γ`). This is faithful to the book,
  which states the theorem in exactly the sense of Definitions A.25/A.27 and identifies
  the state with the `L↑∞` limit of the VBS state (7.1.12).
- **The dynamics marker has no mathematical content:** `IsAKLTChainDynamics S δ` is an
  uninterpreted Prop-valued axiom, following the same idiom as `IsLocalHamiltonianData`
  (`LatticeSystem/Math/CStarAlgebra/GroundState.lean`, line 52). It cannot be
  established for any concrete data, so the theorem is only usable under an assumed
  hypothesis; since the marker admits the interpretation "always false", the pair adds
  no inconsistency. There are currently zero consumers of either declaration in the
  repository, so no proved result depends on them.
- **Axiom reason (documented):** the statement is an assertion about the state space of
  the quasi-local C*-algebra of the spin-1 chain on ℤ — existence of a weak-* limit
  state, uniqueness quantified over all states (not merely translation-invariant ones),
  and a spectral-gap condition phrased through the derivation `δ = [Ĥ_AKLT, ·]`. Its
  proof (Matsui, *Commun. Math. Phys.* **189**, 127 (1997), strengthening
  Affleck–Kennedy–Lieb–Tasaki, *Commun. Math. Phys.* **115**, 477 (1988)) is carried
  out entirely in that operator-algebraic setting and is not reproduced by Tasaki, who
  states it without proof. Per the project's operator-algebra policy — the same one
  under which Appendix A.21–A.28 (states, Banach–Alaoglu, ground states of infinite
  systems, GNS) are recorded — such results are faithful documented axioms that wait
  for a dedicated operator-algebra development, whose natural home is a separate
  project or `mathlib`. This entry therefore creates no book-order discharge work item;
  the "prove theorems Tasaki cites without proof" rule does not override it, because
  its standing exception is exactly the genuine C*-algebra/GNS framework.
- **Re-check condition:** the disposition would change only when all three of the
  following exist in reviewed form in this repository (or are usable from `mathlib`):
  (a) a concrete construction of the quasi-local C*-algebra of the spin-1 chain on ℤ
  together with the AKLT interaction `Σ_x ĥ_x^{AKLT}`, so that `IsAKLTChainDynamics`
  can be replaced by a real definition of the dynamics `δ = [Ĥ_AKLT, ·]` instead of an
  opaque marker; (b) a state/weak-* layer able to construct the `L↑∞` limit of the
  finite-volume VBS states as a state on that algebra and to use Definitions A.25/A.27
  on it; and (c) a math-before-code transcription of Matsui's uniqueness-among-all-
  states argument (or of an independent proof of the same statement). Partial progress
  on (a) or (b) alone does not reopen this entry.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated
  discharge issue exists or is to be opened for Theorem 7.2 while the re-check
  condition above is unmet. Catalogue row:
  `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the
  `IsAKLTChainDynamics` / `aklt_theorem_7_2` row.

## Theorem 7.3 (stability of the AKLT gap under small local perturbations)

**Tasaki §7.1.1, Theorem 7.3** (eq. (7.1.4), p. 180) is a **documented axiom** carried
by two declarations in `LatticeSystem/Quantum/SpinS/AKLTStability.lean`:
`IsTranslationCovariant` (doc comment lines 38-42, declaration line 43) and
`aklt_theorem_7_3` (doc comment lines 86-102, declaration lines 103-111).

- **Proved (axiom-free):** the unperturbed finite-volume model is a theorem —
  Theorem 7.1, `aklt_theorem_7_1` (`LatticeSystem/Quantum/SpinS/AKLTTheorem71.lean`,
  line 49), recorded in the catalogue with the standard three axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Only the stability of that picture under an
  arbitrary small local perturbation is axiomatized. Every other ingredient of the
  Theorem 7.3 statement is a real definition, not an axiom:
  `perturbedAKLTHamiltonianS` (line 63), `IsAKLTPerturbation` (line 49),
  `connectedChainCorrelation` (line 71), `IsUniqueChainGroundState` (line 81),
  `IsLocalRangeR` (`LiebSchultzMattisGeneral.lean`, line 52), `IsPositiveSpectralGap`
  (`HaldaneConjecture.lean`, line 67), `manyBodyOperatorNormS`
  (`ManyBodyOperatorNorm.lean`, line 21) and `ringDist` (`RingDistance.lean`, line 19).
- **What the axiom statement literally asserts:** for every range r and bound v₀
  there is ε₀ > 0 such that for every |ε| < ε₀ there are ΔE, C, ξ > 0 — quantified
  outside ∀L and hence genuinely L-independent — such that for every L ≥ 3 and every
  family v with `IsAKLTPerturbation L r v₀ v` (each v x self-adjoint, r-local in the
  commutant sense, `manyBodyOperatorNormS (v x) ≤ v₀`, and translation covariant), the
  perturbed Hamiltonian Ĥ_ε = Ĥ_AKLT + ε Σ_x v̂_x has a unique ground state Φ at some
  energy E (`IsUniqueChainGroundState`), a spectral gap of at least ΔE (∃ gap,
  ΔE ≤ gap ∧ `IsPositiveSpectralGap`), and connected correlations bounded by
  C * exp(−`ringDist` L x y / ξ).
- **Faithfulness caveats (recorded, not hidden):** the printed statement says only
  that ΔE_ε > 0 is independent of L and that "correlation functions in the ground
  state decay exponentially". The Lean statement additionally makes C and ξ
  L-independent and uses the connected (truncated) correlation; the connected form is
  necessary (a symmetry-breaking perturbation can give nonzero one-point functions, so
  the raw ⟨Ŝ_x · Ŝ_y⟩ need not decay) and both are the standard content of Yarotsky's
  theorem, but neither is literally in the printed sentence and neither has been
  checked line by line against Yarotsky's paper in this repository. Conversely the
  Lean statement is weaker than the book in restricting to L ≥ 3 (excluding the
  degenerate one- and two-site rings, where the AKLT term is a single-bond Casimir
  polynomial and the ground state is not unique) and to the marker-gated hypothesis
  class below. Any future discharge must re-derive, not assume, the C/ξ uniformity.
- **The translation-covariance marker has no mathematical content:**
  `IsTranslationCovariant L v` is an uninterpreted Prop-valued axiom, the same idiom
  as `IsAKLTChainDynamics` (Theorem 7.2, above). It stands for v̂_x = T̂^x v̂_o (T̂†)^x;
  the repository does define a chain translation operator, `chainTranslationOp`
  (`LiebSchultzMattisOrthogonality.lean:40`, instantiated at `N := 2` it has exactly
  the type `ManyBodyOpS (Fin L) 2`), with supporting API
  (`chainTranslationOp_unitary`/`'`, `chainTranslation_conj_onSiteS`/`_mul`/`_spinSDot`,
  `chainTranslation_commute_hamiltonian`), but `AKLTStability.lean` does not import
  `LiebSchultzMattisOrthogonality.lean`, so `IsTranslationCovariant` is not wired to
  this existing operator. Keeping the marker as a hypothesis is deliberate, since
  dropping it would let the axiom
  speak about arbitrary bounded range-r families that need not be translates of one
  local operator. Because the marker cannot be established for any concrete data, the
  axiom is usable only under an assumed hypothesis, and since the marker admits the
  interpretation "always false" the pair adds no inconsistency. The declarations are
  used only within this module (`IsTranslationCovariant` gates the
  `translation_covariant` field of `IsAKLTPerturbation`, which `aklt_theorem_7_3`
  consumes as a hypothesis); no proved result outside this axiom pair depends on
  them.
- **Axiom reason (documented):** Tasaki states Theorem 7.3 without proof and
  attributes it to D. A. Yarotsky, *Ground states in relatively bounded quantum
  perturbations of classical lattice systems*, Commun. Math. Phys. **261**, 799-819
  (2006), arXiv:math-ph/0412040 (Tasaki reference [91]), noting that it "was proved by
  using a sophisticated version of the cluster expansion". That proof is rigorous
  perturbation theory: a convergent cluster/polymer expansion around a classical
  (diagonal) reference system for a relatively bounded quantum perturbation, whose
  combinatorial tree-graph bounds are what deliver convergence uniformly in the
  volume — and it is exactly this machinery, not any finite-dimensional
  linear-algebra argument, that yields both the L-uniform gap and the exponential
  clustering. The repository contains no such development: there is no
  polymer/cluster expansion and no uniform-in-L analyticity layer; the existing
  `chainTranslationOp` (see above) is not wired into `AKLTStability.lean`. Per the
  policy above, perturbation-theoretic
  results — the same class as Lemma 10.1 (degenerate perturbation theory) — are
  faithful documented axioms and are not active proof targets; this is a standing
  named exception, so the "prove theorems Tasaki cites without proof" rule does not
  override it, and this entry creates no book-order discharge work item. Source
  access is not the obstacle here: unlike KLT [41] (Theorem 7.7), Yarotsky's paper is
  openly available as arXiv:math-ph/0412040.
- **Re-check condition:** the disposition would change only when all three of the
  following exist in reviewed form in this repository (or are usable from mathlib):
  (a) a general, reviewed cluster/polymer-expansion (or equivalent
  quantum-perturbation) framework with volume-uniform convergence estimates, strong
  enough to prove gap stability rather than assume it; (b) wiring
  `IsTranslationCovariant` to the existing `chainTranslationOp`
  (`LiebSchultzMattisOrthogonality.lean`), replacing the opaque marker with the actual
  condition v̂_x = T̂^x v̂_o (T̂†)^x using that operator; and (c) a math-before-code
  transcription of Yarotsky's argument (from arXiv:math-ph/0412040) — or of the more
  general frustration-free stability theorem of S. Michalakis, J. P. Zwolak,
  *Stability of frustration-free Hamiltonians*, Commun. Math. Phys. **322**, 277-302
  (2013), arXiv:1109.1588 (Tasaki reference [57]), which Tasaki notes contains
  Theorem 7.3 as a special case. Partial progress on (b) alone — giving
  `IsTranslationCovariant` real content — does not reopen this entry, since the
  theorem itself would remain unproved.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated
  discharge issue exists or is to be opened for Theorem 7.3 while the re-check
  condition above is unmet; the #4485 cited in the proof guide is the closed
  Chapters 3-10 backfill issue, not a discharge tracker. Catalogue row:
  `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the
  `IsAKLTPerturbation` / `perturbedAKLTHamiltonianS` / `aklt_theorem_7_3` row (frozen
  archival record; not edited by this entry). That row, the `AKLTStability.lean`
  module header and the proof guide all label this result "§7.1.3"; the printed book
  places Theorems 7.1-7.3 in §7.1.1 ("The Hamiltonian and the Main Theorem",
  pp. 178-180), while §7.1.3 is "The Uniqueness of the Ground State" (p. 186). The
  section label used above is the book's.

## Theorem 8.1 (large-`D` phase of the anisotropic `S = 1` chain: `L`-uniform gap and clustering)

**Tasaki §8.1.1, Theorem 8.1** (p. 226; eqs. (8.1.1)-(8.1.3) span pp. 226-228) is a **documented axiom**, `tasaki_theorem_8_1` (`LatticeSystem/Quantum/SpinS/AnisotropicLargeD.lean`, doc comment lines 51-60, declaration lines 61-71). Unlike the Theorem 7.2 and 7.3 entries above, a single declaration is involved: there is no companion marker axiom, and this is the only axiom in the module.

- **What the axiom statement literally asserts:** `∃ D₀, 0 < D₀ ∧ ∀ D ≥ D₀, ∃ ΔE₀ C ξ, 0 < ΔE₀ ∧ 0 < C ∧ 0 < ξ ∧ ∀ L, Even L → 2 ≤ L → ∃ E Φ,` the anisotropic ring Hamiltonian `anisotropicChainHamiltonianS L D` has a unique ground state Φ at energy E (`IsUniqueChainGroundState`), a first excited level at least ΔE₀ above it (∃ gap, ΔE₀ ≤ gap ∧ `IsPositiveSpectralGap`; since `IsPositiveSpectralGap H gap` pins gap to be exactly E₁ − E₀ for the smallest eigenvalue E₁ strictly above the ground energy, this says the true gap ΔE(D) is ≥ ΔE₀), and raw two-point ground-state correlations |expectationRatioRe (Ŝ_x^(α) Ŝ_y^(α)) Φ| ≤ C · exp(−ringDist L x y / ξ) for all three α and all sites. ΔE₀, C, ξ may depend on D but are quantified outside ∀L, hence genuinely L-independent, matching the printed "which is a function independent of L". `expectationRatioRe` is the scale-invariant Rayleigh ratio, so Φ is not required to be unit-normalized.
- **Every ingredient other than the axiom is a real definition, not an axiom:** `anisotropicChainHamiltonianS` (`AnisotropicLargeD.lean`, line 47), `heisenbergHamiltonianS` (`HeisenbergCore.lean`, line 34), `ringCoupling` (`ShastryNoSSB.lean`, line 41), `spinSSiteOp3` (`MultiSite.lean`, line 45), `spinSSiteComponentS` (`SiteComponent.lean`, line 21), `IsUniqueChainGroundState` (`AKLTStability.lean`, line 81), `IsGroundEnergy` / `IsPositiveSpectralGap` (`HaldaneConjecture.lean`, lines 61 and 67), `expectationRatioRe` (`AndersonTower.lean`, line 67), `ringDist` (`RingDistance.lean`, line 19) and `ManyBodyOpS` (`MultiSiteCore.lean`, line 36).
- **Consumers:** within `LatticeSystem/`, the only occurrence of `tasaki_theorem_8_1` is its own declaration (`AnisotropicLargeD.lean:61`); so no proved result depends on it. The definition layer is not unconsumed, however: `anisotropicChainHamiltonianS` is used by `guWenHamiltonianS`, the §8.3 Gu-Wen Hamiltonian (8.3.4) (`LatticeSystem/Quantum/SpinS/SPTPhase.lean`, lines 53-54), and is named in the doc comment of the separate open-boundary definition `openAnisotropicChainHamiltonianS` (`LatticeSystem/Quantum/SpinS/AnisotropicEdgeStates.lean`, line 49; `openAnisotropicChainHamiltonianS` itself is declared at line 52, doc comment 48-51). Retiring the axiom later would therefore not disturb the definitions.
- **Faithfulness caveats (recorded, not hidden):**
  1. The printed theorem's fourth (final) sentence — "The ground state in the L ↑ ∞ limit is unique and accompanied by a gap" — has no counterpart in the Lean statement: every conjunct is finite-volume. In this respect the axiom is weaker than the book.
  2. The printed statement makes only ΔE₀(D) explicitly L-independent and says the correlation "decays exponentially in the distance |x − y|" without naming constants. The Lean statement additionally quantifies C and ξ outside ∀L. Volume-uniform decay constants are the standard output of a convergent large-D expansion, but this is not literally in the printed sentence and has not been checked line by line against [49] in this repository. Any future discharge must re-derive, not assume, the C/ξ uniformity. This is the same class of caveat recorded for Theorem 7.3 above.
  3. The uniqueness conjunct is not what the book attributes to the cluster expansion. Tasaki obtains the finite-volume uniqueness of Φ_GS (with Ŝ³_tot Φ_GS = 0) from his Theorem 2.4 (pp. 43-44, proved by Mattis and Nishimori), which covers (8.1.1) as the λ = 1, D ≥ 0 case on a connected bipartite lattice with |A| = |B|; the even periodic ring is such a lattice. The Lean axiom nevertheless bundles `IsUniqueChainGroundState` with the gap and decay conjuncts, so it axiomatizes strictly more than the book attributes to [49]. Nothing in the repository proves this conjunct independently: freshly re-verified within `LatticeSystem/`, `IsUniqueChainGroundState` occurs twelve times — its doc comment and definition (`AKLTStability.lean` lines 77 and 81), the Theorem 7.3 axiom (`AKLTStability.lean` lines 92 and 108), this axiom (`AnisotropicLargeD.lean` lines 55 and 66), a Theorem 8.2 energy-estimate hypothesis (`AnisotropicEdgeEnergy.lean` line 405), and — since Theorem 8.2 is now the proved theorem `tasaki_theorem_8_2`, not an axiom — its implementation's use of `IsUniqueChainGroundState` as a hypothesis: the ground-character helper `edgeGroundCharacter` (`AnisotropicEdgeStatesDischarge.lean` line 73), the single-volume bridge `tasaki_theorem_8_2_fixed_volume` (lines 118 and 128), and the public capstone `tasaki_theorem_8_2` itself (doc-comment mention line 255, hypothesis line 276) — none of which proves the conjunct: `tasaki_theorem_8_2` assumes `IsUniqueChainGroundState` as a premise rather than establishing it.
  4. The Lean statement uses the raw two-point function, matching the book's ⟨Φ_GS| Ŝ_x^(α) Ŝ_y^(α) |Φ_GS⟩ (Theorem 7.3, by contrast, uses the connected correlation). The module doc comment and the catalogue row remark that raw and connected coincide here because the disordered symmetric ground state has vanishing one-point functions; that remark is motivating physics — it is neither asserted by the axiom nor proved, and the book itself only expects the Néel order parameter (8.1.3) to vanish.
  5. 2 ≤ L is a Lean-side restriction absent from the printed hypothesis (which requires only that L be even, with periodic boundary); it excludes L = 0.
- **Axiom reason (documented):** Tasaki states Theorem 8.1 without proof, writing that it "is proved by applying standard methods of rigorous perturbation theory (based on a cluster expansion) for quantum spin systems", citing his reference [49] = T. Kennedy, H. Tasaki, *Hidden symmetry breaking and the Haldane phase in S = 1 quantum spin chains*, Commun. Math. Phys. **147**, 431-484 (1992). He adds that D₀ must be taken large for a rigorous proof ("we once estimated that D₀ = 28 is enough") while the large-D phase is expected to extend down to D_c ≈ 1 — the theorem's content is precisely the convergent large-D expansion regime, not a finite-dimensional linear-algebra statement. Mathematically the proof expands around the trivial diagonal Hamiltonian Ĥ_trivial = D Σ_x (Ŝ_x^(3))² of eq. (8.1.2), whose unique ground state ⊗_x |0⟩_x has gap exactly D, treating the Heisenberg term Σ_x Ŝ_x · Ŝ_(x+1) as a perturbation of relative size 1/D; convergence of the polymer/tree-graph expansion uniformly in the volume is what simultaneously yields the L-independent gap bound ΔE₀(D) and the exponentially decaying correlations with L-independent C, ξ. This is the same machinery as Theorem 7.3 (Yarotsky), here around a classical diagonal reference model. The repository contains no such development: no polymer/cluster-expansion framework and no uniform-in-L analyticity layer exist, and repository-wide the phrase "polymer" has zero hits in `LatticeSystem/`. The same absent-framework reasoning already governs two sibling documented axioms with the identical decay shape (`∃ ξ C, 0 < ξ ∧ 0 < C ∧ ∀ …, |corr| ≤ C * exp(-dist/ξ)`), `tasaki_4_22_exponential_clustering` and `tasaki_4_23_high_temperature_disorder` (`HeisenbergEquilibrium.lean`), which are an apposite existing precedent for deferring this conjunct the same way. Per the policy above, perturbation-theoretic results — the same standing named exception under which Lemma 10.1 (degenerate perturbation theory) and the Chapter 10 singular-perturbation arguments are recorded — are faithful documented axioms and are not active proof targets, so the "prove theorems Tasaki cites without proof" rule does not override this entry, and this entry creates no book-order discharge work item. Source access is not the recorded obstacle here (unlike KLT [41] for Theorem 7.7): the recorded reason is the absent perturbation-theory development.
- **Re-check condition:** the disposition would change only when all three of the following exist in reviewed form in this repository (or are usable from mathlib): (a) a general, reviewed cluster/polymer-expansion (or equivalent quantum-perturbation) framework with volume-uniform convergence estimates, strong enough to prove a spectral gap and exponential clustering at large D rather than assume them; (b) a math-before-code transcription of the large-D expansion for (8.1.1) — from Kennedy-Tasaki [49] or an equivalent source — that derives an explicit threshold D₀, an L-independent ΔE₀(D), and L-independent C and ξ; and (c) for the uniqueness conjunct specifically, a Lean proof of Tasaki Theorem 2.4 (pp. 43-44) applicable at S = 1 to (8.1.1) in the λ = 1, D ≥ 0 case on the even ring. The repository's Theorem 2.4 development reaches an unconditional closure for obligation (1) (`anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional`, `AnisotropicHeisenbergStructuralGeneralN.lean:36`, its `hJpos` hypothesis at line 40) and a general spin-S obligation-(2) wrapper (`AnisotropicHeisenbergSpinSMLMEndpoint.lean:62`, its `hJpos` hypothesis at line 65) that no longer needs the SU(2)-endpoint global-uniqueness callback (removed per `docs/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-03.md` row at line 62), but connecting either to (8.1.1) on the ring is not yet done; the list below records *at least* the following open gaps — it is not a claim of completeness, and no one item is asserted to be uniquely "the" obstruction:
  (i) both the obligation-(1) closure and the obligation-(2) wrapper require a complete-bipartite positivity premise `hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re`, and the obligation-(2) wrapper additionally requires a symmetry premise `hJ_sym : ∀ x y, J x y = J y x` (`AnisotropicHeisenbergSpinSMLMEndpoint.lean:68`); the repository's nearest-neighbour ring coupling `ringCoupling` (`ShastryNoSSB.lean:41`) is directed (`J x y = 1` iff `y = x + 1 mod L`, else `0`), so it fails `hJ_sym` for every L ≥ 3, and (minimally verified, not exhaustively checked for every L) fails `hJpos`'s completeness requirement already at small L such as L = 4, holding only in the degenerate L = 2 case;
  (ii) even granting a symmetric coupling, the known bridge from the symmetrized ring coupling to the (isotropic) Heisenberg chain Hamiltonian (`heisenbergHamiltonianS_ringCouplingSym_eq`, `LiebSchultzMattisRingUniqueness.lean:34-36`, which shows `heisenbergHamiltonianS (ringCouplingSym L) N = 2 • afmHeisenbergChainHamiltonianS L N`) has no established analogue for the anisotropic chain: `anisotropicChainHamiltonianS` (`AnisotropicLargeD.lean:47`) has no proved identity connecting it to `anisotropicHeisenbergS`, and its only other occurrences within `LatticeSystem/` are its use inside `guWenHamiltonianS` (`SPTPhase.lean:51`) and a doc-comment mention in `AnisotropicEdgeStates.lean:49`, neither of which supplies such a bridge;
  (iii) both the obligation-(1) closure and the obligation-(2) wrapper conclude an eigenspace-dimension bound (`finrank ℂ eigenspace ≤ 2` and `≤ 1` respectively, the latter via `hermitianMinEigenvalue`), not `IsUniqueChainGroundState` itself, so an additional predicate-transfer step from the finrank bound to `IsUniqueChainGroundState` would still be needed;
  (iv) separately, a connected-coupling route already exists, `tasaki_2_5_theorem_2_3_data_of_connected` (`ConnectedTheorem23.lean:208`), whose doc comment (line 199) records that it "drops the complete-bipartite `hJ_pos` premise", but it has not been wired through either the obligation-(1) closure or the obligation-(2) wrapper above.
  Closing condition (c) requires resolving all of the gaps above (or finding an alternative route not listed here); discharging any single one of (i)-(iv) does not by itself close condition (c), and partial progress on any single item does not reopen this entry, since the gap and decay conjuncts — precisely what the book attributes to [49] — would remain unproved regardless.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated discharge issue exists for Theorem 8.1, and none is to be opened while the re-check condition above is unmet; the #4485 cited in the proof guide's §8.1.1 paragraph is the closed "Backfill Tasaki Chapters 3-10 numbered items" issue, not a discharge tracker. Catalogue row: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the `anisotropicChainHamiltonianS` / `tasaki_theorem_8_1` row carrying the `tasaki-chapter-8-records` anchor (interim-authoritative archival record; not edited by this entry). The section label §8.1.1 and the pages recorded in the module header, the catalogue row and the proof guide are all correct against the printed book; unlike Theorem 7.3, this entry records no label defect.

## Theorem 8.3 (λ-D model: Néel order bounded by string order)

**Tasaki §8.2.1, Theorem 8.3** (eqs. (8.2.1)-(8.2.4), pp. 239-241) is carried by five declarations in `LatticeSystem/Quantum/SpinS/LambdaDModel.lean`. One is a real definition: `lambdaDChainHamiltonianS` (doc comment lines 42-46, declaration lines 47-50), the concrete λ-D Hamiltonian (8.2.1). The other four are documented axioms: `neelOrderParameterS` (doc comment lines 52-56, declaration line 57, an uninterpreted marker), `stringOrderParameterS` (doc comment lines 59-62, declaration line 63, an uninterpreted marker), `tasaki_theorem_8_3` itself (doc comment lines 65-72, declaration lines 73-74, eq. (8.2.4)), and `tasaki_neel_transverse_eq_nonneg` (doc comment lines 76-79, declaration lines 80-81, the footnote-14 companion statement).

- **What the axiom statement literally asserts:** for `lam D : ℝ`, `hlam : 0 ≤ lam`, and `α : Fin 3`, `tasaki_theorem_8_3` states `neelOrderParameterS lam D α ≤ stringOrderParameterS lam D α`. `neelOrderParameterS` and `stringOrderParameterS` are uninterpreted functions `ℝ → ℝ → Fin 3 → ℝ` — the thermodynamic double limits (8.2.2)-(8.2.3) defining them are not formalized, so they are recorded as opaque real-valued markers rather than computed quantities. The companion `tasaki_neel_transverse_eq_nonneg` states, for `lam D : ℝ` and `0 ≤ lam`, `neelOrderParameterS lam D 0 = neelOrderParameterS lam D 1 ∧ 0 ≤ neelOrderParameterS lam D 0` (footnote 14, p. 240).
- **Faithfulness caveat (recorded, not hidden): missing absolute value.** The printed inequality (8.2.4) is `|O_Néel^(α)(Φ_GS)| ≤ O_string^(α)(Φ_GS)` — with an absolute value on the Néel side (re-verified directly against the rendered book page, p. 240; `pdftotext` extraction of this book is known to drop math symbols such as radicals, so the `.txt` transcript alone cannot be trusted to confirm or refute the presence of `|·|` here). The Lean statement `neelOrderParameterS lam D α ≤ stringOrderParameterS lam D α` has **no absolute value**, so as written it is **strictly weaker** than the book: it bounds the Néel parameter's signed value from above, not its magnitude. This entry records the gap rather than leaving it unremarked.
- **Consumers:** freshly re-verified (`grep -rn` over `LatticeSystem/`): within `LatticeSystem/`, all four names occur only inside `LambdaDModel.lean` itself — `neelOrderParameterS` (declared at line 57, also used in the other axioms' statements at lines 74 and 81), `stringOrderParameterS` (declared at line 63, also used at line 74), `tasaki_theorem_8_3` (line 73), and `tasaki_neel_transverse_eq_nonneg` (line 80) — there is no consumer outside this module. (Repository-wide: three of the four names — `neelOrderParameterS`, `stringOrderParameterS`, `tasaki_theorem_8_3` — also appear as `\texttt{}` names in `tex/proof-guide.tex`; `tasaki_neel_transverse_eq_nonneg` is referenced there only by prose ("A separate axiom records the footnote..."), not by name. All four names also appear in the legacy catalogue `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md` and this ledger entry itself, none of which are Lean consumers.)
- **No representation of the λ-D model's specific order-parameter path-integral exists in this repository:** the proof Tasaki cites uses the path-integral representation of §6.3 to compare the Néel and string order parameters, i.e. a positive quantum-to-classical mapping for this specific comparison. General Trotter/Lie-product infrastructure does exist and is proved axiom-free — `trotterProductFormula`/`lieProductFormula` (`LatticeSystem/Math/MatrixAnalysis/LieProduct.lean`, Appendix A.1 above) — and the repository's Dyson–Lieb–Simon reflection-positivity development (`RingReflection*.lean`, `LatticeSystem/Quantum/SpinS/`) genuinely builds a Trotter-based positive quantum-to-classical assembly on top of it (`RingReflectionGibbsCapstone.lean` invokes `lieProductFormula` directly to construct a reflection-positive trace weight from an RP-decomposed Gibbs weight). But this DLS machinery represents the Gibbs weight of an already reflection-positive Hamiltonian decomposition; it does not supply the specific loop/path-integral representation of §6.3 that Tasaki's proof of (8.2.4) uses to compare `O_Néel` and `O_string`. The repository's existing §6.3 development, `tasaki_prop_6_5_hhaf_spin_one` (`LatticeSystem/Quantum/SpinS/HiddenAntiferromagneticOrderUniqueness.lean`), is a Perron-Frobenius / kink-path argument on the restricted `H_HAF` subspace, also not a path-integral representation. Neither existing piece of machinery supplies what (8.2.4)'s proof needs.
- **Axiom reason (documented):** Tasaki states Theorem 8.3 without proof: "See [49] for the proof (which makes use of the path integral representation as in Sect. 6.3), and [47] for an extension." (p. 240, re-verified against the rendered page), where [49] = T. Kennedy, H. Tasaki, *Hidden symmetry breaking and the Haldane phase in S = 1 quantum spin chains*, Commun. Math. Phys. **147**, 431-484 (1992) (verified against Tasaki (2020), Chapter 8 bibliography, entry [49], which prints a link to `https://projecteuclid.org/euclid.cmp/1104250747`), and [47] = T. Kennedy, *Non-positive matrix elements for Hamiltonians of spin-1 chains*, J. Phys.: Condens. Matter **6**, 8015-8022 (1994) (Tasaki (2020), Chapter 8 bibliography, entry [47]). Unlike KLT [41] for Theorem 7.7, [49] is **not recorded as inaccessible**: Tasaki's own bibliography prints a link for it, so the correct framing is that [49] has **not yet been transcribed** into this repository as a math-before-code note — not that it is unavailable. Separately, [48] and [49] are cited **jointly** — not [48] alone — at multiple points elsewhere in the chapter (e.g. pp. 239 and 241), none of which is Tasaki's cited proof source for (8.2.4) itself: for instance at p. 239 (re-verified against the rendered page) for the general 1992 Kennedy-Tasaki argument that the three Haldane-phase phenomena "can be naturally understood as a consequence of hidden Z2 × Z2 symmetry breaking [48, 49]"; and at p. 241, §8.2.2 (re-verified against the rendered page), for introducing the actual nonlocal unitary transformation (eq. (8.2.5)) itself — "The unitary transformation was introduced by Kennedy and Tasaki [48, 49] ... It is sometimes called the **Kennedy–Tasaki transformation**" (not "Kennedy–Takayama": "Takayama" does not co-author either [48] or [49] and appears in the book's bibliography only as a co-author of the unrelated reference [56]).
  This entry belongs to the same **"Tasaki states without proof"** policy class as Theorem 10.11 and Theorem 11.13 above, not to a separate or new exception: Tasaki cites external work ([49], and [47] for an extension) for the proof of (8.2.4) rather than proving it himself, and the primary, policy-grounded reasons for deferral are (i) no path-integral / positive quantum-to-classical representation infrastructure exists in this repository for this specific comparison (established above), and (ii) Kennedy-Tasaki [49]'s proof has not been transcribed into a math-before-code note here. Footnote 13 (p. 239, re-verified against the rendered page) is a genuine additional wrinkle — it reads "To be rigorous the existence of the limits in (8.2.2) and (8.2.3) are not proved in general" — but it does not make the theorem's premises unstatable: this repository has direct precedent (Prop 4.10) for discharging a result whose underlying claim could not be proved unconditionally by instead recording it as a *conditional* theorem with an explicit hypothesis, rather than leaving it an axiom. Accordingly the footnote-13 gap is recorded below as a caveat to be addressed if and when a transcription of [49] is attempted, not as a hard prerequisite that blocks discharge indefinitely.
- **Re-check condition:** the disposition would change when both of the following exist in reviewed form in this repository: (a) a rigorous path-integral / positive quantum-to-classical representation framework applicable to the λ-D model (or an alternative proof route not relying on one); and (b) a math-before-code transcription of Kennedy-Tasaki [49] (or an equivalent independent proof of (8.2.4) and the footnote-14 companion statement). Partial progress on (a) or (b) alone does not reopen this entry. **Note (footnote-13 caveat):** if a transcription of [49] is attempted, the existence of the limits (8.2.2)-(8.2.3) is not proved in general (footnote 13), so the transcription will likely need to either prove existence under the repository's hypotheses or take existence as an explicit hypothesis (per the Prop 4.10 precedent) rather than as a literal unconditional limit.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated discharge issue exists for Theorem 8.3, and none is to be opened while the re-check condition above is unmet. Catalogue row: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, row at line 37 (`lambdaDChainHamiltonianS` / `tasaki_theorem_8_3`). This row's **AXIOM** label is accurate as currently printed; no status transition or `approved_changes()` entry is needed, so this entry proposes no catalogue edit.
  Three ancillary defects are recorded here for a future bundled fix; none is yet corrected:
  (i) `LambdaDModel.lean`'s own module doc comment (lines 33-35) cites "T. Kennedy, H. Tasaki, Phys. Rev. B **45**, 304 (1992)" — i.e. [48] — as its reference for Theorem 8.3, where the book's actual proof citation is [49] (Commun. Math. Phys. **147**, 431-484 (1992)); the module doc comment should be corrected to cite [49] (and may retain [48] separately for the KT transformation, which this file does not itself formalize).
  (ii) `LatticeSystem/Quantum/SpinS/HiddenAntiferromagneticOrder.lean` is internally inconsistent about the status of Proposition 6.5: its module doc comment (lines 39-40) still describes Proposition 6.5 as "recorded as a documented axiom", but the file's own trailing comment (lines 1042-1046) correctly states "This was formerly a documented axiom; it is now **proved** as `tasaki_prop_6_5_hhaf_spin_one` in the companion module `Quantum/SpinS/HiddenAntiferromagneticOrderUniqueness.lean`" (confirmed: `tasaki_prop_6_5_hhaf_spin_one` is a theorem at `HiddenAntiferromagneticOrderUniqueness.lean:1110`). Proposition 6.5 has no entry in this ledger, so this is a stale in-source doc comment, not a ledger correction; worth fixing separately.
  (iii) the missing-absolute-value gap recorded above (`tasaki_theorem_8_3` lacks the `|·|` that (8.2.4) has on the Néel side): since `tasaki_theorem_8_3` is currently an axiom rather than a proved theorem, correcting its *statement* to match (8.2.4) exactly requires no new infrastructure — it is declaring a different (stronger, more faithful) axiom, not proving anything. This is logically independent of the re-check condition (a)-(b) above, which gates *proving* the theorem, not restating it; a small `.lean`-only follow-up could close gap (iii) on its own without needing (a)-(b).

## Eq. (8.3.3) (Oshikawa: parity dependence of the spin-`S` VBS string order)

**Tasaki §8.3.1, eq. (8.3.3)** (p. 252) is a **documented axiom** carried by two declarations in `LatticeSystem/Quantum/SpinS/SPTPhase.lean`: `vbsStringOrderParameterS` (doc comment lines 56-58, declaration line 59, an uninterpreted marker) and `tasaki_oshikawa_8_3_3` (doc comment lines 61-66, declaration lines 67-68). Unlike Theorem 8.3 above, this is not a numbered theorem of the book but a displayed equation Tasaki reports from the literature.

- **What the axiom statement literally asserts:** for `S : ℕ` and `α : Fin 3`, `tasaki_oshikawa_8_3_3` states `(Odd S → 0 < vbsStringOrderParameterS S α) ∧ (Even S → vbsStringOrderParameterS S α = 0)`. `vbsStringOrderParameterS : ℕ → Fin 3 → ℝ` is itself an axiom — an uninterpreted function symbol, not a defined quantity; the thermodynamic double limit that would define `O_string^{(α)}(Φ_VBS^S)` is not formalized. This matches the printed display, which reads `O_string^{(α)}(Φ_VBS^S) { > 0 if S = 1, 3, 5, …; = 0 if S = 2, 4, 6, … }` (re-verified directly against the rendered book page, p. 252, not from the `pdftotext` transcript — that transcript is known to drop math symbols, so it alone could not settle whether the display carries a decoration such as the `|·|` that Theorem 8.3's (8.2.4) does; the rendered page shows **no** absolute value here, so unlike Theorem 8.3 this entry records **no** missing-`|·|` gap).
- **The pair has no mathematical content (self-satisfiable):** because the carrier is an opaque function symbol rather than a computed quantity, the pair `vbsStringOrderParameterS` + `tasaki_oshikawa_8_3_3` is satisfied by the interpretation `fun S _ => if Odd S then 1 else 0` (`Odd` and `Even` are mutually exclusive on `ℕ`), so it adds no inconsistency — and, dually, it proves nothing whatsoever about any concrete VBS state, string operator or correlation function in this repository. What the axiom records is the *bookkeeping* of (8.3.3), not a statement about `akltVBSState` / `stringCorrelationAxisS`. This is the same idiom as the `neelOrderParameterS` / `stringOrderParameterS` markers of Theorem 8.3 above.
- **Faithfulness caveat (recorded, not hidden): over-quantification to `S = 0`.** The printed display enumerates `S = 1, 3, 5, …` and `S = 2, 4, 6, …`, i.e. integer spins `S ≥ 1`. The Lean statement quantifies over all `S : ℕ`, so at `S = 0` its even branch additionally asserts `vbsStringOrderParameterS 0 α = 0`. This is not derivable from anything and is not refutable either (the marker is opaque), and it is at least not obviously false — the `S = 0` chain has vanishing spin operators — but it is not part of the printed statement. Any future discharge must either restrict to `1 ≤ S` or re-derive the `S = 0` case rather than inherit it.
- **Consumers:** freshly re-verified (`grep -rn` over `LatticeSystem/`): `vbsStringOrderParameterS` occurs only inside `SPTPhase.lean` (its doc comment line 56, its declaration line 59, and the axiom statement at line 68) and `tasaki_oshikawa_8_3_3` only at its own declaration (line 67). No proved result depends on either. (Repository-wide, `tasaki_oshikawa_8_3_3` occurs outside `SPTPhase.lean` in the legacy catalogue `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, in `tex/proof-guide.tex` (once, as a `\texttt{}` name in prose) and in this ledger entry — none of which is a Lean consumer. `vbsStringOrderParameterS` occurs outside `SPTPhase.lean` and this entry in exactly one other place: `tex/proof-guide.tex:12701` names it once, in prose, as a `\texttt{}` reference — likewise not a Lean consumer.)
- **Axiom reason (documented):** Tasaki states (8.3.3) without proof, attributing it to M. Oshikawa, *Hidden Z₂ × Z₂ symmetry in quantum spin chains with arbitrary integer spin*, J. Phys.: Condens. Matter **4**, 7469 (1992) (Tasaki (2020), Chapter 8 bibliography, entry [78]): "The problems of hidden antiferromagnetic order and related hidden Z₂ × Z₂ symmetry breaking for the VBS state with a general integer spin `S` were systematically studied by Oshikawa [78]… But, rather surprisingly, the hidden antiferromagnetic order was found to depend on `S` as (8.3.3)" (p. 252, re-verified against the rendered page). Footnote 24 (p. 252, likewise re-verified) records that the (8.2.5) definition of `Û_KT` — itself due to Oshikawa [78] — extends to general `S`, whereas the original definition in [48, 49] covered `S = 1` only. This entry therefore belongs to the same **"Tasaki states without proof"** policy class as Theorem 8.3, Theorem 10.11 and Theorem 11.13 above.
  **The obstacle here is different in kind from Theorem 8.1 and Theorem 8.3, and is recorded as such:** it is *not* an absent framework. The repository already contains the `S = 1` matrix-product / transfer-matrix machinery that computes exactly this quantity, and uses it to prove the `S = 1` (odd) instance of (8.3.3) axiom-free: `aklt_string_order_7_2_8` (`LatticeSystem/Quantum/SpinS/AKLTStringOrder.lean`, line 20; `#print axioms` freshly re-verified = `propext`, `Classical.choice`, `Quot.sound`) establishes, in the ε-form of the double limit `|x − y| ↑ ∞` after `L ↑ ∞`, that the periodic spin-one AKLT VBS state has den Nijs-Rommelse string order `4/9` in every axis `α` — in particular `> 0`, which is the odd-`S` branch of (8.3.3) at `S = 1`. What is missing is only the **general-`S` extension of that same machinery**: `akltVBSState` (`AKLTStringOrderDefs.lean`, line 36) is hard-wired to the three `2 × 2` spin-one matrices `akltVBSMatrices` (declaration line 27, entries lines 28-32), `stringOperatorS` (line 47) to the spin-one string phase `spinSStringPhaseS1` (line 41), and every object involved is typed at `ManyBodyOpS (Fin L) 2` / `Fin L → Fin 3`. Repository-wide there is no general-`S` VBS matrix-product state and no general-`S` string operator. The transfer-matrix layer is the one exception and is recorded precisely here: a **general-`N` MPS transfer matrix does exist** — `mpsTransferMatrix (A : MPSMatrices D N) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ` (`LatticeSystem/Quantum/SpinS/MPSTheorem75Defs.lean`, declaration line 28, doc comment line 27, Tasaki eq. (7.2.42)), whose argument type `MPSMatrices D N` (line 24) is documented as the matrices `(A^σ)_{σ = 0,…,N}` of bond dimension `D` "for a spin-`S` site (`N = 2S`)" (doc comment lines 22-23). What is `S = 1`-specialized is the **string-decorated** transfer machinery — the transfer matrices carrying the string-order phase insertions — namely the private `weightedTransfer` (`AKLTStringOrderTransfer.lean`, line 18) and its three instances `ordinaryTransfer` (line 23), `endpointTransfer` (line 28, the `Ŝ³` endpoint insertion) and `phaseTransfer` (line 33, the interior `exp(iπŜ³)` insertion), all hard-wired to the spin-one label type `Fin 3`, to `akltVBSMatrices` and to the `Fin 2 × Fin 2` doubled bond space. So the missing piece at the transfer-matrix layer is the general-`S` *string-decorated* evaluation, not a general-`S` transfer matrix as such. The deferral is therefore of the "waiting for a general-`S` extension of existing, working machinery" kind, not of the "no such development exists here" kind recorded for Theorem 8.1/7.3 (cluster expansion) or Theorem 8.3 (path-integral representation).
- **Re-check condition:** the disposition would change when all of the following exist in reviewed form in this repository: (a) a general-`S` VBS matrix-product state generalizing `akltVBSState` off the fixed `akltVBSMatrices`; (b) a general-`S` string operator and string correlation generalizing `stringOperatorAxisS` / `stringCorrelationAxisS` (`AKLTStringOrderDefs.lean`, lines 63 and 72) off the `S = 1` phase `spinSStringPhaseS1`; and (c) a general-`S` *string-decorated* transfer-matrix evaluation of the resulting double limit — generalizing the private `weightedTransfer` family above, the plain MPS transfer matrix `mpsTransferMatrix` being already general-`N` — together with a math-before-code transcription of Oshikawa [78], sufficient to replace `vbsStringOrderParameterS` with a real definition and to prove both branches of (8.3.3). Partial progress on any single item does not reopen this entry. **Note (limit-existence caveat):** as with Theorem 8.3's footnote-13 caveat, the existence of the defining double limit is not proved in general, so a transcription will likely need either to prove existence in the VBS case (as `aklt_string_order_7_2_8` does at `S = 1`) or to take it as an explicit hypothesis, per the Prop 4.10 precedent.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated discharge issue exists for eq. (8.3.3), and none is to be opened while the re-check condition above is unmet. Catalogue row: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the `guWenHamiltonianS` / `IsSPTPhase` / `tasaki_oshikawa_8_3_3` row. The sibling §8.3.1 pair in the same module, `vbsOpenChainGroundDegeneracyS` / `tasaki_vbs_edge_degeneracy` (`SPTPhase.lean`, lines 72 and 77, the `(S+1)²` open-chain edge degeneracy), is **not** covered by this entry and has no ledger entry yet.

## §8.3.2 SPT-phase markers (`IsShortRangeGappedUniqueGS`, `IsProductStateHamiltonian`)

**Tasaki §8.3.2** (pp. 254-256) contributes two **documented axioms** in `LatticeSystem/Quantum/SpinS/SPTPhase.lean`: `IsShortRangeGappedUniqueGS` (doc comment lines 79-84, declaration line 85) and `IsProductStateHamiltonian` (doc comment lines 87-88, declaration line 89). Unlike every entry above, these do not stand in for a *theorem*: §8.3.2 is a definitional section (what it means for two Hamiltonians to be continuously connected, and what the trivial and the nontrivial SPT phases are), and these two markers are the fixed-`L` stand-ins for the two infinite-volume notions the definition rests on.

- **What the axioms literally assert:** nothing. Each is an uninterpreted `Prop`-valued function of `H : ManyBodyOpS (Fin L) 2` at a fixed `L`, with no defining equation and no axiom constraining it. Consequently neither can be established for any concrete Hamiltonian, and neither can be refuted: both admit the interpretation "always false" (and "always true"), so the pair adds no inconsistency and no proved result can depend on them for content.
- **Everything built on the markers is a real definition, not an axiom:** `HamiltonianPath` (structure, line 94), `ContinuouslyConnected` (line 105), `SymmetryConnected` (line 111), `IsTrivialPhase` (line 119) and `IsSPTPhase` (line 126) are `def`s/`structure`s, as the module doc comment states explicitly ("the SPT-phase notions … are honest `def`s (never axioms — the SPT phase is a definition, not a theorem)"). The axiomatization is confined to the two markers, and to them the definitions delegate all the deep content: `HamiltonianPath.gapped_unique` (line 100) requires `IsShortRangeGappedUniqueGS` along the path, `IsTrivialPhase` (line 120) requires a product-state endpoint via `IsProductStateHamiltonian`, and `IsSPTPhase` (line 127) requires `IsShortRangeGappedUniqueGS H`.
- **Axiom reason (documented) — the classification is infinite-volume by the book's own statement:** Tasaki defines continuous connection for short-ranged chain Hamiltonians with a unique gapped ground state and then says, in the same paragraph (p. 254, re-verified directly against the rendered book page): "Since we are interested in classifying bulk properties of the ground states, the above process should be done in a suitably defined system on the infinite chain." The claim that gives the classification its content — that without imposed symmetry *all* short-ranged 1D Hamiltonians with a unique gapped ground state are continuously connected, rigorously established within matrix product states by Ogata (Tasaki (2020) Chapter 8 bibliography, entries [72]-[74]: Y. Ogata, *A class of asymmetric gapped Hamiltonians on quantum spin chains and its characterization I/II/III*, Commun. Math. Phys. **348**, 847-895 and 897-957 (2016), **352**, 1205-1263 (2017)) — is likewise a statement about the infinite chain. At a fixed finite `L` the two notions lose exactly this content: "short-ranged" is vacuous (every operator on `Fin L` is trivially a sum of terms of range `≤ L`), and "unique ground state with a nonvanishing gap" becomes an ordinary finite-dimensional spectral condition with no volume-uniformity. A faithful fixed-`L` reading would therefore leave essentially any two gapped-unique Hamiltonians symmetry-connectable and `IsSPTPhase` uninhabited — the classification would collapse to a triviality instead of reproducing the book's. **This collapse is the recorded design reason for keeping the markers opaque; it is not itself formalized here** (no Lean proof that `IsSPTPhase` is empty at fixed `L` is claimed or asserted). Per the project's policy the deferral class is the operator-algebra / infinite-volume boundary — the same class as Appendix A.21-A.28 and Theorem 7.2 above. Note that infinite/thermodynamic-limit systems are explicitly **in** scope as a long-term project goal, so this is not an "out of scope" marker: what is absent is the quantum quasi-local C\*-algebra layer for the spin chain. The repository's existing infinite-volume development stops short of supplying it: `InfiniteSpinSystem` carries its local algebra as a *free* field and `QuasiLocalRealization` (`LatticeSystem/Quantum/SpinS/QuasiLocalRealization.lean`, line 40) bundles the inductive-limit identification as **hypotheses** (`BoxTowerExhaustsLocalAlg`, `BoxTowerClosureIsQuasiLocalAlgebra`) rather than constructing it, and nothing there provides infinite-volume gapped uniqueness or a phase-connection relation.
- **Faithfulness caveat (recorded, not hidden): the ground state's continuity along the path is not required.** The printed definition asks for a family `Ĥ_s` that "depends continuously on `s` … and has a unique ground state (which is also required to depend continuously on `s`) with a nonvanishing energy gap for any `s`" (p. 254, re-verified against the rendered page). `HamiltonianPath` requires only `Continuous toFun` (field `continuous_toFun`, line 98, a condition on the Hamiltonian) together with the pointwise marker `IsShortRangeGappedUniqueGS (toFun s)` on `[0,1]`; the parenthesized continuity of the *ground state* in `s` has no counterpart. The Lean connection relation is therefore weaker than the book's, which makes `ContinuouslyConnected` / `SymmetryConnected` / `IsTrivialPhase` easier to satisfy and `IsSPTPhase` correspondingly *stronger* (rarer) than the book's notion. Adding the missing conjunct is one of the choices to be made at re-check time, not a defect that can be repaired while the ground state itself is only reachable through an opaque marker.
- **Consumers:** freshly re-verified (`grep -rn` over `LatticeSystem/`): both names occur only inside `SPTPhase.lean` (`IsShortRangeGappedUniqueGS` at lines 79, 85, 100 and 127; `IsProductStateHamiltonian` at lines 87, 89 and 120), plus two cross-reference mentions of `IsShortRangeGappedUniqueGS` inside doc comments in `LiebSchultzMattisDiscrete.lean` (lines 43 and 68) that record the deliberate scope split from the general-`N` markers `HasShortRangeHamiltonianS` / `HasUniqueGappedGroundStateS`. No proved result depends on either marker. (`tex/proof-guide.tex` mentions each name twice — `IsShortRangeGappedUniqueGS` at lines 12694 and 12702, `IsProductStateHamiltonian` at lines 12697 and 12702 — in prose; neither is a Lean consumer.)
- **Re-check condition:** the disposition would change only when all three of the following exist in reviewed form in this repository (or are usable from `mathlib`): (a) a constructed quasi-local C\*-algebra of the spin chain on `ℤ` — i.e. the inductive limit currently taken as a `QuasiLocalRealization` hypothesis discharged into an actual construction; (b) an infinite-chain notion of "short-ranged Hamiltonian with a unique gapped ground state" definable on it (Definitions A.25/A.27 style), so that `IsShortRangeGappedUniqueGS` and `IsProductStateHamiltonian` can be replaced by real definitions rather than opaque markers; and (c) a decision, recorded at that point, on whether to carry the book's ground-state-continuity conjunct in `HamiltonianPath`. Partial progress on (a) alone does not reopen this entry, since the phase classification would remain unstatable.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated discharge issue exists for the §8.3.2 markers, and none is to be opened while the re-check condition above is unmet. Catalogue row: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the `guWenHamiltonianS` / `IsSPTPhase` / `tasaki_oshikawa_8_3_3` row.

## §8.3.3 entanglement-entropy marker (`entanglementEntropyS`)

**Tasaki §8.3.3** (`S_LR = −Σ_j p_j log p_j`, defined just after eqs. (8.3.7)-(8.3.8), p. 262) contributes one **documented axiom**, `entanglementEntropyS` (`LatticeSystem/Quantum/SpinS/SPTTopologicalIndex.lean`, doc comment lines 88-91, declaration line 92). This is a contentless marker, not a deferred theorem: no book theorem in this repository depends on it.

- **What the axiom literally asserts:** nothing. `entanglementEntropyS {L N : ℕ} : ((Fin L → Fin (N + 1)) → ℂ) → ℝ` is an uninterpreted function symbol attaching a real number to each chain wave function, with no defining equation and no axiom constraining it. No property of it is derivable; it is a pure name.
- **What the book's quantity is, and why the finite version would not be it:** Tasaki's `S_LR` is the von Neumann entropy of the Schmidt weights `p_j` of the **half-infinite**-chain bipartition of the infinite-chain ground state (8.3.7)-(8.3.8): "The corresponding entanglement entropy of the ground state `|Φ_GS⟩` is defined by `S_LR := −Σ_j p_j log p_j`" (p. 262, re-verified directly against the rendered book page). He introduces the whole discussion as heuristic: "Let us heuristically discuss the basic idea behind the 'topological' indices of Pollmann, Turner, Berg, and Oshikawa's. We formally consider a spin system and its ground state on the infinite chain `ℤ`." (p. 261, likewise re-verified), adding two sentences later that the illustrative `S = 1` VBS example is taken "without being mathematically careful". The precise versions are deferred to §8.3.4 (matrix product states) and §8.3.6 (Ogata's rigorous infinite-chain indices). A **finite-`L`** bipartite entanglement entropy, by contrast, *is* definable with machinery already present: reshape the coefficient tensor of `(Fin L → Fin (N+1)) → ℂ` across a cut into a rectangular matrix, take its singular values (the repository proves the singular-value decomposition axiom-free — `matrix_singular_value_decomposition`, `LatticeSystem/Math/MatrixAnalysis/Decomposition.lean`, line 46, Tasaki Theorem A.20), normalize their squares to Schmidt weights and form `−Σ_j p_j log p_j`. But that object is **not** the printed quantity: the printed one is a half-infinite-chain Schmidt decomposition on `ℤ`. Attaching a finite-`L` definition to this name would therefore silently change what the §8.3.3 marker refers to rather than discharge it.
- **Consumers:** freshly re-verified (`grep -rn` over `LatticeSystem/`): `entanglementEntropyS` occurs only at its own declaration (`SPTTopologicalIndex.lean`, line 92) and in that module's header doc comment (line 26). There are **zero** consumers: no definition, theorem or axiom anywhere in the repository mentions it, the module header being prose only. (`tex/proof-guide.tex` mentions the name once in prose and the legacy catalogue row lists it; neither is a Lean consumer.)
- **The book does argue with `S_LR`, but nothing here does:** on the same page (p. 262, re-verified) Tasaki uses Kramers degeneracy to conclude that each Schmidt multiplicity `|J(p)|` is even, hence `S_LR ≥ log 2` for a time-reversal-invariant ground state whose effective half-chain states carry half-odd-integer spin, with equality `p₁ = p₂ = 1/2`, `S_LR = log 2` for the VBS state (8.3.6) — "'entanglement imposed by symmetry' is a definite sign that the state is in a nontrivial SPT phase". None of this is formalized here: the marker carries no such inequality and no declaration states one. So the entry records an unused name, not a deferred proof of the `log 2` bound.
- **Axiom reason (documented):** the class here is the project's "definition with no content" defer class — an uninterpreted marker standing for a quantity the book itself introduces only heuristically, and which no declaration in this repository uses. It is not deferred because a proof is hard: as declared, there is no statement to prove. The genuine infinite-chain construction (half-infinite-chain Schmidt decomposition, reduced density matrix, von Neumann entropy) belongs to the operator-algebra layer, the same class as Theorem 7.2 and the §8.3.2 markers above.
- **Re-check condition:** revisit when a book-order result that actually *uses* this quantity reaches the frontier — that is §8.3.4 ("Topological" indices for matrix product states, p. 264) or §8.3.6 (Ogata's rigorous infinite-chain indices), where the entropy and the entanglement spectrum acquire content; the `S_LR ≥ log 2` argument above is the first candidate consumer, and it needs the half-infinite-chain layer, not merely a definition of the entropy. At that point the choice to be recorded is between (i) a genuine half-infinite-chain construction on the quasi-local algebra (blocked by the same missing layer as the §8.3.2 markers) and (ii) a finite-`L` bipartition entropy built from the SVD above and used only in statements phrased at finite `L` — in which case it should be given a *different*, finite-`L` name rather than silently redefining this one. Until such a consumer exists, the marker should be neither defined nor relied on; if §8.3.4/§8.3.6 are formalized without needing it, deleting it is the appropriate resolution rather than defining it.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated discharge issue exists for `entanglementEntropyS`, and none is to be opened while the re-check condition above is unmet. Catalogue row: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the `IsTimeReversalInvariant` / `IsBondInversionInvariant` / `vbsInversionParityS` / `entanglementEntropyS` row, which labels `entanglementEntropyS` an **AXIOM** and points back here. That row's text differs from the frozen `docs/index.md` baseline through an `approved_changes()` entry in `scripts/check_docs_hierarchy.py`, which is what keeps the frozen-parity check exact.
- **Also recorded here (same module, no separate entry): the §8.3.2 odd/even-`S` SPT classification has no explicit formalization in this repository at all.** Tasaki states it only as a belief — "It is indeed believed that, when `S` is an odd integer, a spin `S` quantum antiferromagnetic chain exhibiting the Haldane gap is in a nontrivial SPT phase protected by one of (S1), (S2), or (S3) above [81, 82]. When `S` is an even integer, on the other hand, it is believed that the model exhibiting the Haldane gap belongs to the trivial phase." (p. 258) — so there is no proof in the book to formalize; the marker pair that used to name it in `SPTTopologicalIndex.lean`, `IsSpinSVBSNontrivialSPT : ℕ → Prop` together with `tasaki_spt_classification : IsSpinSVBSNontrivialSPT S ↔ Odd S`, was removed because it was **self-satisfiable and contentless** (the interpretation `fun S => Odd S` satisfies it outright) and had zero consumers, so it asserted nothing about any VBS state, any Hamiltonian or any phase and could be neither discharged nor refuted. A rigorous version, should one ever be wanted, must be stated against real objects — a general-`S` VBS state and the §8.3.4 (MPS) / §8.3.6 (Ogata) indices, i.e. the same missing layer as the entries above — and not by reinstating an opaque predicate.
- **Also recorded here (same module, no separate entry): the (S2) time-reversal marker `IsTimeReversalInvariant` and the general-`N` `IsTimeReversalSymmetricS` are a genuine duplicate pair, kept in parallel.** `IsTimeReversalInvariant (H : ManyBodyOpS (Fin L) 2) : Prop` (`SPTTopologicalIndex.lean`, doc comment lines 64-70, declaration line 71) has the same type and meaning as the `N = 2` instance of `IsTimeReversalSymmetricS {L N : ℕ} : ManyBodyOpS (Fin L) N → Prop` (`LiebSchultzMattisDiscrete.lean`, declaration line 62), so the scope split the two doc comments used to claim is not real. `IsTimeReversalInvariant` has zero consumers; `IsTimeReversalSymmetricS` occurs only as a hypothesis of the axiom `tasaki_theorem_8_6` (`LiebSchultzMattisDiscrete.lean:84`), and no proved result depends on either, so the redundancy is inert. Consolidating them would delete a declaration, which is a separately approved decision that has not been taken; the pair is therefore recorded here as knowingly parallel rather than removed, and both doc comments say so.
