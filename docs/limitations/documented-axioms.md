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
- **Consumers:** within `LatticeSystem/`, the only occurrence of `tasaki_theorem_8_1` is its own declaration (`AnisotropicLargeD.lean:61`); so no proved result depends on it. The definition layer is not unconsumed, however: `anisotropicChainHamiltonianS` is used by `guWenHamiltonianS`, the §8.3 Gu-Wen Hamiltonian (8.3.4) (`LatticeSystem/Quantum/SpinS/SPTPhase.lean`, lines 50-51), and is named in the doc comment of the separate open-boundary definition `openAnisotropicChainHamiltonianS` (`LatticeSystem/Quantum/SpinS/AnisotropicEdgeStates.lean`, line 51; `openAnisotropicChainHamiltonianS` itself is declared at line 54, doc comment 50-53). Retiring the axiom later would therefore not disturb the definitions.
- **Faithfulness caveats (recorded, not hidden):**
  1. The printed theorem's fourth (final) sentence — "The ground state in the L ↑ ∞ limit is unique and accompanied by a gap" — has no counterpart in the Lean statement: every conjunct is finite-volume. In this respect the axiom is weaker than the book.
  2. The printed statement makes only ΔE₀(D) explicitly L-independent and says the correlation "decays exponentially in the distance |x − y|" without naming constants. The Lean statement additionally quantifies C and ξ outside ∀L. Volume-uniform decay constants are the standard output of a convergent large-D expansion, but this is not literally in the printed sentence and has not been checked line by line against [49] in this repository. Any future discharge must re-derive, not assume, the C/ξ uniformity. This is the same class of caveat recorded for Theorem 7.3 above.
  3. The uniqueness conjunct is not what the book attributes to the cluster expansion. Tasaki obtains the finite-volume uniqueness of Φ_GS (with Ŝ³_tot Φ_GS = 0) from his Theorem 2.4 (pp. 43-44, proved by Mattis and Nishimori), which covers (8.1.1) as the λ = 1, D ≥ 0 case on a connected bipartite lattice with |A| = |B|; the even periodic ring is such a lattice. The Lean axiom nevertheless bundles `IsUniqueChainGroundState` with the gap and decay conjuncts, so it axiomatizes strictly more than the book attributes to [49]. Nothing in the repository proves this conjunct independently: within `LatticeSystem/`, `IsUniqueChainGroundState` occurs at exactly eight places — its doc comment and definition (`AKLTStability.lean` lines 77 and 81), the Theorem 7.3 axiom (`AKLTStability.lean` lines 92 and 108), this axiom (`AnisotropicLargeD.lean` lines 55 and 66), and the Theorem 8.2 axiom hypothesis (`AnisotropicEdgeStates.lean` lines 69 and 80) — none of which is a proof.
  4. The Lean statement uses the raw two-point function, matching the book's ⟨Φ_GS| Ŝ_x^(α) Ŝ_y^(α) |Φ_GS⟩ (Theorem 7.3, by contrast, uses the connected correlation). The module doc comment and the catalogue row remark that raw and connected coincide here because the disordered symmetric ground state has vanishing one-point functions; that remark is motivating physics — it is neither asserted by the axiom nor proved, and the book itself only expects the Néel order parameter (8.1.3) to vanish.
  5. 2 ≤ L is a Lean-side restriction absent from the printed hypothesis (which requires only that L be even, with periodic boundary); it excludes L = 0.
- **Axiom reason (documented):** Tasaki states Theorem 8.1 without proof, writing that it "is proved by applying standard methods of rigorous perturbation theory (based on a cluster expansion) for quantum spin systems", citing his reference [49] = T. Kennedy, H. Tasaki, *Hidden symmetry breaking and the Haldane phase in S = 1 quantum spin chains*, Commun. Math. Phys. **147**, 431-484 (1992). He adds that D₀ must be taken large for a rigorous proof ("we once estimated that D₀ = 28 is enough") while the large-D phase is expected to extend down to D_c ≈ 1 — the theorem's content is precisely the convergent large-D expansion regime, not a finite-dimensional linear-algebra statement. Mathematically the proof expands around the trivial diagonal Hamiltonian Ĥ_trivial = D Σ_x (Ŝ_x^(3))² of eq. (8.1.2), whose unique ground state ⊗_x |0⟩_x has gap exactly D, treating the Heisenberg term Σ_x Ŝ_x · Ŝ_(x+1) as a perturbation of relative size 1/D; convergence of the polymer/tree-graph expansion uniformly in the volume is what simultaneously yields the L-independent gap bound ΔE₀(D) and the exponentially decaying correlations with L-independent C, ξ. This is the same machinery as Theorem 7.3 (Yarotsky), here around a classical diagonal reference model. The repository contains no such development: no polymer/cluster-expansion framework and no uniform-in-L analyticity layer exist, and repository-wide the phrase "polymer" has zero hits in `LatticeSystem/`. The same absent-framework reasoning already governs two sibling documented axioms with the identical decay shape (`∃ ξ C, 0 < ξ ∧ 0 < C ∧ ∀ …, |corr| ≤ C * exp(-dist/ξ)`), `tasaki_4_22_exponential_clustering` and `tasaki_4_23_high_temperature_disorder` (`HeisenbergEquilibrium.lean`), which are an apposite existing precedent for deferring this conjunct the same way. Per the policy above, perturbation-theoretic results — the same standing named exception under which Lemma 10.1 (degenerate perturbation theory) and the Chapter 10 singular-perturbation arguments are recorded — are faithful documented axioms and are not active proof targets, so the "prove theorems Tasaki cites without proof" rule does not override this entry, and this entry creates no book-order discharge work item. Source access is not the recorded obstacle here (unlike KLT [41] for Theorem 7.7): the recorded reason is the absent perturbation-theory development.
- **Re-check condition:** the disposition would change only when all three of the following exist in reviewed form in this repository (or are usable from mathlib): (a) a general, reviewed cluster/polymer-expansion (or equivalent quantum-perturbation) framework with volume-uniform convergence estimates, strong enough to prove a spectral gap and exponential clustering at large D rather than assume them; (b) a math-before-code transcription of the large-D expansion for (8.1.1) — from Kennedy-Tasaki [49] or an equivalent source — that derives an explicit threshold D₀, an L-independent ΔE₀(D), and L-independent C and ξ; and (c) for the uniqueness conjunct specifically, a Lean proof of Tasaki Theorem 2.4 (pp. 43-44) applicable at S = 1 to (8.1.1) in the λ = 1, D ≥ 0 case on the even ring. The repository's Theorem 2.4 development reaches an unconditional closure for obligation (1) (`anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional`, `AnisotropicHeisenbergStructuralGeneralN.lean:36`, its `hJpos` hypothesis at line 40) and a general spin-S obligation-(2) wrapper (`AnisotropicHeisenbergSpinSMLMEndpoint.lean:62`, its `hJpos` hypothesis at line 65) that no longer needs the SU(2)-endpoint global-uniqueness callback (removed per `docs/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-03.md` row at line 62), but connecting either to (8.1.1) on the ring is not yet done; the list below records *at least* the following open gaps — it is not a claim of completeness, and no one item is asserted to be uniquely "the" obstruction:
  (i) both the obligation-(1) closure and the obligation-(2) wrapper require a complete-bipartite positivity premise `hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re`, and the obligation-(2) wrapper additionally requires a symmetry premise `hJ_sym : ∀ x y, J x y = J y x` (`AnisotropicHeisenbergSpinSMLMEndpoint.lean:68`); the repository's nearest-neighbour ring coupling `ringCoupling` (`ShastryNoSSB.lean:41`) is directed (`J x y = 1` iff `y = x + 1 mod L`, else `0`), so it fails `hJ_sym` for every L ≥ 3, and (minimally verified, not exhaustively checked for every L) fails `hJpos`'s completeness requirement already at small L such as L = 4, holding only in the degenerate L = 2 case;
  (ii) even granting a symmetric coupling, the known bridge from the symmetrized ring coupling to the (isotropic) Heisenberg chain Hamiltonian (`heisenbergHamiltonianS_ringCouplingSym_eq`, `LiebSchultzMattisRingUniqueness.lean:34-36`, which shows `heisenbergHamiltonianS (ringCouplingSym L) N = 2 • afmHeisenbergChainHamiltonianS L N`) has no established analogue for the anisotropic chain: `anisotropicChainHamiltonianS` (`AnisotropicLargeD.lean:47`) has no proved identity connecting it to `anisotropicHeisenbergS`, and its only other occurrences within `LatticeSystem/` are its use inside `guWenHamiltonianS` (`SPTPhase.lean:51`) and a doc-comment mention in `AnisotropicEdgeStates.lean:51`, neither of which supplies such a bridge;
  (iii) both the obligation-(1) closure and the obligation-(2) wrapper conclude an eigenspace-dimension bound (`finrank ℂ eigenspace ≤ 2` and `≤ 1` respectively, the latter via `hermitianMinEigenvalue`), not `IsUniqueChainGroundState` itself, so an additional predicate-transfer step from the finrank bound to `IsUniqueChainGroundState` would still be needed;
  (iv) separately, a connected-coupling route already exists, `tasaki_2_5_theorem_2_3_data_of_connected` (`ConnectedTheorem23.lean:208`), whose doc comment (line 199) records that it "drops the complete-bipartite `hJ_pos` premise", but it has not been wired through either the obligation-(1) closure or the obligation-(2) wrapper above.
  Closing condition (c) requires resolving all of the gaps above (or finding an alternative route not listed here); discharging any single one of (i)-(iv) does not by itself close condition (c), and partial progress on any single item does not reopen this entry, since the gap and decay conjuncts — precisely what the book attributes to [49] — would remain unproved regardless.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No dedicated discharge issue exists for Theorem 8.1, and none is to be opened while the re-check condition above is unmet; the #4485 cited in the proof guide's §8.1.1 paragraph is the closed "Backfill Tasaki Chapters 3-10 numbered items" issue, not a discharge tracker. Catalogue row: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the `anisotropicChainHamiltonianS` / `tasaki_theorem_8_1` row carrying the `tasaki-chapter-8-records` anchor (interim-authoritative archival record; not edited by this entry). The section label §8.1.1 and the pages recorded in the module header, the catalogue row and the proof guide are all correct against the printed book; unlike Theorem 7.3, this entry records no label defect.
