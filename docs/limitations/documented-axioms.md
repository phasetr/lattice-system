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
  as `IsAKLTChainDynamics` (Theorem 7.2, above). It stands for v̂_x = T̂^x v̂_o (T̂†)^x,
  which needs a chain translation operator that the repository does not define;
  keeping it as a hypothesis is deliberate, since dropping it would let the axiom
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
  polymer/cluster expansion, no uniform-in-L analyticity layer, and no chain
  translation operator (the only occurrences of "cluster expansion" under
  `LatticeSystem/` are the doc comments of this axiom and of the Theorem 8.1 large-D
  axiom). Per the policy above, perturbation-theoretic
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
  enough to prove gap stability rather than assume it; (b) a real definition of the
  chain translation operator T̂ on `ManyBodyOpS (Fin L) 2`, so that
  `IsTranslationCovariant` is replaced by the actual condition
  v̂_x = T̂^x v̂_o (T̂†)^x instead of an opaque marker; and (c) a math-before-code
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
