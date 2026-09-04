---
layout: page
title: "Documented-axiom status and axiomatization policy"
permalink: /limitations/documented-axioms/
---

# Documented-axiom status and axiomatization policy

> This current policy text was moved losslessly from the former monolithic index.

> **Read the correction below before applying the policy text.** Its third class ("Book theorems
> that Tasaki states without proof") states, in general form, a rule this project has withdrawn.
> The block is frozen at its migrated wording, so the withdrawal is recorded after it, in
> [Correction: citation-only status is not a ground for a documented
> axiom](#correction-citation-only-status-is-not-a-ground-for-a-documented-axiom).

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

- **Perturbation-theoretic results** (e.g., the singular-perturbation and
adiabatic-continuation arguments in Chapter 10, the cluster expansions behind
**Theorem 7.3** and **Theorem 8.1**, and the quasi-adiabatic continuation behind
**Theorem 8.9**): the analytic proofs of weak-coupling continuation and adiabatic
following for eigenstate families are **not undertaken** as an active project goal;
such techniques naturally belong to a separate analytic-perturbation development.
The class is delimited by the *machinery* it needs — analytic eigenvalue-branch
(Rellich–Kato) continuation, cluster/polymer expansions, volume-uniform estimates —
and does **not** cover finite-dimensional degenerate perturbation theory at fixed
finite volume, which is ordinary linear algebra and is proved (**Lemma 10.1**, the
strong-coupling **Theorem A.12**, and **Theorem 10.4** are all axiom-free).

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

## Correction: citation-only status is not a ground for a documented axiom

This supersedes the third class of the policy text above ("Book theorems that Tasaki states
without proof"). That paragraph states, in general form, that results Tasaki quotes rather than
proves are recorded as faithful documented axioms and that reproving the cited external work is
not an active project goal. **That rule is withdrawn**, by the 2026-07-05 decision recorded in the
Chapter 4 entries: an externally cited result the book merely quotes is to be proved, not deferred
for being cited. The paragraph is frozen in place above only because the block is held at byte
parity with the text it was migrated from.

**What this correction is, and what it is not.** It withdraws one ground and nothing else. It does
**not** enumerate the admissible grounds and states no closed list of them. The authority for what
is excluded from the book-order formalization campaign is the body of the campaign tracking issue
**#5379**: a target is excluded only if it is a policy-approved actual Lean `axiom` class or an
exact user-approved defer. The entries on the chapter pages keep their own recorded reasons, which
are more varied than any list here would capture.

**Effect, entry by entry.** Citation-only status — "Tasaki cites this result instead of proving
it" — no longer sustains an entry by itself. The census below is taken over all thirty-five entries
on the eight chapter ledgers, counting an entry as invoking citation-only when the ground recorded
for the axiom it carries states that Tasaki cites or states the result rather than proving it —
including entries that name the rule only to record that it does not override them. One of the
thirty-five, the [Corollary 4.3 support
entry](/lattice-system/limitations/documented-axioms/chapter-04/#entry-corollary-4-3-support),
carries **no axiom of its own**: it stays on a ledger of documented axioms because the axiom its
result is charged to is documented here, in the Theorem 4.2 entry, and it is counted in none of the
buckets below, which classify entries by the ground of the axiom they carry. Of the remaining
thirty-four, **sixteen invoke citation-only.** **Six rest on it alone**, so the retraction leaves
them without a recorded ground:

- [Theorem 4.24](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-24) (improved Hohenberg–Mermin–Wagner) and
  [Theorem 4.25](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-25) (McBryan–Spencer, Koma–Tasaki power-law
  bound), recorded as "an external analytic technique that Tasaki reports without reproducing".
  Their re-check conditions ask only for a transcription of that method; neither entry claims any
  machinery is missing here. Theorem 4.24 calls itself the same class as
  [Theorem 7.7](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-7) and Theorems 4.26/4.27, and Theorem 4.25 the
  same class as Theorem 4.24; but Theorem 7.7 and Theorems 4.26/4.27 record different grounds of
  their own, which survive.
- [Theorem 10.11](/lattice-system/limitations/documented-axioms/chapter-10/#entry-theorem-10-11) (Kubo–Kishi) and
  [Theorem 11.13](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-13) (Mielke), the two the withdrawn
  paragraph names.
- [Theorem 11.8](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-8) (Nagaoka connectivity classification),
  "a cited external classification theorem".
- [Lemma 11.25](/lattice-system/limitations/documented-axioms/chapter-11/#entry-lemma-11-25) (Hubbard–t-J equivalence in the
  strong-coupling limit), "the technical transfer itself is the original paper's argument".

Being left without a recorded ground does not discharge these six and does not by itself remove
their Lean axioms; what it removes is their standing as **precedent**. No further axiom may be
justified by pointing at them, and the cross-references between them calling each other "the same
class" describe how they were classified when written, not a live class that admits new members.

**One entry splits.** [Lemma 4.15 and Theorem 4.11
support](/lattice-system/limitations/documented-axioms/chapter-04/#entry-lemma-4-15-theorem-4-11-support) carries three axioms on two
different grounds. Its `p̂` mirror `mStar_eq_phat_ratio_limit` rests on citation-only alone —
Tasaki's eq. (4.2.40) calls the concentration "elementary, proof omitted; see [66]", and that
entry's own tracking bullet records that this axiom carries no other marker — so that one axiom
is in the same position as the six entries above. Its two `ô²` mirrors carry an **explicit dated
decision (2026-07-12, the "no-overreach boundary")**, recorded in their doc comments, and are
unaffected.

**Nine more invoke citation-only together with a second ground this correction does not touch**,
and are unaffected in substance:

- [Theorem 7.2](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-2) (AKLT infinite chain), whose ground is the
  operator-algebra / C\*-algebra–GNS class: its proof (Matsui) "is carried out entirely in that
  operator-algebraic setting and is not reproduced by Tasaki, who states it without proof".
- [Theorem 7.3](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-3) (stability of the AKLT gap), recorded as
  "Tasaki states Theorem 7.3 without proof and attributes it to … Yarotsky", and standing on the
  **volume-uniform perturbation-theory** class of the policy text above (a convergent
  cluster/polymer expansion, absent here). Source access is explicitly not its obstacle.
- [Theorem 8.1](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-theorem-8-1) (large-`D` phase) and
  [Theorem 8.9](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-9) (stability of the toric code) also
  stand on the **volume-uniform perturbation-theory** class — a convergent cluster expansion and
  quasi-adiabatic continuation / Lieb–Robinson bounds respectively. That reading stands on the
  perturbation-theory ground.
- [Theorem 8.3](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-theorem-8-3) (λ-D model) also stands on the
  absence of any path-integral / positive quantum-to-classical representation layer here.
- [Eq. (8.3.3)](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-eq-8-3-3) (Oshikawa parity dependence) also stands
  on the missing general-`S` extension of the existing spin-one VBS / string-order machinery.
- [Theorem 8.6](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-6) (Lieb–Schultz–Mattis without
  continuous symmetry), whose entry opens "the book explicitly declines to prove the theorem and
  defers to an operator-algebraic paper" and then stands on that operator-algebra ground
  (Ogata–Tasaki, via the split property and the associated Cuntz algebra).
- [Theorem 8.8](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-8) (index theorem and the SPT phase
  transition), which records its ground as a **missing layer** — this repository has nowhere to
  write down infinite-volume gaplessness, ground-state multiplicity, or the `s`-dependence of an
  infinite-volume expectation — and notes Tasaki's own non-proof separately from it. It is listed
  because that note is inside its recorded reason; nothing about it turns on the retraction.
- [Theorem 11.27](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-27) (Tanaka–Tasaki metallic ferromagnetism)
  also stands on a genuine `u₂, U ↑ ∞` limit, the same limit-taking caveat as Theorem 5.4.

Five of these entries — Theorems 7.2, 7.3, 8.1, 8.6 and 8.9 — say in their own text that the
"prove theorems Tasaki cites without proof" rule does not override them. Each of those readings
stands on the entry's second ground, not on citation-only, and so survives unchanged.

**Three entries read as though they invoked citation-only, and do not.** The
[general-`S` bond-inversion parity entry](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-general-s-bond-inversion-parity)
records only the missing general-`S` extension of the spin-one machinery; the claim it defers is
Tasaki's own remark that the `S = 1` argument "can be extended to general `S` in a straightforward
manner", not an external citation, and it has no Lean declaration at all.
[Theorem 5.4](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-4) names the policy only to place itself under the
**open-conjecture** exclusion — Tasaki's footnote says the existence of the iterated limit is
itself unproved — "rather than being a tractable finite-dimensional cite-only case".
[Theorem 4.2](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-2) is **not** a won't-do citation, per the
2026-07-05 override, and says so in so many words. The
[Corollary 4.3](/lattice-system/limitations/documented-axioms/chapter-04/#entry-corollary-4-3-support) entry is not among the three, and
not because its text is silent about the book's non-proof — it records that Tasaki proves neither
the corollary nor Theorem 4.2 — but because it carries no axiom of its own for any ground to be
recorded of; its content is charged to Theorem 4.2, whose classification it inherits; see below.

**Theorem 7.7 is left exactly where its own entry puts it, and does not invoke citation-only.**
[That entry](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-7) records a real implementation dependency: the
rigorous two-dimensional honeycomb correlation-decay proof requires Kennedy–Lieb–Tasaki [41], for
which no open-access or author-hosted copy was found — checked 2026-08-16 via OpenAlex, Unpaywall
and author homepages, with the entry noting that open-access status is time-varying and should be
re-checked rather than assumed permanent. Its discharge issue #5132 is closed as not planned
(2026-08-16); no other dated decision appears in the entry. This correction does not reach it, does
not reclassify it, and denies no part of its recorded ground; its own re-check condition — [41]
obtained and transcribed, or an independent [41]-free proof of eq. (7.3.9) — governs.

**Theorem 4.2** (Shastry; Tasaki §4.1, footnote 3, p. 76) and **Corollary 4.3** (§4.1,
eq. (4.1.11), p. 77) are results of precisely the kind the withdrawn paragraph would have parked —
the book cites rather than proves them. They are therefore **open, not deferred.** Both are now carried by the
single axiom `shastryEnergyGain`: Corollary 4.3 is proved from Theorem 4.2 the way the book proves
it, by contraposition, so it no longer has a susceptibility axiom of its own. That axiom is a live
discharge target, tracked in the [Chapter 4 entries](/lattice-system/limitations/documented-axioms/chapter-04/); a reader who finds it
in this ledger should read it as unfinished work, not as settled policy.

**Bulk reclassification is out of scope here and is parked.** This section records the withdrawal
and how far it reaches; it rewrites no chapter entry. Re-deriving the six citation-only-alone
entries and the `p̂` axiom onto a ground that survives, retiring their axioms, or opening discharge
work for them is separate work, and belongs to the campaign tracked in **#5379**.

## Entry pages

The per-declaration entries are recorded on the chapter pages below; this page keeps the
policy text only.

- [Tasaki Chapter 7](/lattice-system/limitations/documented-axioms/chapter-07/) — <a id="theorem-77-hexagonal-aklt-correlation-decay-and-infinite-volume-uniqueness"></a>[Theorem 7.7](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-7), <a id="theorem-72-aklt-infinite-chain-unique-ground-state-with-a-nonzero-gap"></a>[Theorem 7.2](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-2), <a id="theorem-73-stability-of-the-aklt-gap-under-small-local-perturbations"></a>[Theorem 7.3](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-3)
- [Tasaki Chapter 8 (part 1 of 3)](/lattice-system/limitations/documented-axioms/chapter-08-part-01/) — <a id="theorem-81-large-d-phase-of-the-anisotropic-s--1-chain-l-uniform-gap-and-clustering"></a>[Theorem 8.1](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-theorem-8-1), <a id="theorem-83--d-model-nel-order-bounded-by-string-order"></a>[Theorem 8.3](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-theorem-8-3), <a id="eq-833-oshikawa-parity-dependence-of-the-spin-s-vbs-string-order"></a>[Eq. (8.3.3)](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-eq-8-3-3)
- [Tasaki Chapter 8 (part 2 of 3)](/lattice-system/limitations/documented-axioms/chapter-08-part-02/) — <a id="spt-phase-markers-isshortrangegappeduniquegs-isproductstatehamiltonian"></a>[§8.3.2 SPT-phase markers](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-spt-markers-8-3-2), <a id="general-s-bond-inversion-parity-of-the-vbs-state-p-259-unnumbered-display"></a>[General-`S` bond-inversion parity](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-general-s-bond-inversion-parity), <a id="entanglement-entropy-marker-entanglemententropys"></a>[§8.3.3 entanglement-entropy marker](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-entanglement-entropy-8-3-3)
- [Tasaki Chapter 8 (part 3 of 3)](/lattice-system/limitations/documented-axioms/chapter-08-part-03/) — <a id="theorem-86-lieb-schultz-mattis-type-theorem-without-continuous-symmetry"></a>[§8.3.5 Theorem 8.6](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-6), <a id="theorem-88-rigorous-index-theorem-and-the-spt-phase-transition"></a>[§8.3.6 Theorem 8.8](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-8), <a id="theorem-89-stability-of-the-toric-codes-topological-order-under-arbitrary-local-perturbations"></a>[§8.4 Theorem 8.9](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-9)
- [Tasaki Chapter 4](/lattice-system/limitations/documented-axioms/chapter-04/) — [Theorem 4.2 support](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-2), [Corollary 4.3 support](/lattice-system/limitations/documented-axioms/chapter-04/#entry-corollary-4-3-support), [Lemma 4.15 / Theorem 4.11 support](/lattice-system/limitations/documented-axioms/chapter-04/#entry-lemma-4-15-theorem-4-11-support), [Theorem 4.20](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-20), [§4.3 thermodynamic-limit bridge](/lattice-system/limitations/documented-axioms/chapter-04/#entry-section-4-3-thermodynamic-limit-bridge), [Theorem 4.22](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-22), [Theorem 4.23](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-23), [Theorem 4.24](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-24), [Theorem 4.25](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-25), [Theorem 4.26](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-26), [Theorem 4.27](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-27)
- [Tasaki Chapter 5](/lattice-system/limitations/documented-axioms/chapter-05/) — [Theorem 5.1](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-1), [Theorem 5.2](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-2), [Theorem 5.3](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-3), [Theorem 5.4](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-4)
- [Tasaki Chapter 10](/lattice-system/limitations/documented-axioms/chapter-10/) — [Theorem 10.11](/lattice-system/limitations/documented-axioms/chapter-10/#entry-theorem-10-11)
- [Tasaki Chapter 11](/lattice-system/limitations/documented-axioms/chapter-11/) — [Theorem 11.8](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-8), [Theorem 11.13](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-13), [Theorem 11.18](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-18), [Theorem 11.19](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-19), [Lemma 11.22/11.23](/lattice-system/limitations/documented-axioms/chapter-11/#entry-lemma-11-22-11-23), [Lemma 11.25](/lattice-system/limitations/documented-axioms/chapter-11/#entry-lemma-11-25), [Theorem 11.27](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-27)

Each `<a id="…">` above is the id Kramdown generated for that entry's heading while this page
still carried the entries, so links published against the former single-page ledger keep
resolving. Entries written after the split were never addressable here and get no such id.

A new entry is written on the page of its Tasaki chapter (`chapter-NN.md`, created on first
use and added to this list). When a page would exceed 48 KiB, start the next `-part-NN` page
so that the 64 KiB soft page-size threshold of `scripts/check_docs_hierarchy.py` stays an
early warning rather than the first signal of the 128 KiB hard failure.
