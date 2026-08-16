---
layout: page
title: "Appendix status and axiomatization policy"
permalink: /limitations/documented-axioms/
---

# Appendix status and axiomatization policy

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
axiom**, `tasaki_theorem_7_7` (`LatticeSystem/Quantum/SpinS/GeneralAKLT.lean`, lines
128–183). This page's title and banner scope it to Appendix A; this section records a
non-Appendix documented axiom here as well, pending the broader reorganization tracked
by #5228.

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
     predicate. `#print axioms` on any consumer of `tasaki_theorem_7_7` therefore shows
     *two* axiom names, one of which (`HasUniqueInfiniteVolumeVBSGroundState`) carries
     no formalized statement at all.
- **Not yet formalized (book-level content, not literally part of the axiom
  statement):** per the catalogue's own language (`docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`,
  rows for `honeycombVBSState` and `honeycombVBSState_isGeneralGraphVBSGroundState`),
  finite-volume ground-state uniqueness, a spectral gap, and (for a general hexagon)
  the finite-volume ingredients of the correlation-decay estimate all "remain
  unproved." These are not asserted by `tasaki_theorem_7_7` as stated (which only
  requires *existence* of a decaying-correlation ground state, not uniqueness or a
  gap), so they should not be read off the axiom text; they are simply absent from the
  formalization entirely.
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
  real implementation dependency confirmed unobtainable **as of 2026-08-16** (via
  automated OpenAlex/Unpaywall/author-homepage search; open-access status is
  time-varying and this claim should be re-checked, not assumed permanent): OpenAlex
  work `W2092140400` reports `oa_status = closed` with no repository fulltext;
  Unpaywall confirms `is_oa = false`; none of Kennedy, Lieb, or Tasaki self-host a copy
  (Kennedy's own publication page links only to a dead `springerlink.com` URL).
- **Re-check condition:** the disposition would change if either (a) a legitimate copy
  of KLT [41] is obtained (e.g. via institutional library/Springer subscription access,
  since no open-access route exists) and a math-before-code transcription of its
  finite-volume uniqueness proof and its proof of eq. (7.3.9) is completed, or (b) an
  independent proof route not depending on KLT [41] is formalized. A private design
  sketch exploring deriving eq. (7.3.9) directly from the explicit finite VBS amplitude
  `honeycombVBSState` is a known candidate for route (b); it is not complete and is not
  currently authorized as active work.
- **Tracking:** Issue #5132 (Theorem 7.7 discharge status); master tracker #4718.
  Catalogue rows: `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md`, the
  `tasaki_theorem_7_7` declaration row (grouped detail record #767) and the two inline
  `honeycombVBSState` / `honeycombVBSState_isGeneralGraphVBSGroundState` rows (not
  grouped detail records) that state the "remain unproved" items cited above.
