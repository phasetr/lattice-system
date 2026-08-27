---
layout: page
title: "Documented axioms: Tasaki Chapter 4 (part 1 of 3)"
permalink: /limitations/documented-axioms/chapter-04-part-01/
---

# Documented axioms: Tasaki Chapter 4 (part 1 of 3)

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-4-2"></a>

## Theorem 4.2 (Shastry: absence of symmetry breaking in one dimension)

**Tasaki §4.1, Theorem 4.2** (eqs. (4.1.9)-(4.1.10), pp. 76-77) is a
**documented axiom**, `shastry_no_symmetry_breaking_1d`
(`LatticeSystem/Quantum/SpinS/ShastryNoSSB.lean`, declaration line 82).

- **Proved (axiom-free):** the one-dimensional staggered-field antiferromagnetic
  Heisenberg Hamiltonian `staggeredFieldChainHamiltonianS` and its ring
  coupling/sublattice-sign helpers (same file) are real definitions.
- **What the axiom statement literally asserts:** for the 1D spin-`S`
  antiferromagnetic Heisenberg ring under staggered field
  `Ĥ_h = Σ_x Ŝ_x·Ŝ_{x+1} − h·Ô_L^{(3)}` (eq. (4.1.9)), the per-site staggered
  order parameter of any *normalized* ground state vanishes in the iterated
  limit `lim_{h↓0} lim_{L↑∞}` (eq. (4.1.10)), stated soundly in `ε`-`δ` form:
  for every `ε > 0` there is a field threshold `h₀ > 0` such that for each
  `0 < h < h₀` there is a size threshold `L₀` beyond which every normalized
  ground state has staggered moment `< ε` per site.
- **Axiom reason (documented):** Tasaki §4.1 footnote 3 (p. 76) explicitly
  states "We do not prove Theorem 4.2 in the present book," referring to
  Shastry's original argument (B. S. Shastry, *J. Phys. A* **25**, L249,
  1992) and its rigorous formulation in Tanaka–Takeda–Idogaki (*J. Magn.
  Magn. Mater.* **272-276**, 908, 2004) [63]. This is the project's
  external-cite-only documented-axiom class; the reflection-positivity
  infrastructure project (#4777) formalizes supporting finite-dimensional RP
  layers for the Gibbs decomposition, not a re-proof of Theorem 4.2 itself.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Shastry / Tanaka–Takeda–Idogaki argument is
  completed.
- **Tracking:** master tracker #4718; supporting infrastructure issue #4777
  (reflection-positivity, does not itself discharge this axiom).

<a id="entry-corollary-4-3-support"></a>

## Corollary 4.3 support (Shastry staggered susceptibility bound)

**Tasaki §4.1, Corollary 4.3** (eq. (4.1.11), p. 77, with footnotes 3 (p. 76)
and 9 (p. 83)) rests on one **documented axiom**,
`shastry_staggered_susceptibility_bound`
(`LatticeSystem/Quantum/SpinS/NoLongRangeOrder1D.lean`, declaration line 64).

- **Proved (axiom-free):** Corollary 4.3 itself, `no_long_range_order_1d`
  (`NoLongRangeOrderConditional.lean`), is a genuine **theorem**, obtained by
  feeding this axiom as the single quantitative input into the conditional
  reduction `no_long_range_order_1d_of_susceptibility`; only the
  susceptibility estimate below remains axiomatized.
- **What the axiom statement literally asserts:** for the zero-field
  one-dimensional spin-`S` antiferromagnetic Heisenberg ring on an **even**
  number `L ≥ 2` of sites, there is a size-uniform constant `C ≥ 0` such that
  every normalized ground state `Φ` admits a potential `y` for `ÔΦ` (i.e.
  `(Ĥ − E₀) y = ÔΦ`) with static staggered susceptibility `Re⟨y, ÔΦ⟩ ≤ C·L`
  (physically `χ(k*) = L · f_L^{(-1)}(k*)` at the antiferromagnetic wavevector
  `k* = π`). Restricted to even `L` because only bipartite rings have a
  balanced staggered sublattice (`Σ_x ε_x = 0`), which is what makes the
  ground state an SU(2)-singlet with `⟨Φ, ÔΦ⟩ = 0` and hence `ÔΦ` orthogonal
  to the ground space, so the resolvent potential `y` genuinely exists; odd
  rings lie outside Tasaki's §4.1 setting.
- **Axiom reason (documented):** Tasaki's footnote 9 (§4.1, p. 83) singles out
  exactly this bound on `f_L^{(-1)}(k*)` as "the only nontrivial part that
  requires some hard analysis," deferring it to Shastry's original bound
  (B. S. Shastry, *J. Phys. A: Math. Gen.* **25**, L249, 1992) and its
  rigorous formulation in Tanaka–Takeda–Idogaki (*J. Magn. Magn. Mater.*
  **272-276**, 908, 2004) [63], cited by Tasaki's footnote 3 (p. 76). The
  quantitative estimate rests on a massive-Green-function / inverse-Fourier
  analysis with `O(L)` control of the `k* = π` singularity that lies outside
  the book's scope — the same external-cite-only class as Theorem 4.2 above.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Shastry / Tanaka–Takeda–Idogaki susceptibility
  estimate is completed.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-lemma-4-15-theorem-4-11-support"></a>

## Lemma 4.15 and Theorem 4.11 support (order-parameter concentration estimates)

Three **documented axioms** record the Koma–Tasaki [66] volume-uniform
concentration mechanism underlying Tasaki §4.2.2 Lemma 4.15 (eq. (4.2.38)) and
the still-open Conjecture 4.12 that Theorem 4.11 (eq. (4.2.23)) would need for
an unconditional equality:

- `mStar_eq_phat_ratio_limit` (`LatticeSystem/Quantum/SpinS/OrderOperatorAlgebra.lean`,
  declaration line 812) — the `p̂`/`U(1)` mirror.
- `orderSqMoment_ratio_le_mStarSq` (`LatticeSystem/Quantum/SpinS/AndersonTowerOrderSqConcentration.lean`,
  declaration line 56) — the `ô²`/`SU(2)` mirror, conditional on the explicit
  hypothesis `IsConjecture412Equality` (never asserted true).
- `orderSqMoment_ratio_le_mStarSq_family` (same file, declaration line 111) —
  the `n = 0` instance of the same mirror, `hFamily`-pinned and
  `Conjecture 4.12`-independent (this is the axiom Theorem 4.11's proved
  "easy half" consumes).

- **Proved (axiom-free):** the surrounding realizing-family machinery
  (`IsRealizingTanakaGroundStateFamily`, the base-ratio log-convexity squeeze
  `orderSqMoment_baseRatio_tendsto`) and the finite-volume order operators
  they quantify over are real definitions, not axioms.
- **What the axiom statements literally assert:** `mStar_eq_phat_ratio_limit`
  states that for a realizing ground-state family `Φ` with exact staggered
  moment `mStar` and LRO limit `q₀`, the bare `p̂`-moment ratio has iterated
  limit `lim_n liminf_L ⟨p̂^{n+1}⟩/⟨p̂^n⟩ ≥ (mStar)²`, together with the bound
  `√(2 q₀) ≤ mStar` (eq. (4.2.39)). `orderSqMoment_ratio_le_mStarSq` states
  the `limsup`-upper direction `∀ n ε, eventually in L, s_n < (mStar)² + ε`
  for the `V²`-normalized `ô²`-moment ratio `s_n`, conditional on
  `IsConjecture412Equality mStar qStar` (`hconj`). Dropping `hconj` while
  leaving `mStar` free would be **unsound** (`mStar := 0` with a genuine LRO
  family makes the claimed bound false), so
  `orderSqMoment_ratio_le_mStarSq_family` instead pins `mStar` to the true
  order parameter via `IsRealizingTanakaGroundStateFamily` and states only the
  `hconj`-free `n = 0` instance, `s₀ ≤ (mStar)² + ε` eventually — the "easy
  half" (`(mStar)² ≥ 3 q₀`) of Theorem 4.11, not the equality `(mStar)² = 3 q₀`
  that Conjecture 4.12 would supply.
- **Axiom reason (documented):** Tasaki §4.2.2 eq. (4.2.40) states the `p̂`-ratio
  concentration is "elementary, proof omitted; see [66]" (T. Koma, H. Tasaki,
  *Symmetry breaking and finite-size effects in quantum many-body systems*,
  J. Stat. Phys. **76**, 745-803, 1994), and eqs. (4.2.59)-(4.2.61) instruct
  the reader to repeat the same argument for the `ô²` field. Per the
  2026-07-12 no-overreach boundary decision, the `ô²` mirror is deferred with
  exact parity to the `p̂` axiom rather than rebuilding the multi-PR [66]
  concentration machinery; Conjecture 4.12 is kept an explicit hypothesis,
  never asserted.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Koma–Tasaki [66] concentration argument is completed
  for both the `p̂` and `ô²` fields (proving, not assuming, the volume-uniform
  moment-ratio limits); Conjecture 4.12 itself would additionally require an
  independent proof of the matching equality, which is a strictly stronger,
  still-open statement.
- **Tracking:** master tracker #4718; the three axioms share the
  "2026-07-12 no-overreach boundary" decision recorded in their doc comments.
  No dedicated discharge issue exists or is to be opened while the re-check
  condition above is unmet.
