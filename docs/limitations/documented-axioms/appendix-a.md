---
layout: page
title: "Documented axioms: Tasaki Appendix A (operator-algebraic core)"
permalink: /limitations/documented-axioms/appendix-a/
---

# Documented axioms: Tasaki Appendix A (operator-algebraic core)

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

The [documented-axiom policy](/lattice-system/limitations/documented-axioms/) names this class
generically ("Wigner's theorem, states, Banach–Alaoglu, ground states of infinite systems, the GNS
construction") without giving a per-declaration entry. This page supplies that entry for each of
the seven Appendix A.21–A.28 declarations.

<a id="entry-wigner-theorems-a-21-a-22"></a>

## Theorems A.21–A.22 (Wigner's theorem)

**Tasaki §A.6, Theorems A.21–A.22** (eqs. (A.6.1)–(A.6.10), pp. 482–485) are three
**documented axioms** in `LatticeSystem/Math/WignerTheorem.lean`: `wignerAutomorphism_unitary`,
`wignerAutomorphism_antiunitary`, and `wignerProjection`.

- **Proved (axiom-free):** the notion the third axiom quantifies over is a genuine `def` in the
  same file — `IsRankOneProjection P` (`P.IsHermitian ∧ P * P = P ∧ P.trace = 1`), the matrix
  rendering of a "ray". Only the three implementability statements are axiomatized.
- **What each axiom statement literally asserts:**
  - `wignerAutomorphism_unitary` — a one-to-one, multiplicative, `∗`-preserving, ℂ-linear map `Γ`
    on `Matrix D D ℂ` (a *linear* `∗`-automorphism, Tasaki's (A1)–(A4)) is implemented by a
    unitary `Û`: `Γ(Â) = Û† Â Û` for all `Â` (eq. (A.6.1)).
  - `wignerAutomorphism_antiunitary` — the same hypotheses except *antilinear* in place of
    ℂ-linear (Tasaki's (A4′)) give conjugation by a unitary composed with entrywise complex
    conjugation, `Γ(Â) = Û† (Â.map conj) Û` (eq. (A.6.2)).
  - `wignerProjection` — a map `Γ` carrying rank-one orthogonal projections to rank-one
    orthogonal projections and preserving transition probabilities `Tr[P P′]` is implemented by a
    unitary `U` in one of two ways: either `Γ(P) = U P U†` for every rank-one `P` (the unitary
    case) or `Γ(P) = U P̄ U†` for every rank-one `P` (the antiunitary case, `P̄ = P.map conj`),
    eq. (A.6.10).
  None of the three asserts uniqueness of the implementing operator up to a phase; that part of
  the book statement is recorded only in the module's prose, not in the Lean statement.
- **Axiom reason (documented):** Wigner's theorem and its automorphism variant (Bargmann) are deep
  results outside the finite-dimensional linear-algebra core this project proves from scratch; per
  the [documented-axiom policy](/lattice-system/limitations/documented-axioms/)'s operator-algebra
  class, they are recorded as faithful documented axioms and are not an active proof target. (The
  finite-dimensional statement here does not itself need C*-algebra machinery to state — `D` is a
  `Fintype` and `Matrix D D ℂ` is finite-dimensional — but the proof method (rays, projective
  Hilbert space geometry) is the deep part being deferred, not a missing finite-dimensional
  framework.)
- **Consumers:** none. `wignerAutomorphism_unitary`, `wignerAutomorphism_antiunitary`, and
  `wignerProjection` have no Lean consumer in `LatticeSystem/`: each occurs there only at its own
  `axiom` declaration in `LatticeSystem/Math/WignerTheorem.lean`, and no proved result depends on
  any of them. The remaining mentions in the corpus are documentation references — the roadmap
  history page lists all three, and the proof guide cites `wignerProjection` — and neither consumes
  them.
- **Re-check condition:** the disposition would change when a math-before-code transcription of
  Wigner's/Bargmann's proof (the rank-one-projection argument sketched in Tasaki §A.6.1) is
  completed for the finite-dimensional case, or when an equivalent result becomes available from
  `mathlib`.

<a id="entry-theorem-a-24-banach-alaoglu"></a>

## Theorem A.24 (Banach–Alaoglu for states)

**Tasaki §A.7, Theorem A.24** (eq. (A.7.3), pp. 488–489) is a **documented axiom**,
`stateSpace_isCompact` (`LatticeSystem/Math/CStarAlgebra/State.lean`).

- **Proved (axiom-free):** Definition A.23 (state on a C*-algebra) is a genuine `def`, `IsState`
  (same file): a weak-∗-continuous linear functional `φ : WeakDual ℂ A` with `φ(1) = 1` and
  `0 ≤ φ(star a * a)` for every `a`. `stateSpace A` is the corresponding subset of
  `WeakDual ℂ A`. Only the compactness of that set is axiomatized.
- **What the axiom statement literally asserts:** for a unital complex C*-algebra `A`
  (`[CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]`), `IsCompact (stateSpace A)` in the
  weak-∗ topology — equivalently (Tasaki's elementary reading, eq. (A.7.3)) every sequence of
  states has a weak-∗-convergent subsequence with limit again a state.
- **Axiom reason (documented):** Banach–Alaoglu compactness of the state space is a genuine
  functional-analytic/operator-algebraic input — it is the fact that makes infinite-volume limits
  of states available (Tasaki cites eq. (4.3.7) as its use) — and belongs to the operator-algebra
  class of the [documented-axiom policy](/lattice-system/limitations/documented-axioms/): a
  dedicated operator-algebra/functional-analysis development, whose natural home may be `mathlib`
  itself.
- **Consumers:** none. `stateSpace_isCompact` has no Lean consumer in `LatticeSystem/`: it occurs
  there only at its own `axiom` declaration in `LatticeSystem/Math/CStarAlgebra/State.lean`, and no
  proved result depends on it. The sole other mention in the corpus, on the roadmap history page,
  is a documentation reference and does not consume it.
- **Re-check condition:** the disposition would change when `mathlib` (or a project-local
  development) supplies weak-∗ compactness of the state space of a general unital C*-algebra, or
  the specific instance needed here.

<a id="entry-theorem-a-26-ground-state-variational-characterization"></a>

## Theorem A.26 (variational characterization of ground states)

**Tasaki §A.7, Definitions A.25/A.27 and Theorem A.26** (eqs. (A.7.4)–(A.7.7), pp. 488–489) are
carried by two declarations in `LatticeSystem/Math/CStarAlgebra/GroundState.lean`:
`IsLocalHamiltonianData` (a marker axiom) and `groundState_variational` (the theorem axiom).

- **Proved (axiom-free):** Definitions A.25 and A.27 are genuine `def`s in the same file —
  `IsGroundState ω δ` (`∀ a, 0 ≤ ω (star a * δ a)`) and `HasNonzeroGap ω δ γ`
  (`0 < γ ∧ ∀ a, ω a = 0 → (γ : ℂ) * ω (star a * a) ≤ ω (star a * δ a)`), where `δ : A → A` models
  the Hamiltonian commutator `Â ↦ [Ĥ, Â]`. Only the variational-characterization theorem
  (Theorem A.26) and the marker gating its hypotheses are axiomatized.
- **What each axiom statement literally asserts:**
  - `IsLocalHamiltonianData : (A → A) → (ℕ → A) → (ℕ → Set (WeakDual ℂ A)) → Prop` is an
    uninterpreted Prop-valued marker with **no mathematical content of its own**, standing for
    "`(δ, HL, CL)` are the dynamics `[Ĥ, ·]`, partial Hamiltonians `Ĥ_L = Σ_{x ∈ Λ_L} ĥ_x`
    (eq. (A.7.6)), and outside-`Λ_L` constraint sets `C_L^ω` (states agreeing with `ω` outside
    `Λ_L`) of one and the same quantum spin Hamiltonian on `ℤᵈ`." It exists so that
    `groundState_variational` is stated only for genuine local-Hamiltonian data and cannot be
    applied to unrelated `δ, HL, CL`.
  - `groundState_variational` — given `IsLocalHamiltonianData δ HL CL`, `ω ∈ CL L` for every `L`,
    and `CL L ⊆ stateSpace A` for every `L`: `IsGroundState ω δ ↔ ∀ L, IsLeast
    ((fun φ => (φ (HL L)).re) '' CL L) ((ω (HL L)).re)` (eq. (A.7.7)) — `ω` is a ground state iff
    for every `L` the energy `ω(Ĥ_L)` is least among states agreeing with `ω` outside `Λ_L`.
- **The marker has no mathematical content:** the same idiom as `IsAKLTChainDynamics`/
  `IsTranslationCovariant` in the Chapter 7 documented-axiom entries (see
  [Theorem 7.2](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-2) and
  [Theorem 7.3](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-3)) — it
  cannot be established for any concrete data, so `groundState_variational` is usable only under an
  assumed hypothesis, and since the marker admits the interpretation "always false" the pair adds
  no inconsistency.
- **Axiom reason (documented):** Theorem A.26 is a deep operator-algebraic result
  (Bratteli–Robinson) about states of the quasi-local C*-algebra of an infinite quantum spin
  system, parametrized by the partial-Hamiltonian family `Ĥ_L` and the constraint sets `C_L`; it
  belongs to the operator-algebra class of the [documented-axiom
  policy](/lattice-system/limitations/documented-axioms/) and is not an active proof target.
- **Consumers:** none. `groundState_variational` has no Lean consumer in `LatticeSystem/`: it
  occurs there only at its own `axiom` declaration in
  `LatticeSystem/Math/CStarAlgebra/GroundState.lean`, where `IsLocalHamiltonianData`, besides its
  own `axiom` declaration, occurs only as that theorem's gating hypothesis; no proved result
  depends on either declaration. The remaining mentions in the corpus are documentation
  references — the roadmap history page names `groundState_variational`, and the Chapter 7
  Theorem 7.2 entry names `IsLocalHamiltonianData` only as an analogy for a different marker's
  idiom — and neither consumes them.
- **Re-check condition:** the disposition would change when (a) a concrete construction of the
  quasi-local C*-algebra of a quantum spin system on `ℤᵈ`, together with the local Hamiltonians
  `ĥ_x` and the partial Hamiltonians `Ĥ_L`, replaces `IsLocalHamiltonianData` with a real
  definition, and (b) a math-before-code transcription of the Bratteli–Robinson variational
  argument is completed for that concrete data.

<a id="entry-theorem-a-28-gns-construction"></a>

## Theorem A.28 (Gelfand–Naimark–Segal construction)

**Tasaki §A.7, Theorem A.28** (eqs. (A.7.8)–(A.7.11), pp. 489–490) is a **documented axiom**,
`gns_construction` (`LatticeSystem/Math/CStarAlgebra/GNS.lean`).

- **What the axiom statement literally asserts:** for a unital complex C*-algebra `A`
  (`[CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]`) and a state `ρ : WeakDual ℂ A` with
  `IsState ρ`, there exist a Hilbert space `H` (`NormedAddCommGroup`, `InnerProductSpace ℂ`,
  `CompleteSpace`), a `∗`-representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)`, and a vector `Ω : H` such
  that `ρ a = ⟪Ω, π a Ω⟫_ℂ` for every `a` (eq. (A.7.11)) and `{π a Ω | a ∈ A}` is dense in `H`
  (cyclicity) — i.e. `(H, π, Ω)` is a GNS triple for `ρ`, and every state is a vector state in its
  GNS space.
- **Axiom reason (documented):** `mathlib` already contains GNS machinery
  (`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`: `f.GNS`, `gnsStarAlgHom`); the module
  doc records that this axiom is "dischargeable from that machinery" but the precise Tasaki
  packaging (the cyclic vector recovering the state, eq. (A.7.11), plus the density condition) has
  not been assembled from it. Per the [documented-axiom
  policy](/lattice-system/limitations/documented-axioms/), the GNS construction is named in the
  operator-algebra class and is recorded as a faithful documented axiom rather than an active proof
  target — but unlike the other six axioms recorded here, the module doc itself flags this one as
  the most directly dischargeable, since the needed `mathlib` machinery already exists.
- **Consumers:** none. `gns_construction` has no Lean consumer in `LatticeSystem/`: it occurs
  there only at its own `axiom` declaration in `LatticeSystem/Math/CStarAlgebra/GNS.lean`, and no
  proved result depends on it. The sole other mention in the corpus, on the roadmap history page,
  is a documentation reference and does not consume it.
- **Re-check condition:** the disposition would change when a math-before-code comparison of
  `mathlib`'s `GelfandNaimarkSegal.lean` API against the exact statement above (existence of the
  cyclic vector, eq. (A.7.11), and density) confirms the packaging goes through, and the axiom is
  replaced by a theorem built on that `mathlib` construction.
