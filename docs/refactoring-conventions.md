---
layout: page
title: Refactoring conventions and review criteria
permalink: /refactoring-conventions/
---

# Refactoring conventions and review criteria

This document captures conventions and review criteria distilled
from the project's refactoring rounds. It is **applied as the
review checklist for every pull request**, not only refactor PRs.

The knowledge is grouped by phase / category so that reviewers can
locate the relevant criteria quickly.

## 1. Test methods (per refactor plan v4 §2.1)

The following table is the canonical menu of test idioms used in
this project. Each PR that adds or changes tests should be
checkable against it.

| Method | Code shape | Use |
|---|---|---|
| **A. decide-based universal** | `example : ∀ x : Fin n, P x := by decide` | Pin the meaning of a finite, `Decidable` predicate. Most refactor-resistant. |
| **B. matrix entry-wise on small `Fin n`** | `ext i j; fin_cases i <;> fin_cases j <;> simp [defn_apply]` | Cross-check small matrix-valued definitions. Catches meaning changes immediately. |
| **C. bridge identity** | `example : defn_A = defn_B := rfl` | Pin the consistency of two definitions of the same object. Refactor detector. |
| **D. signature-preservation shim** | `example : <type> := named_thm args` | **Limited** to public API freeze. Survives rename only of the body, not of the name. |
| **E. `Plausible`** | (POC only) | **Not primary.** Generator integration cost is high for our `ℂ` / matrix setting. |
| **F. `#guard_msgs`** | `/-- expected msg -/ #guard_msgs in <command>` | Pin diagnostic output: `@[deprecated]` warnings, intended failures, linter behaviour. **Not** for theorem regression. |
| **G. small exhaustive (`Fin n; fin_cases`)** | `example : ∀ x : Fin n, P x := by intro x; fin_cases x <;> simp` | Pin meaning of a parameterised lemma on a small but complete sample. The most refactor-resistant for parameterised statements. |

**Primary axis**: A + C + G. **Limited use**: D, B. **Niche**: F. **Not primary**: E.

For canonical examples of methods A / B / C / F / G in
working code, see [`LatticeSystem/Tests/Foundation.lean`][1] —
the test-method POC file from Phase 0 (#280). Each method has
a labelled subsection with at least one minimal example.

[1]: https://github.com/phasetr/lattice-system/blob/main/LatticeSystem/Tests/Foundation.lean

### Review check — tests

When a PR introduces or modifies tests, the reviewer checks:

- [ ] Each module / cluster covered by at least one of A / C / G
  (not only D shims).
- [ ] If only D shims are added, the PR description justifies
  why A / C / G are not applicable (e.g., matrix-over-`ℂ` props
  are not `Decidable`).
- [ ] No test relies on internal namespace details that would
  break under a Phase 2 module split.

## 2. Module split conventions (per refactor plan v4 §3.1)

Module split criteria, all four required:

1. **Two or more clearly separable responsibilities.**
2. **Linear import DAG** after split (no cycles).
3. **Public API boundary** is clean.
4. **Tests already pin meaning** (depends on Phase 1 of the refactor).

### Façade module policy

Each split module retains a **façade module** that re-imports the
new files. This preserves backward-compatible import paths:

```
LatticeSystem/Quantum/NeelState.lean  -- façade (re-imports NeelState.*)
LatticeSystem/Quantum/NeelState/Definition.lean
LatticeSystem/Quantum/NeelState/Definition2D.lean
...
```

Old `import LatticeSystem.Quantum.NeelState` works unchanged.

### Façade variant: `Core.lean` sub-pattern (cycle avoidance)

When the original module's *bulk* stays put and only a *new
feature file* is extracted, the naive façade pattern would
require the new feature file to `import` the (now-trimmed)
original — and the original-as-façade would `import` the new
feature file. That is a cycle.

The fix: rename the (trimmed) original to `<Module>/Core.lean`
and create a fresh `<Module>.lean` façade that imports both
`<Module>/Core.lean` and the new feature file:

```
LatticeSystem/Quantum/SpinDot.lean             -- façade (~30 lines)
LatticeSystem/Quantum/SpinDot/Core.lean        -- bulk of original
LatticeSystem/Quantum/SpinDot/Hamiltonian.lean -- new feature
```

Now `Hamiltonian.lean` imports `SpinDot.Core` (not `SpinDot`),
and `SpinDot.lean` (façade) imports both. No cycle.

When to use: any time the new sub-file would need to import the
original file's content (which, if not renamed, would be the
façade).

Origin: PR #317 (SpinDot/Hamiltonian extraction). See
`docs/index.md` Phase 2 entries for cumulative usage.

### Façade variant: content + extensions (no façade)

When the parent file already contains the *core* concept and the
sub-file extends it with derived material (eigenvalue calculations,
companion-theorem families, additional algebraic structure that
doesn't fit the parent's responsibility), the parent stays as
content (not turned into a façade) and the sub-file imports the
parent. Downstream code that wants the extension content imports
the sub-file directly. The parent's module-header docstring **must**
list the extension sub-files in a table.

```
LatticeSystem/Quantum/HeisenbergChain.lean             -- content
LatticeSystem/Quantum/HeisenbergChain/Eigenvalues.lean -- extension
LatticeSystem/Quantum/HeisenbergChain/Gibbs.lean       -- extension
```

Now `Eigenvalues.lean` and `Gibbs.lean` import `HeisenbergChain`,
and `HeisenbergChain.lean` does **not** import them. Users who
just need the basic chain Hamiltonian + Hermiticity import
`Quantum.HeisenbergChain`; users who want the eigenvalue or Gibbs
companion family import the specific sub-file. This keeps the
parent file's import surface small.

When to use vs Core.lean sub-pattern: use *content + extensions*
when the parent's identity as a content-bearing module is more
important than convenience for downstream; use *Core.lean* when
you want a single import to give the full module surface.

Examples in this codebase:
- `TotalSpin.lean` + `TotalSpin/Casimir.lean` + `TotalSpin/Rotation.lean`
- `HeisenbergChain.lean` + `HeisenbergChain/Eigenvalues.lean`
  + `HeisenbergChain/Gibbs.lean`
- `SpinHalfRotation.lean` + `SpinHalfRotation/Conjugation.lean`
- `GibbsState.lean` + `GibbsState/Covariance.lean`
- `TimeReversalMulti.lean` + `TimeReversalMulti/SpinOpEquivariance.lean`
  + `TimeReversalMulti/Heisenberg.lean`

### Helper visibility

When extracting a helper lemma from one file to another, if the
helper is referenced by other downstream files, it must be lifted
from `private lemma` to `lemma` at extraction time. Document the
visibility change in the PR body.

Examples:
- PR #332 lifted `spinHalfSign_mul_antiparallel` from
  `private lemma` to public `theorem` so the new generic
  `inner_neelStateOf_szsz_neelStateOf_antiparallel` could use it.
  Also documented in `docs/index.md` per §6 below.
- During Phase 2 several `_aux` private lemmas had to be lifted
  when their parent file was split (e.g., `prod_alternating_neg_one`,
  `onSite_conjTranspose`). Each PR body explicitly documented the
  visibility change with a one-line "Visibility lift" note.

### Review check — module split

- [ ] All four split criteria justified in the PR description.
- [ ] Façade module retained at original path.
- [ ] No new module cycles introduced.
- [ ] Build-time delta recorded in the PR description.
- [ ] `[simp]` lemmas surveyed before split (cross-file
  dependencies on global simp set noted).

## 3. Generic / dedup conventions (per refactor plan v4 §3.2)

When consolidating duplicated patterns:

- **Public API uses set-based formulations** (e.g.,
  `(hpart : G.IsBipartiteWith s t)` with `s t : Set V`).
- **Internal lemmas use Bool-based formulations** (e.g.,
  `σ : V → Bool`) for `simp` ergonomics.
- Avoid abstract `IsBipartite` (Colorable 2) at entry points;
  prefer the explicit `IsBipartiteWith` witness form.

### Deprecation window

When generalising a definition, keep the **specialised version**
with a `@[deprecated <replacement> (since := "YYYY-MM-DD")]`
annotation. The deprecation window is at least one minor version
of the project (or one feature-cluster of subsequent PRs).
**Concrete current policy: 6 months from `since`** — see
[deprecations.html](deprecations.html) for the live tracking
table, removal-PR checklist, and current entries.

**Do not deprecate** until all bridge lemmas are in place and
verified.

When `@[deprecated]` cannot use a target name (because the
generic replacement requires a lambda argument the deprecation
syntax can't express), use the message form
`@[deprecated "use the generic ... with the ... indicator ..."
(since := "YYYY-MM-DD")]` to give callers a concrete migration
hint.

Internal companion theorems on the deprecated name continue to
exist (they are the migration scaffolding). Suppress the
deprecation linter for the block of companions immediately after
the deprecated declaration with a single
`set_option linter.deprecated false` and a comment explaining
why. Tests that exercise the deprecated names for backward-compat
coverage do the same at file level (test files exempt). The
deprecation warning text itself is captured by `#guard_msgs`
(method F) at the end of the test file.

### Review check — generic / dedup

- [ ] If deprecating, all bridge lemmas listed and merged first.
- [ ] `@[deprecated ... (since := ...)]` annotation present with
  explicit date.
- [ ] At least one `#guard_msgs` test pinning the deprecation
  warning text (per §1 method F).

## 4. Naming and docstring conventions (per refactor plan v4 §3.3)

- Theorem / definition names should aim for **≤ 60 characters**
  where readability is not sacrificed. Long names like
  `inner_basisVec_spinHalfDot_basisVec_antiparallel` (52 chars)
  are at the edge — acceptable only if no shorter alternative
  exists.
- Every `def` / `noncomputable def` / `theorem` / `lemma` must
  have a docstring.
- Tasaki-related results must cite the **equation number + page
  number** (e.g., `Tasaki §2.5 eq. (2.5.3), p. 37`).
- Comments inside proofs should be sparse: the proof itself, plus
  any **non-obvious WHY** (subtle invariant, hidden constraint,
  workaround). No redundant WHAT comments.

### Review check — naming & docstring

- [ ] Every new public name has a docstring.
- [ ] Tasaki / mathlib references are explicit (eq. number + page
  / mathlib symbol path).
- [ ] No theorem name > 80 characters (hard limit; soft limit 60).

## 5. Linter exception conventions (per refactor plan v4 §3.4)

- **No file-level `set_option linter.* false`** in source files
  (test files exempt only with comment justification).
- **In-line `set_option linter.flexible false in`** etc. are
  acceptable only when no proof-level rewrite achieves the goal;
  must include comment explaining why. Track every remaining
  per-theorem suppression in [`docs/deprecations.md`](deprecations.html)
  for transparency.
- `lake build` should produce **zero linter warnings** in steady
  state.

### Common rewrite patterns (use these instead of suppressing)

- **`linter.unusedSectionVars` / `linter.unusedDecidableInType`**:
  use `omit [Fintype Λ] in` or `omit [DecidableEq Λ] in` directly
  before the affected theorem, instead of a file-level
  `set_option`. The variable is still in scope as a `variable`
  declaration; `omit` just tells Lean not to auto-include it in
  this specific theorem's signature.
- **`linter.deprecated` triggered by internal companions on a
  deprecated definition**: place a single
  `set_option linter.deprecated false` after the deprecated
  declarations and before the companion theorems with a comment
  pointing to the deprecation rationale. The companions are
  migration scaffolding (see §3 "Deprecation window" above).
- **`linter.unusedSimpArgs`**: trim the dead arguments. If the
  argument is needed in some sub-cases of a `<;>`-chained simp
  but not others, accept the warning per-theorem with comment
  rather than refactoring into separate per-case proofs.
- **`linter.flexible` (`simp [...]` after `fin_cases`)**: ideally
  refactor to `simp only [...]` with the explicit lemma list
  (use `simp?` interactively to find it), or use `suffices` to
  state the simplified form. Per-theorem
  `set_option linter.flexible false in` with comment is
  acceptable as a temporary measure when interactive `simp?` is
  not available.

### Review check — linter

- [ ] No new `set_option linter.* false` introduced (without
  comment justification).
- [ ] Per-theorem `omit [...]` directives preferred over
  `set_option linter.unused* false`.
- [ ] If linter exception is removed elsewhere, build still passes.
- [ ] `lake build` warning count not increased (record before /
  after in PR description if relevant).
- [ ] New per-theorem suppressions added to `docs/deprecations.md`
  transparency table.

## 6. Public-doc synchronisation (CLAUDE.local.md, longstanding)

For every PR adding `def` / `theorem` / `lemma`, the same PR must:

1. Update `docs/index.md` table (Lean name + statement + file +
   citation).
2. Update Roadmap line if applicable.
3. Update `tex/proof-guide.tex` if relevant.

This is enforced by review and not by CI.

### Review check — public doc sync

- [ ] `docs/index.md` updated (or PR explicitly notes "no
  user-visible API").
- [ ] References to Tasaki / mathlib added where applicable.

## 6b. Verifying push before merge (incident-driven)

When chaining `git commit && git push` inside a single background
shell command, the `git push` step can fail silently — for
example due to a transient network error or an interrupted
background task — without aborting the chain or surfacing the
failure on subsequent commands. The PR API will then report a
**successful merge of an empty diff**, silently dropping the
intended changes.

### Review check — push verification

- [ ] After `git push` (especially in chained / background
  invocations), verify with `git ls-remote origin <branch>`
  that the remote SHA matches the local `HEAD`.
- [ ] After `gh pr merge`, run `git pull` on `main` and confirm
  the expected files are present (`ls` the new file paths).
- [ ] If a previous PR's diff is empty on inspection, **redo
  the PR** before claiming the underlying refactor done.

Origin: PR #311 (intended JordanWigner Operators extraction)
merged with empty diff; redone via PR #312.

## 7. Refactoring knowledge accumulation (this document)

This document is itself the **single source of truth** for
review criteria. When new conventions emerge (e.g., from a
Phase 2 split surfacing a new pitfall), the convention is added
here in the same PR that demonstrates it.

The goal is that **anyone reviewing a PR can apply this checklist
mechanically** and catch most regressions / drift.

### History
- **2026-05-23 (PR #3512)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground predecessor API after the lowerable and explicit lowerable
  positive-source final wrappers became a stable suffix.
  `Theorem23OutsideGroundPredecessor.lean` now keeps the source-weight and
  positive-source final-wrapper layers, while
  `Theorem23OutsideGroundPredecessorLowerable.lean` contains the lowerable and
  explicit lowerable final-wrapper suffix consumed by the real source-weight
  and raising-source downstream module. Focused checks cover the split
  predecessor modules and the predecessor-difference downstream module.
- **2026-05-23 (PR #3511)**: Refactored the Tasaki §2.5 Theorem 2.3
  base adjacent-energy API after the predicted-Casimir adjacent common-energy
  wrappers became a stable suffix. `Theorem23.lean` now keeps the site-sum and
  Casimir-nonvanishing adjacent common-energy links, while
  `Theorem23PredictedCasimirEnergy.lean` contains the predicted-Casimir
  adjacent common-energy and ladder-image packages consumed by the dominance
  and sector-existence layers. Focused checks cover the split base /
  predicted-Casimir modules and the dominance / sector-existence downstream
  consumers.
- **2026-05-23 (PR #3510)**: Refactored the Tasaki §2.5 Theorem 2.3 local
  predecessor-difference API after the unpacked real predecessor-difference
  callback adapters became a stable suffix. `Theorem23LocalDifference.lean`
  now keeps the sublattice coefficient and predecessor raising-source
  difference identities, while `Theorem23LocalDifferenceUnpacked.lean`
  contains the fully threaded unpacked callback adapters consumed by the
  interval and outside-ground wrappers. Focused checks cover the split local
  difference modules and the interval / outside-ground downstream consumers.
- **2026-05-23 (PR #3509)**: Refactored the Tasaki §2.5 Theorem 2.3
  cross-ladder final-wrapper API after the lowered-joint magnetization and
  lowered-joint cross-ladder wrappers became a stable suffix.
  `Theorem23OutsideGroundCrossLadder.lean` now keeps the sublattice-component,
  joint-component, and joint-coefficient final-wrapper layers, while
  `Theorem23OutsideGroundCrossLadderLoweredJoint.lean` contains the
  lowered-joint suffix. Focused checks cover the split cross-ladder modules and
  the unpacked / re-embedded downstream modules.
- **2026-05-23 (PR #3508)**: Refactored the Tasaki §2.5 Theorem 2.3
  interval-Casimir API after the global / sector minimality bridges and named
  callbacks became a stable suffix. `Theorem23IntervalCasimir.lean` now keeps
  the predicted-Casimir interval-chain wrappers (559 lines), while
  `Theorem23IntervalCasimirMinimality.lean` contains the minimality bridge and
  named callback suffix (152 lines). Focused checks cover the split
  interval-Casimir modules and the outside-ground / final downstream modules.
- **2026-05-23 (PR #3507)**: Refactored the Tasaki §2.5 Theorem 2.3
  predicted-ladder API after the real-scalar and predicted-Casimir transfer
  wrappers became a stable suffix. `Theorem23PredictedLadder.lean` now keeps
  the predicted-GS ladder closure, joint sublattice-Casimir structure, and
  lowered joint-magnetization package (437 lines), while
  `Theorem23PredictedLadderCasimirTransfer.lean` contains the
  scalar-cancellation and total-Casimir transfer suffix (249 lines). Focused
  checks cover the split predicted-ladder modules and the dominance /
  sector-existence downstream consumers.
- **2026-05-23 (PR #3505)**: Refactored the Tasaki §2.5 Theorem 2.3 final
  boundary API after the lowered-vector-Marshall final wrappers became a stable
  suffix. `Theorem23Final.lean` now keeps the outside-ground and direct
  lowered-site-sum final boundaries (536 lines), while
  `Theorem23FinalLoweredMarshall.lean` contains the lowered-vector-Marshall
  final suffix (256 lines). Focused checks cover the split final modules and
  downstream outside-ground predicted-GS documentation references.
- **2026-05-23 (PR #3506)**: Refactored the Tasaki §2.5 Theorem 2.3
  interval-chain API after the lowered-vector-Marshall and predicted-GS-aware
  sublattice-component interval wrappers became a stable suffix.
  `Theorem23Interval.lean` now keeps the named callbacks and direct
  interval-chain wrappers (543 lines), while
  `Theorem23IntervalPredictedGS.lean` contains the predicted-GS-aware interval
  suffix (242 lines). Focused checks cover the split interval modules and the
  joint interval downstream consumer.
- **2026-05-23 (PR #3504)**: Refactored the Tasaki §2.5 Theorem 2.3
  sector-existence API after the dominance-form successor/predecessor wrappers
  became a stable suffix. `Theorem23SectorExistence.lean` now keeps the final
  theorem proposition, per-sector Theorem 2.2 wrapper, and predicted-Casimir
  existential packages (483 lines), while
  `Theorem23SectorExistenceDominance.lean` contains the dominance-form
  sector-existence suffix (433 lines). Focused checks cover the split modules
  and interval-chain downstream modules.
- **2026-05-23 (PR #3503)**: Refactored the Tasaki §2.5 Theorem 2.3 local
  coefficient API after the predecessor raising-source wrappers became a stable
  suffix. `Theorem23LocalCoefficient.lean` now keeps the lowered signed and
  positive-source coefficient layers (457 lines), while
  `Theorem23LocalCoefficientRaisingSource.lean` contains the predecessor
  raising-source suffix (459 lines). Focused checks cover the split modules and
  the local-difference / outside-ground predecessor downstream modules.
- **2026-05-23 (PR #3502)**: Refactored the Tasaki §2.5 Theorem 2.3
  dominance API after the predicted-GS dominance wrappers became a stable
  suffix. `Theorem23Dominance.lean` now keeps the base dominance and
  predicted-Casimir dominance layers (568 lines), while
  `Theorem23DominancePredictedGS.lean` contains the predicted-GS dominance
  suffix (369 lines). Focused checks cover the split modules and the
  sector-existence downstream module.
- **2026-05-23 (PR #3501)**: Refactored the Tasaki §2.5 Theorem 2.3
  predicted-data API after the source-weight and lowering-predecessor
  bridges became a stable suffix. `Theorem23Predicted.lean` now keeps the
  predicted-Casimir, predicted-GS, and cross-ladder bridge layer (559 lines),
  while `Theorem23PredictedSourceWeight.lean` contains the diagonal
  source-weight and lowering-predecessor bridge suffix (384 lines). Focused
  checks cover the split modules and the interval / outside-ground downstream
  modules.
- **2026-05-23 (PR #3500)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground predecessor API after the real predecessor source-weight and
  raising-source final wrappers became a stable suffix.
  `Theorem23OutsideGroundPredecessor.lean` now keeps the source-weight,
  positive-source, lowerable, and explicit lowerable final-wrapper layers
  (589 lines), while `Theorem23OutsideGroundPredecessorRaising.lean` contains
  the real source-weight and raising-source final-wrapper suffix (357 lines).
  Focused checks cover the split modules and the predecessor-difference
  downstream module.
- **2026-05-23 (PR #3499)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground cross-ladder API after the unpacked lowered-joint
  cross-ladder final wrappers became a stable suffix.
  `Theorem23OutsideGroundCrossLadder.lean` now keeps the sublattice-component,
  joint-component, lowered-joint, and packed cross-ladder final-wrapper layers
  (683 lines), while `Theorem23OutsideGroundCrossLadderUnpacked.lean`
  contains the unpacked lowered-joint cross-ladder final-wrapper suffix
  (288 lines). Focused checks cover the split modules and the re-embedded
  downstream module.
- **2026-05-23 (PR #3498)**: Refactored the Tasaki §2.5 Theorem 2.3
  local-difference site-sum API after the strict off-`A` witness and lowered
  site-sum dominance bridges became a stable suffix.
  `Theorem23LocalDifference.lean` now keeps the predecessor-difference
  callback layer (689 lines), while `Theorem23LocalDifferenceSiteSum.lean`
  contains the lowered site-sum dominance suffix (280 lines). Focused checks
  cover the split modules and the Marshall wrapper downstream module.
- **2026-05-22 (PR #3497)**: Refactored the Tasaki §2.5 Theorem 2.3
  local lowering API after the single-site lowering component formula,
  Marshall-signed local identities, and off-`A`/on-`A` filtered sign-sum
  bounds became a stable suffix. `Theorem23Local.lean` now keeps the
  local ladder and site-sum expansion layer (440 lines), while
  `Theorem23LocalLowering.lean` contains the lowering component suffix
  (527 lines). Focused checks cover the split modules and the local
  coefficient downstream module.
- **2026-05-22 (PR #3496)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground predicted-Casimir API after the predicted-Casimir final
  wrappers became a stable suffix. `Theorem23OutsideGround.lean` now keeps
  the outside-sector lower-bound, sector-minimality, and common-energy
  final-packaging layers (580 lines), while
  `Theorem23OutsideGroundPredictedCasimir.lean` contains the
  predicted-Casimir final-wrapper suffix (512 lines). Focused checks cover
  the split modules and the predicted-GS downstream module.
- **2026-05-22 (PR #3495)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground predecessor-difference boundary API after the
  predecessor-difference and outside-sector final wrappers became a stable
  suffix. `Theorem23OutsideGroundPredecessor.lean` now keeps the
  predecessor-specialized source-weight and raising-source final-wrapper
  layers (924 lines), while
  `Theorem23OutsideGroundPredecessorDifference.lean` contains the
  predecessor-difference outside-sector boundary suffix (258 lines).
  Focused checks cover the split modules and the final downstream module.
- **2026-05-22 (PR #3494)**: Refactored the Tasaki §2.5 Theorem 2.3
  sector-existence interval API after the predicted-GS interval-chain wrappers
  became a stable suffix. `Theorem23SectorExistence.lean` now keeps the final
  statement, per-sector Theorem 2.2 reuse wrapper, and adjacent
  sector-existence wrappers (892 lines), while
  `Theorem23SectorExistenceInterval.lean` contains the predicted-GS
  interval-chain suffix (371 lines). Focused checks cover the split modules
  and the outside-ground / final downstream modules.
- **2026-05-22 (PR #3493)**: Refactored the Tasaki §2.5 Theorem 2.3
  interval-chain API after the joint-component and lowered-joint cross-ladder
  interval wrappers became a stable suffix. `Theorem23Interval.lean` now keeps
  the named callbacks plus the basic predecessor-difference, lowered-Marshall,
  and predicted-GS sublattice-component interval chains (805 lines), while
  `Theorem23IntervalJoint.lean` contains the joint-component and lowered-joint
  cross-ladder interval-wrapper suffix (474 lines). Focused checks cover the
  split modules and the interval-Casimir / outside-ground downstream modules.
- **2026-05-22 (PR #3492)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground cross-ladder final API after the re-embedded cross-ladder
  and source-weight final wrappers became a stable suffix.
  `Theorem23OutsideGroundCrossLadder.lean` now keeps the sublattice-component,
  joint-component, lowered-joint, and unpacked lowered-joint final-wrapper
  layers (948 lines), while `Theorem23OutsideGroundCrossLadderReembedded.lean`
  contains the re-embedded / source-weight final-wrapper suffix (466 lines).
  Focused checks cover the split modules and the predecessor / final
  downstream modules.
- **2026-05-22 (PR #3491)**: Refactored the Tasaki §2.5 Theorem 2.3
  outside-ground predicted-GS final API after the left-endpoint predicted-GS
  and lowered-Marshall final wrappers became a stable suffix.
  `Theorem23OutsideGround.lean` now keeps the outside-sector lower-bound,
  sector-minimality, and predicted-Casimir final-wrapper layers (1073 lines),
  while `Theorem23OutsideGroundPredictedGS.lean` contains the predicted-GS and
  lowered-Marshall final-wrapper suffix (488 lines). Focused checks cover the
  split modules and the cross-ladder / predecessor / final downstream modules.
- **2026-05-22 (PR #3490)**: Refactored the Tasaki §2.5 Theorem 2.3
  predicted ladder API after the predicted-GS ladder-closure,
  lowered-joint-subspace, and scalar-cancellation wrappers became a stable
  suffix. `Theorem23Predicted.lean` now keeps the predicted-Casimir,
  predicted-GS, cross-ladder, and source-weight bridge layer (919 lines),
  while `Theorem23PredictedLadder.lean` contains the ladder-closure and
  scalar-transfer suffix (662 lines). Focused checks cover the split modules,
  `Theorem23`, dominance, sector-existence, interval, and outside-ground
  downstream modules.
- **2026-05-22 (PR #3489)**: Refactored the Tasaki §2.5 Theorem 2.3
  common-energy API after the dominance and predicted-GS wrappers became a
  stable suffix. `Theorem23.lean` now keeps the site-sum and
  predicted-Casimir common-energy links (709 lines), while
  `Theorem23Dominance.lean` contains the dominance-form and predicted-GS
  common-energy wrappers (916 lines). Focused checks covered `Theorem23`,
  `Theorem23Dominance`, `Theorem23SectorExistence`, `Theorem23Interval`,
  `Theorem23IntervalCasimir`, the outside-ground downstream modules, and
  `LatticeSystem.lean`.
- **2026-05-21 (PR #3453)**: Refactor checkpoint after the 50
  post-#3402 Tasaki §2.5 Theorem 2.3 PRs (#3403--#3452).
  Build-speed evaluation for the active module:
  `lake env lean LatticeSystem/Quantum/SpinS/Theorem23.lean`
  completed in `real 33.36s` (`user 47.27s`, `sys 8.53s`);
  cached `lake build LatticeSystem.Quantum.SpinS.Theorem23`
  completed in `real 6.55s` (`user 2.00s`, `sys 3.40s`). No
  module split was performed: `Theorem23.lean` remains large and
  the final Theorem 2.3 adjacent-sector callback chain is still
  actively being collapsed through the predecessor difference and
  site-sum bridges. Splitting now would add import churn while the
  proof boundary is still moving; keep extraction deferred until the
  final adjacent-sector theorem wrapper lands.
- **2026-05-19 (PR #3402)**: Refactor checkpoint after the 20
  post-#3381 Tasaki §2.5 Theorem 2.3 feature PRs (#3382--#3401).
  Build-speed evaluation for the active module:
  `lake env lean LatticeSystem/Quantum/SpinS/Theorem23.lean`
  completed in `real 22.50s` (`user 34.64s`, `sys 4.83s`);
  cached `lake build LatticeSystem.Quantum.SpinS.Theorem23`
  completed in `real 3.55s` (`user 1.70s`, `sys 2.46s`). No
  module split was performed: `Theorem23.lean` is large
  (8837 lines), but the current proof still has one critical
  lowered-Marshall-positivity callback in flight, and the newest
  predicted-GS/Casimir bridges are tightly coupled to the adjacent
  sublattice-lowering chain. Splitting now would add import churn
  without a measured build-speed win. Revisit extraction after the
  lowered-sector Marshall positivity step lands.
- **2026-05-19 (PR #3381)**: Refactor checkpoint after the 20
  post-#3360 Tasaki §2.5 Theorem 2.3 feature PRs. Build-speed
  evaluation for the active module:
  `lake env lean LatticeSystem/Quantum/SpinS/Theorem23.lean`
  completed in `real 18.40s` (`user 19.60s`, `sys 4.23s`);
  cached `lake build LatticeSystem.Quantum.SpinS.Theorem23`
  completed in `real 3.60s` (`user 1.70s`, `sys 2.40s`). No
  module split was performed: `Theorem23.lean` is large
  (4400 lines), but the current proof is still in-flight and the
  latest additions are tightly coupled interval-chain wrappers.
  Splitting now would add import churn without a measured
  build-speed win. Revisit extraction once the remaining
  predicted-GS membership or lowered-dominance input is proved.
- **2026-04-22**: Initial version. Codifies the methods and
  conventions established in refactor plan v4 (Phase 0, Phase 1,
  early Phase 2). Origin: discussion during the §2.5 burst
  cleanup (#251–#278, then #279 + #280–#284 child issues).
- **2026-04-22 (PR #312)**: Added §6b (push verification) after
  PR #311 merged with empty diff because of a silent
  background-`git push` failure.
- **2026-04-22 / 2026-04-23 (Phase 3 #283 closed)**: Generic
  graph-centric Néel API (`neelStateOf`, `_antiparallel` per-bond
  primitives), Marshall sign generic + `@[deprecated]` window,
  2D / 3D Heisenberg companion family parity. PRs #329 / #330 /
  #331 / #332 / #333 / #334.
- **2026-04-23 (Phase 4 #284 substantially complete)**: Linter-warning
  cleanup (`lake build` is **zero warnings + zero errors**), §3
  expanded with concrete deprecation policy (6-month window from
  `since`, message-form when target name unavailable, internal
  companions linter-suppression pattern, `#guard_msgs` capture),
  §5 with common linter-rewrite patterns (per-theorem `omit`
  instead of file-level `set_option linter.unused*`, etc.), §2
  with content + extensions pattern + helper-visibility examples,
  §1 cross-reference to `Tests/Foundation.lean` POC, §6b
  push-verification origin, `docs/deprecations.md` Jekyll page
  (live tracking + removal checklist + remaining linter-
  suppression transparency), all parent module-header docstrings
  now document their extension sub-files (NeelState, SpinDot,
  JordanWigner facades; TotalSpin, HeisenbergChain,
  SpinHalfRotation, GibbsState, TimeReversalMulti content +
  extensions). PRs #335–#372.
