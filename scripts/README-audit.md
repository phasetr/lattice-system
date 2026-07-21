# Recurring-pattern audit gate

Deterministic, **local** enforcement that blocks newly-introduced abnormal code.
CI is intentionally not used (it is slow); this runs on `git push` in a few seconds.

What is forbidden is the **entity**, not the name (renaming does not help). The
deterministic gate covers `theorem`/`lemma` only (for Props, statement-equality
implies duplication by proof irrelevance, and off-critical-path means unreferenced —
both decidable from text):

- **Decorative declaration**: a `theorem`/`lemma` referenced nowhere
  (off the critical path), not in the capstone allowlist, not `@[simp]`.
- **Duplicate declaration**: a `theorem`/`lemma` whose statement matches an existing
  one (twin / doubled). Detected textually.
- **Long line**: an added line over 100 columns (mathlib's longLine rule; URLs and
  imports exempt). Enforced in this hook, not as a build error: the longLine syntax
  linter registers only after `import Mathlib`, so a lakefile option for it is silently
  ignored (verified). Existing long lines are grandfathered (ratchet).
- **Newly unreachable module**: a module the build roots reached at the base ref but
  no longer reach at `HEAD` (see below).

## Build-root reachability

`lakefile.toml`'s `defaultTargets` (`LatticeSystem`, `LatticeSystem.Tests`) carry no
glob, so lake compiles exactly the **import-closure of those roots**. A module outside
that closure is not compiled at all: it cannot emit a warning, `#print axioms` never
reaches it, and a `sorry` in it would not surface — while the build stays green.

That is not hypothetical. In PR #5099 one deleted `import` line (the only in-repo
reference to the module) dropped `AnisotropicHeisenbergCrossingDualSectorGroundExplicit`
and `AnisotropicHeisenbergParametricGapCrossingGeneric` out of the build. Both are
book results written up in `docs/index.md` (Tasaki §2.5 Theorem 2.4, obligation (2)).
Neither the build, nor V1/V2/V3, nor codex caught it; a human reviewer did.

The gate parses the roots out of `lakefile.toml` (never hardcoded), walks the `import`
graph from them at **both** the base ref and `HEAD`, and blocks any module that was
reachable at base and is not at `HEAD`. A module added by the diff and left unwired is
caught too (unreachable at `HEAD`, absent at base).

Each side uses **its own lakefile's roots** — the base closure with the base ref's
`defaultTargets`, the `HEAD` closure with `HEAD`'s. Sharing `HEAD`'s roots would make
*deleting a build root* invisible, which is the strictly worse form of #5099: dropping
`LatticeSystem.Tests` from `defaultTargets` orphans 1,198 modules in one line.

Unreadable roots **fail closed** (`BLOCKED`, exit 2), exactly like an unresolvable base
ref. An empty root list would make every module trivially unreachable-at-both-ends and
turn V4 into a silent no-op, i.e. a gate that always passes — worse than no gate. This
covers a deleted `defaultTargets` line and a migration to `lakefile.lean` (the Lean DSL
is not parsed; a `.lean` lakefile always fails closed, even if its text happens to match
the TOML shape). Both TOML quote styles are understood, so the alternative spelling
still reads the roots rather than falling back to the no-op.

The lakefile is looked up in **lake's own precedence order — `lakefile.lean` first**
(Lean v4.29.0, `lake/Lake/Load/Package.lean:68-76`: with both present lake logs
"are both present; using lakefile.lean"). Reading the TOML first would let an added
`.lean` config silently re-target the build while the gate went on reporting against
roots lake no longer uses.

The lakefile also counts as a source for the "uncommitted changes" fail-closed rule:
V4 reads the roots from the working tree, so an uncommitted `defaultTargets` edit would
otherwise excuse an orphan that the pushed state still has.

The baseline is **recomputed from the base ref every run**, not stored in a file: a
committed orphan list goes stale on the first rewire or rename, and a stale baseline
either blocks legitimate work or quietly stops blocking. Recomputing keeps the check a
ratchet — existing orphans never fire, and the bar rises automatically as debt is paid.

The base-ref graph is read straight out of git (`ls-tree` + `cat-file --batch`, both
checked for failure), so there is no checkout and no temp tree. Imports inside block or
line comments are not edges.

`--full` lists every module unreachable from the roots (report only, never blocking).

`def`/`abbrev` duplication depends on the body (same type but different value is not a
duplicate), which text cannot decide soundly, and α-renamed duplicates are also
textual blind spots — both are left to the `lean-audit-tier1`/`tier2` subagents.
The `suffix-hints` helper scans `def` too, but only as a lead to investigate.

File-size is reported but never blocks (no forced splits).

`lint` debt (long lines, missing doc comments, unused vars, deprecation) is enforced
separately as **build errors** via `warningAsError = true` (+ `linter.style.longLine`,
`linter.docBlame`) in `lakefile.toml` — not by this gate.

## One-time activation (per clone)

```sh
git config core.hooksPath .githooks
```

That points git at the tracked `.githooks/pre-push`, which runs the gate in ratchet
mode (`--diff main`): existing debt is grandfathered, only new violations block.

The gate audits the committed (`HEAD`) state that is being pushed, so it fails closed
if there are uncommitted `*.lean` changes (commit them first) or if the base ref
cannot be resolved (it falls back to `origin/main`, else blocks).

## Manual use

```sh
python3 scripts/audit_gate.py --diff main   # new decls vs main (what the hook runs)
python3 scripts/audit_gate.py --full        # whole-repo report (Tier-2 cleanup)
scripts/audit-helpers.sh dead-decls         # zero-reference theorem/lemma candidates
scripts/audit-helpers.sh undocumented-dead [FILE|-]   # of those, the ones the
                                            # docs do not record ('-' = stdin)
scripts/audit-helpers.sh oversize 700       # files over a line threshold
```

## Documented-name matching (compressed family notation)

A zero-reference declaration that `docs/index.md` / `tex/proof-guide.tex` write up
(with its Tasaki equation number) is a book-facing result, not dead code. Both
documents record whole families in a **compressed notation**, so matching them with
an exact grep is wrong — in the Wave-1 sweep it mis-reported 49 of 50 candidates as
undocumented, and deleting them would have erased Tasaki Problem 2.2.a / 2.2.b.

`scripts/audit/docs_names.py` expands the four compressions the two documents
actually use (TeX `\_ \{ \}` escaping and `\texttt{...}` are undone first):

| notation | example | expands to |
|---|---|---|
| brace | `spinOnePiRot{1,2,3}_sq` | `spinOnePiRot1_sq`, `…2_sq`, `…3_sq` (cross product over several groups; an empty alternative as in `_{,complement_}` is allowed) |
| slash | `spinOneOpPlus/Minus_conjTranspose`, `spinHalfRot1/2/3_pi` | both members. The left side is kept verbatim; the right side is an abbreviation, so the left is cut exactly where the right continues it — before a trailing digit run for `1/2/3`, before the trailing camelCase segment for `Plus/Minus`, after the last `_` for `pos/neg`. `L` + the right side from its first `_` on covers the other direction |
| continuation | `complexConjugationSpinHalf_sq` / `_add`, `tJConfigOf_tJSiteHop_up/_down` | a code span (or slash side) starting with `_` continues the previous name, replacing whole `_`-segments; the number replaced varies, so every `_`-boundary head is tried (never a cut inside a segment). A continuation that also *ends* with `_` is an infix replacement and keeps the base's tail (`…_horizontal_adjacent_eq_…` / `_vertical_adjacent_`) |
| star | `spinOnePiRot{1,2,3}_comm_*` | prefix match — only when the `*` follows `_` or `.`, so prose/markdown `word*` is not a family. The anchoring separator is also dropped from the prefix, because `spinHalfOp_*` is how the docs abbreviate `spinHalfOp1/2/3` |

Guards against over-broad readings (the index feeds a *deletion* sweep, so a
manufactured name is as harmful as a missed one): a name enters the index only if
it is identifier-shaped (`_` or a camelCase hump), so prose words do not;
a slash token without `_` is a path or prose (`AngularMomentum/Ladder`,
`add/sub`); a wildcard right side is never read standalone (`…/sub_*` must not
yield `sub_*`); and neither a slash nor a continuation may cut inside a name
segment (`spinHalfRot1/2/3_…` must not yield `spin2_*`, `rightGauge_conj_…` must
not be cut down to `right`). Every notation and every crossing of two notations
has a positive and a negative case in the test file. Namespace wildcards
(`CollatzWielandt.*`) only match qualified names, so they do not cover the bare
last segments the sweep works with.

```sh
python3 scripts/audit/docs_names.py --expand          # the whole documented index
python3 scripts/audit/docs_names.py --check NAME...   # documented / undocumented
python3 scripts/audit/docs_names.py --filter LIST|-   # drop documented lines
python3 scripts/audit/test_docs_names.py              # expansion regression tests
python3 scripts/audit/test_audit_gate_reachability.py # V4 reachability regression tests
                                            # (drives the gate's exit code in a
                                            # throwaway git worktree; ~45 s)
```

The two document paths are resolved against the **repo root**, not the CWD, and a
missing document (or an empty index) is a hard error — silently indexing nothing
would report every declaration as undocumented, i.e. as deletable.

This affects only the **sweep's** classification; `audit_gate.py`'s V1/V2/V3
decisions are untouched (the gate exempts capstones via
`scripts/audit/capstones.txt`, not via the docs).

`scripts/audit/capstones.txt` is the allowlist (one name per line) that exempts a name
from **both** checks: genuine zero-reference book theorems (V1), and declarations a
reviewer has confirmed are not real duplicates despite a matching displayed statement
(V2, e.g. distinct ambient `variable` context the textual gate cannot see). Everything
else zero-referenced is decorative; every matching statement is a duplicate.

## Limitations (heuristic, by design)

The gate is a fast text scan, not Lean name resolution, so it is deliberately
conservative — it must never block legitimate work:

- V1 reference counting keys on the declaration's **last name segment** over a
  comment-stripped blob. A dead qualified decl (`Matrix.foo`) whose last segment
  (`foo`) is also used elsewhere is therefore *not* flagged. This biases toward
  false negatives (a missed dead decl), never false positives.
- V2 duplicate detection is textual (`α`-renamed binders that differ in spelling
  are not matched).
- V4 reachability treats `LatticeSystem.Tests` as a root because lake does, so a
  production module kept alive only by a test import counts as reachable. That is the
  build's own notion, not a statement that the wiring is good; the test-only cases are
  the `lean-audit-tier2` subagent's job.
- V4 reads plain `import`; `public import` (Lean's module system) is not yet an edge.
  The repo has none today, and adopting it needs a matching change here first —
  otherwise a module reachable only through a `public import` is unreachable at *both*
  refs and so permanently grandfathered. Tracked in #5098.
- V4's base is the resolved base ref (`origin/main`), not the merge base that V1–V3's
  three-dot diff uses. On a branch behind `main` this can flag a module `main` orphaned
  independently; the reverse direction is grandfathered, so it never passes silently.
  Tracked in #5098.
- Like V1/V2, V4 is vacuous if the source tree indexes to nothing (a mistyped
  `LEAN_SRC_ROOT`, or deleting the whole root directory): with an empty HEAD graph
  there is no module left to call unreachable. The gate reports on the tree it can see.

These residual cases are the job of the `lean-audit-tier1`/`tier2` subagents, which
read statements and resolve names; the gate is the cheap deterministic first line.
