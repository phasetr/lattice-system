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
| slash | `spinOneOpPlus/Minus_conjTranspose` | `spinOneOpPlus_conjTranspose`, `spinOneOpMinus_conjTranspose` (the abbreviated side is restored by cutting at `_`/camelCase boundaries) |
| continuation | `complexConjugationSpinHalf_sq` / `_add` | a following code span starting with `_` continues the previous one, replacing its trailing segments. A continuation that also *ends* with `_` is an infix replacement and keeps the base's tail (`…_horizontal_adjacent_eq_…` / `_vertical_adjacent_`) |
| star | `spinOnePiRot{1,2,3}_comm_*` | prefix match — only when the `*` follows `_` or `.`, so prose/markdown `word*` is not a family |

Guards against over-broad readings (the index feeds a *deletion* sweep, so a
manufactured name is as harmful as a missed one): a name enters the index only if
it is identifier-shaped (`_` or a camelCase hump), so prose words do not;
a slash token without `_` is a path or prose (`AngularMomentum/Ladder`,
`add/sub`); a wildcard right side is never read standalone (`…/sub_*` must not
yield `sub_*`); and a continuation head must itself be identifier-shaped
(`rightGauge_conj_…` must not be cut down to `right`). Namespace wildcards
(`CollatzWielandt.*`) only match qualified names, so they do not cover the bare
last segments the sweep works with.

```sh
python3 scripts/audit/docs_names.py --expand          # the whole documented index
python3 scripts/audit/docs_names.py --check NAME...   # documented / undocumented
python3 scripts/audit/docs_names.py --filter LIST|-   # drop documented lines
python3 scripts/audit/test_docs_names.py              # expansion regression tests
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

These residual cases are the job of the `lean-audit-tier1`/`tier2` subagents, which
read statements and resolve names; the gate is the cheap deterministic first line.
