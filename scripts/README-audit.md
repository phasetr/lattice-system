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
scripts/audit-helpers.sh oversize 700       # files over a line threshold
```

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
