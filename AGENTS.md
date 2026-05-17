# AGENTS.md

Instructions for AI agents (Codex CLI, etc.) operating in this repository.

This file is auto-loaded by Codex CLI on every invocation. **Read it
end-to-end and follow it strictly** before doing anything else.

## Always-read files (in this order)

Before answering any request — review, edit, refactor, or otherwise — load
the following on-disk files and obey their instructions:

1. **`CLAUDE.local.md`** at the repository root. This is the authoritative
   source for project conventions, workflow rules, approval boundaries,
   document-language requirements, the 20-PR refactor cadence, the no-CI-watch
   rule, the multi-PR-issue-tracking rule, the codex-cross-check rule, etc.
   It is gitignored (a personal file of the author), so other clones may not
   have it; if it is absent, fall back to the documents in step 2.

2. The documents `CLAUDE.local.md` references (all under `.self-local/`,
   gitignored personal notes — read whichever exist):
   - `.self-local/docs/1-requirements.md` — requirements
   - `.self-local/docs/2-basic-design.md` — basic design
   - `.self-local/docs/3-testing-strategy.md` — testing strategy
   - `.self-local/docs/4-workflow.md` — workflow (PR/branch/merge)
   - `.self-local/docs/5-coding-conventions.md` — coding conventions
   - `.self-local/docs/refactoring-plan-2026-04-22.md` — refactor plan
     and the 20-PR cadence history (§A.4)
   - `.self-local/SESSION-RESUME.md` — current in-flight state and the
     "Next concrete step" marker; **read first when resuming**

3. The committed project documents:
   - `README.md` — project introduction
   - `docs/index.md` — public-facing roadmap and theorem index
   - `tex/proof-guide.tex` — public-facing mathematical exposition

## Hard rules (echoed from `CLAUDE.local.md`; obey even if it is missing)

- **All changes go through pull requests.** Never push directly to `main`.
- **Do not stop at a refactor-checkpoint resume just because a prior note says
  the user should run `/clear`.** If the execution environment exposes a
  callable session-clear operation, the agent must perform it. If it does not,
  the agent must emulate a fresh session by rereading `CLAUDE.local.md`,
  `.self-local/SESSION-RESUME.md`, the referenced `.self-local/docs/*` files,
  `README.md`, `docs/index.md`, and `tex/proof-guide.tex`, then continue from
  the recorded "Next concrete step" without asking the user to run `/clear`.
- **Do not skip pre-commit / pre-push hooks** (`--no-verify` etc.) unless
  the user explicitly asks for it.
- **Do not run destructive git operations** (`push --force`, `reset --hard`,
  `branch -D`, etc.) without explicit user approval.
- **One PR per textbook theorem**, not per small lemma. Tasaki Theorem N.M
  ⇒ multiple commits on one branch ⇒ one PR. Per-lemma PRs are forbidden
  even when bulk-pushed.
- **Multi-PR threads need a tracking GitHub Issue created _before_ the
  first PR.** Reference `#issue` in every PR body and title.
- **20-PR refactor cadence**: every 20 merged PRs since the most recent
  refactor PR, the next merge must be a refactor PR (build-speed
  evaluation required, even if "evaluate-only").
- **No CI watching**: do not poll `gh pr checks --watch` or sleep waiting
  for CI. Push, run codex review in the background, then check CI once
  before merging.
- **Codex cross-check is a single review at squash-merge time**, not
  per-commit / per-CI.
- **All committed prose (commit messages, PR titles/bodies, doc strings,
  README, docs/, tex/) must be in English.** Conversational replies to
  the user remain in 日本語.
- **Add a doc comment to every `def` / `theorem` / `lemma` / `structure`,
  including `private` ones. Maintain zero linter warnings.**
- **Updating `docs/index.md` and `tex/proof-guide.tex`** in the same PR
  is mandatory whenever a new `def` / `theorem` / `lemma` is committed.
- **Citations** must include edition, equation/theorem number, and page
  number when referring to a textbook.

## Response style

- Reply to the user in 日本語. Code, comments, and committed prose remain
  in English.
- Cite Lean code with `path:line` so the user can navigate (e.g.
  `LatticeSystem/Quantum/SpinS/SingleClusterHamiltonian.lean:120`).
- Do not invent file paths, theorem names, PR numbers, or issue numbers.
  Verify with `git`, `gh`, or `grep` before claiming.
- If a constraint in `CLAUDE.local.md` and a user prompt conflict, surface
  the conflict explicitly rather than silently picking one.

## Codex review prompts (when invoked as reviewer)

Typical pattern from this repo:

```
codex exec '<PR number, what changed, what to verify>' < /dev/null 2>&1 | tail -10
```

Keep reviews terse:
1. Confirm the named theorems exist and match the claimed values.
2. Confirm the proofs are reasonable (`unfold; push_cast; ring`,
   structural induction, etc.).
3. Run `lake env lean <single file>` if the change is local to one file.
4. Flag any missing `docs/index.md` row update or stale `(PR pending)`
   tag (the author updates these in the next PR — that is expected).

Do not run `lake build` of the whole project unless the change spans
many files. The 20-PR refactor cadence keeps single-file build times
under ~13 s for the numerics modules.
