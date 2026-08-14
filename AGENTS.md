# AGENTS.md

Instructions for AI agents (Codex CLI, etc.) operating in this repository.

This file is auto-loaded by Codex CLI on every invocation. **Read it
end-to-end and follow it strictly** before doing anything else.

## Required startup sources

Before answering any request — review, edit, refactor, or otherwise — load
the following on-disk sources and obey their instructions:

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
     and cadence history (§A.4; `CLAUDE.local.md` supersedes any stale
     threshold text there, and the current threshold is 20 PRs)

3. The committed project documents:
   - `README.md` — project introduction
   - `docs/index.md` — concise public-facing landing page
   - `formalization-status/v1/` — prototype structured-status contract and samples
   - `docs/formalization/legacy/` — authoritative theorem/status catalogue
   - `tex/proof-guide.tex` — public-facing mathematical exposition

## Active-work state

Records have three distinct roles, and only one is authoritative for
restarting work:

1. **`.self-local/active/<topic>.md` (gitignored, private) is the sole
   restart authority.** Keep normalized CURRENT facts only: state,
   decisions, verification outcome, and the next action.
2. **The public GitHub Issue/PR body is a minimal pointer.** It carries
   only the allowlist: brief objective; strict in-scope and out-of-scope;
   current state; exactly one exact Next action; acceptance-criteria
   summary; public Issue/PR links. Anything else is forbidden, including
   summarized, paraphrased, or quoted forms. Update by rewriting the
   current state, never by appending chronology.
3. **`.self-local/issues/<number>.md` mirrors that minimal public body
   verbatim.** It is a copy: neither a place for detail nor a restart
   input.

Never record, publicly or privately, conversation transcripts, quotations,
approval dialogue or its chronology, personal, credential, or security
data, or internal agent, tool, command, log, sandbox, permission, or
process detail. Record authorization only as normalized current state
(for example "Exact scope approved"), never its source dialogue.

Remove disallowed content instead of correcting it by appending.
Sanitization overrides append-only, immutability, pre-backup, and
preservation defaults; never copy removed content into a backup, report,
temporary file, draft, or reply. Inventory and result records may carry
identifiers, category labels, and counts only. Platform edit history may
retain earlier revisions; report that limitation without quoting content
and escalate when a true purge is required.

TaskLists, handover notes, generated captures, transcripts, reports, and
chronological records are never authority for current state or restart.

## Resume order

When starting or resuming work, read in this order and resolve conflicts
in the same order:

1. the private active record `.self-local/active/<topic>.md`;
2. the current `git log` and working state of `main`;
3. the minimal current state on the public Issue/PR.

Then update the private active record first, regenerate the minimal
public snapshot from it, and finally the mirror. Do not create an
alternative checkpoint and do not infer current work from a historical
handover.

## Hard rules (echoed from `CLAUDE.local.md`; obey even if it is missing)

- **All changes go through pull requests.** Never push directly to `main`.
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
- **Use sandbox-stable command forms before giving up.** For TeX builds,
  route LuaTeX caches to writable roots on the first attempt and do not
  preemptively request escalation:
  `env TEXMFSYSVAR=/private/tmp/texmf-sysvar TEXMFVAR=/private/tmp/texmf-var TEXMFCONFIG=/private/tmp/texmf-config TEXMFCACHE=/private/tmp/texmf-cache latexmk -g -lualatex <file>.tex`.
  Use the same `/private/tmp` cache paths from `.self-local/tex/`; avoid
  repo-local relative cache paths for LuaTeX because `luaotfload` may fail
  to discover them. If a TeX build still reports `no writeable cache path`,
  first fix `TEXMFSYSVAR` / `TEXMFCACHE` / absolute cache paths and rerun
  sandboxed instead of stopping for a TeX approval prompt.
  For `tex/proof-guide.tex`, use `latexmk -g -pdf proof-guide.tex` as the
  routine verification command: the document does not use Lua-only packages,
  and TeX Live 2026 LuaHBTeX/luaotfload can mis-detect writable cache
  directories even when `TEXMFCACHE` resolves to a writable absolute path.
  Keep the LuaLaTeX cache command above for TeX files that actually depend on
  LuaTeX or LuaTeX-ja.
  Codex/Codex CLI agents must run `codex exec ...` cross-checks with the
  environment's escalation mechanism on the first attempt, not after a failed
  sandboxed attempt, and persist a scoped `codex exec` approval rule when
  available. Avoid shell redirection and pipes in `codex exec` commands so
  the persistent rule can match `codex exec` broadly. If GitHub CLI bodies
  contain backticks, use single-quoted bodies or `--body-file` so the shell
  does not execute the backtick content.
- **Codex/Codex CLI only: do not ask conversational permission for routine
  workflow commands.** Claude Code already auto-executes routine commands;
  this rule is for Codex agents that otherwise tend to stop for redundant
  permission. For normal PR work, GitHub CLI updates, TeX builds, codex
  cross-checks, one-shot CI checks, and sandbox/network retries, execute
  directly. If the environment requires escalation, use the escalation
  mechanism immediately with a concise justification and, when available, a
  narrow persistent prefix rule. Direct user questions are reserved for
  destructive git operations, repository settings changes, or genuine
  specification ambiguities that cannot be resolved from local documents.
- **Codex/Codex CLI only: run all `gh ...` commands through escalation on the
  first attempt.** GitHub CLI operations are routine workflow commands for
  this repository: PR create/view/edit/list/checks/merge, issue
  view/list/edit/comment, run view/list, repo view/sync, labels, and similar
  GitHub metadata operations. Use the environment's escalation mechanism
  immediately for every `gh ...` command and persist a `gh` prefix rule when
  available, instead of first trying a sandboxed network command that is
  likely to fail. This rule does not authorize destructive git operations or
  GitHub repository settings changes; those still require explicit approval
  when the environment or repository policy demands it.
- **Codex/Codex CLI only: keep `gh ...` command strings prefix-rule friendly.**
  Do not wrap routine GitHub CLI operations in shell redirection (`>`, `>>`,
  `<`), pipes (`|`), command substitutions (`$(...)`), or wildcard-heavy shell
  forms. Those shell features prevent the environment from matching a broad
  `gh` prefix rule and cause repeated approval stops. Run commands such as
  `gh issue view 412 --json body --jq .body` directly, then create or edit
  any local body files separately with the normal file-editing tools. Prefer
  `--body-file` for GitHub writes once the file already exists.
- **Codex/Codex CLI only: keep workflow temporary files repo-local.** Do not
  write PR bodies, Issue bodies, Issue comments, review prompts, or similar
  routine workflow scratch files to `/private/tmp`. Put them under the
  gitignored repo-local directory `.self-local/tmp/`; create it with
  `mkdir -p .self-local/tmp` and continue without asking if it is missing.
  `/private/tmp` is reserved only for tool caches such as the TeX
  `TEXMFVAR` / `TEXMFCONFIG` directories described above.
- **Codex cross-check is a single review at squash-merge time**, not
  per-commit / per-CI.
- **All committed prose (commit messages, PR titles/bodies, doc strings,
  README, docs/, tex/) must be in English.** Conversational replies to
  the user remain in 日本語.
- **Add a doc comment to every `def` / `theorem` / `lemma` / `structure`,
  including `private` ones. Maintain zero linter warnings.**
- **Updating the authoritative record under `docs/formalization/legacy/` and
  `tex/proof-guide.tex`** in the same PR is mandatory whenever a new `def` /
  `theorem` / `lemma` is committed. `docs/index.md` is the landing page;
  `formalization-status/v1/` remains a non-authoritative prototype until a
  separately reviewed catalogue cutover.
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
codex exec '<PR number, what changed, what to verify>'
```

Codex/Codex CLI agents must run that command through the environment's
escalation mechanism on the first attempt, as described above, and should not
wrap it in shell redirection or pipes.

Keep reviews terse:
1. Confirm the named theorems exist and match the claimed values.
2. Confirm the proofs are reasonable (`unfold; push_cast; ring`,
   structural induction, etc.).
3. Run `lake env lean <single file>` if the change is local to one file.
4. Flag any missing or stale row in the authoritative legacy catalogue,
   including its exact Lean name, statement, source path, and citation.

Do not run `lake build` of the whole project unless the change spans
many files. The 20-PR refactor cadence keeps single-file build times
under ~13 s for the numerics modules.
