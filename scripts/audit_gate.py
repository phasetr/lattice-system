#!/usr/bin/env python3
"""audit_gate.py — deterministic hard gate for the recurring-pattern audit.

An advisory "a subagent points it out" check has no teeth. This gate is run from
the git pre-push hook and **blocks** newly-introduced recurring patterns
mechanically (no CI involved; local, grep-based, a few seconds).

Scope: `theorem`/`lemma` only. For Props, statement-equality implies duplication
(proof irrelevance) and off-critical-path means unreferenced — both decidable from
text. `def`/`abbrev` duplication depends on the *body* (same type, different value is
NOT a duplicate), which text cannot decide soundly; those are left to the
`lean-audit-tier1`/`tier2` subagents.

What it blocks (the *entity*, not the name — renaming never bypasses it):
  V1 decorative declaration: a zero-reference new theorem/lemma that is neither in
     the capstone allowlist nor @[simp] (i.e. off the critical path).
  V2 duplicate declaration: a new theorem/lemma whose statement (everything after
     the name, up to ':=') matches an existing one's statement, even under a
     different name (twin / doubled / mirror).
  V3 long line: an ADDED line over 100 columns (mathlib's longLine rule; URLs and
     imports exempt). The longLine syntax linter cannot be a lakefile build error
     downstream (it registers only after `import Mathlib`), so it is enforced here
     textually on the diff. Existing long lines are grandfathered (ratchet).

Non-blocking (report only; forced splits are disallowed):
  oversize files are listed but never affect the exit code.

usage:
  audit_gate.py --diff [BASE]   # new decls only (BASE=main); used by the hook.
  audit_gate.py --full          # whole repo (Tier-2 cleanup; report only).
"""
from __future__ import annotations
import os, re, subprocess, sys, glob
from collections import Counter

ROOT = os.environ.get("LEAN_SRC_ROOT", "LatticeSystem")
ALLOWLIST = os.environ.get(
    "AUDIT_CAPSTONE_ALLOWLIST", "scripts/audit/capstones.txt")
OVERSIZE = int(os.environ.get("AUDIT_OVERSIZE", "900"))

# Lean identifiers include Unicode (Greek, subscripts, primes): match a run of
# non-delimiter characters for the name, and a broad Unicode class for ref tokens.
DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*'
    r'(theorem|lemma)\s+([^\s:(){}\[\]⦃⦄]+)')
SIMP_RE = re.compile(r'@\[[^\]]*\bsimp\b[^\]]*\]')
_TOKEN_RE = re.compile(r"[A-Za-z_À-￿][\w'À-￿]*", re.UNICODE)


def _statement_end(text):
    """Index of the declaration-level ':=' or 'where' at bracket depth 0 (so a
    named argument like `(V := V)` inside the type does not end the statement).
    Returns len(text) if none is found."""
    depth = 0
    n = len(text)
    j = 0
    while j < n:
        c = text[j]
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            if text[j] == ':' and j + 1 < n and text[j + 1] == '=':
                return j
            if (text.startswith("where", j)
                    and (j == 0 or not (text[j - 1].isalnum() or text[j - 1] == '_'))
                    and (j + 5 >= n or not (text[j + 5].isalnum() or text[j + 5] == '_'))):
                return j
        j += 1
    return n


def lean_files():
    return sorted(glob.glob(f"{ROOT}/**/*.lean", recursive=True))


def parse_decls(files):
    """Return list of (name, statement, file, lineno, is_simp).

    `statement` is the text AFTER the keyword+name (binders + ':' + type), up to
    ':='/'where', whitespace-normalized — so two declarations with the same
    statement but different names produce the same string (V2 relies on this).
    """
    out = []
    for f in files:
        lines = open(f, encoding="utf-8").read().splitlines()
        in_block = 0  # depth inside /- ... -/ (incl. /-- and /-! ) comments
        for i, l in enumerate(lines):
            start_depth = in_block
            in_block = max(0, in_block + l.count("/-") - l.count("-/"))
            # Skip lines that begin inside a block comment or are line comments,
            # so prose like "theorem 11.5 states ..." is never read as a decl.
            if start_depth > 0 or l.lstrip().startswith("--"):
                continue
            m = DECL_RE.match(l)
            if not m:
                continue
            name = m.group(2)
            # @[simp] on the decl line or in the attribute lines just above it.
            is_simp = bool(SIMP_RE.search(l))
            j = i - 1
            while j >= 0 and (lines[j].strip().startswith("@[")
                              or lines[j].strip().endswith("-/")
                              or lines[j].strip() == ""):
                if SIMP_RE.search(lines[j]):
                    is_simp = True
                if not lines[j].strip().startswith("@["):
                    break
                j -= 1
            # Join the declaration text (name stripped from the first line) across
            # up to 60 lines, then cut at the top-level ':='/'where' at bracket
            # depth 0 — so a named argument like (V := V) in the type does not
            # truncate the statement. The statement excludes the name, so twins
            # with different names compare equal.
            raw = lines[i][m.end():]
            k = i + 1
            while _statement_end(raw) >= len(raw) and k < len(lines) and k - i <= 60:
                raw += "\n" + lines[k]
                k += 1
            stmt = re.sub(r'\s+', ' ', raw[:_statement_end(raw)]).strip()
            out.append((name, stmt, f, i + 1, is_simp))
    return out


def token_counter(blob):
    """Count identifier tokens across the blob in one pass (fast ref counting)."""
    return Counter(_TOKEN_RE.findall(blob))


def load_allowlist():
    if not os.path.exists(ALLOWLIST):
        return set()
    return {ln.strip() for ln in open(ALLOWLIST, encoding="utf-8")
            if ln.strip() and not ln.startswith("#")}


def strip_comments(text):
    """Remove /- ... -/ block comments and -- line comments (best effort)."""
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.DOTALL)
    return re.sub(r'--[^\n]*', ' ', text)


def resolve_base(base):
    """Resolve the diff base, failing closed (None) if nothing resolves.

    For the default 'main', prefer the upstream ref over a possibly stale local
    branch (else already-merged upstream decls look new). For an explicit base
    (a sha or a branch name), honor it first, then its origin/ form."""
    if base == "main":
        cands = (f"origin/{base}", "origin/main", base, "main")
    else:
        cands = (base, f"origin/{base}")
    for cand in cands:
        r = subprocess.run(["git", "rev-parse", "--verify", "--quiet", cand],
                           capture_output=True, text=True)
        if r.returncode == 0:
            return cand
    return None


def head_dirty_lean():
    """True if the working tree's *.lean differ from HEAD — including modified,
    staged, deleted AND untracked files (the glob later reads the working tree,
    so any of these would desync it from the pushed HEAD state)."""
    r = subprocess.run(["git", "status", "--porcelain", "--", "*.lean"],
                       capture_output=True, text=True)
    return bool(r.stdout.strip())


def added_decl_targets(base):
    """Return {(name, file, lineno)} of theorem/lemma declarations added vs `base`.

    Keyed on the exact (file, new-line) occurrence — not the name — so adding a
    `foo` never pulls a pre-existing same-named `foo` (other file, other namespace,
    or same file) into ratchet scope. Fails closed: a git error propagates.
    """
    diff = subprocess.run(
        ["git", "diff", "--unified=0", f"{base}...HEAD", "--", "*.lean"],
        capture_output=True, text=True, check=True).stdout
    targets = set()
    cur = None
    newline = 0
    for l in diff.splitlines():
        if l.startswith("+++ b/"):
            cur = l[6:].strip()
            continue
        if l.startswith("@@"):
            mh = re.search(r'\+(\d+)', l)
            newline = int(mh.group(1)) if mh else 0
            continue
        if l.startswith("+") and not l.startswith("+++"):
            m = DECL_RE.match(l[1:])
            if m and cur:
                targets.add((m.group(2), cur, newline))
            newline += 1
        elif l.startswith("-") and not l.startswith("---"):
            pass  # removed line: does not advance the new-file counter
    return targets


def added_long_lines(base, limit=100):
    """Return [(file, lineno, width)] for lines ADDED vs `base` over `limit` columns
    (codepoints). This is mathlib's longLine rule enforced textually in the hook:
    the longLine *syntax* linter cannot be a lakefile build error downstream (it is
    registered only after `import Mathlib`, so a leanOptions entry for it is silently
    ignored). URLs and import lines are exempt, as upstream. Ratchet: only added
    lines are checked, so existing long lines are grandfathered."""
    diff = subprocess.run(
        ["git", "diff", "--unified=0", f"{base}...HEAD", "--", "*.lean"],
        capture_output=True, text=True, check=True).stdout
    out = []
    cur = None
    newline = 0
    for l in diff.splitlines():
        if l.startswith("+++ b/"):
            cur = l[6:].strip()
            continue
        if l.startswith("@@"):
            mh = re.search(r'\+(\d+)', l)
            newline = int(mh.group(1)) if mh else 0
            continue
        if l.startswith("+") and not l.startswith("+++"):
            content = l[1:]
            if (len(content) > limit and cur
                    and "http" not in content
                    and not content.lstrip().startswith("import ")):
                out.append((cur, newline, len(content)))
            newline += 1
    return out


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "--diff"
    base = sys.argv[2] if len(sys.argv) > 2 else "main"

    files = lean_files()
    decls = parse_decls(files)
    # Reference counting ignores comments/docstrings (a name mentioned only in
    # prose is not a real reference).
    counts = token_counter(strip_comments(
        "\n".join(open(f, encoding="utf-8").read() for f in files)))
    allow = load_allowlist()

    if mode == "--diff":
        # Fail closed: never audit nothing because a ref/tree is missing.
        if head_dirty_lean():
            print("[audit-gate] BLOCKED: uncommitted *.lean changes. Commit them so"
                  " the gate audits the pushed (HEAD) state, then push.")
            return 2
        resolved = resolve_base(base)
        if resolved is None:
            print(f"[audit-gate] BLOCKED: base ref '{base}' (and origin/main) not"
                  " found; cannot determine new declarations.")
            return 2
        try:
            targets = added_decl_targets(resolved)  # {(name, file, lineno)}
            long_lines = added_long_lines(resolved)  # [(file, lineno, width)]
        except subprocess.CalledProcessError as e:
            print(f"[audit-gate] BLOCKED: git diff against '{resolved}' failed: {e}")
            return 2
        scope = [d for d in decls if (d[0], d[2], d[3]) in targets]
        scope_label = f"new decls vs {resolved}"
    else:
        scope = decls
        long_lines = []  # width is only ratcheted on the diff, not scanned whole-repo
        scope_label = "whole repo"

    # V1 decorative declaration (zero reference). Count references by the name's
    # last segment, so a qualified decl (e.g. Matrix.foo, referenced as `foo` or
    # `Matrix.foo`) is audited too; sharing a last segment only makes this more
    # conservative (never a false block), it does not open a bypass.
    def last_seg(n):
        return n.rsplit(".", 1)[-1]
    ndecl_last = Counter(last_seg(d[0]) for d in decls)
    v1 = []
    for name, stmt, f, ln, is_simp in scope:
        if is_simp or name in allow:
            continue
        seg = last_seg(name)
        if counts.get(seg, 0) - ndecl_last[seg] <= 0:
            v1.append((name, f, ln))

    # V2 duplicate declaration (statement match, name-independent).
    stmt_map = {}
    for name, stmt, f, ln, _ in decls:
        if stmt:
            stmt_map.setdefault(stmt, []).append((name, f, ln))
    v2 = []
    seen = set()
    for name, stmt, f, ln, _ in scope:
        if not stmt or stmt in seen or name in allow:
            continue
        others = [g for g in stmt_map.get(stmt, []) if (g[0], g[1], g[2]) != (name, f, ln)]
        if others:
            seen.add(stmt)
            v2.append(((name, f, ln), others))

    # Non-blocking oversize report.
    over = []
    for f in files:
        n = sum(1 for _ in open(f, encoding="utf-8"))
        if n > OVERSIZE:
            over.append((n, f))
    over.sort(reverse=True)

    print(f"[audit-gate] scope = {scope_label}; allowlist = {len(allow)} names")
    if over:
        print(f"[audit-gate] (non-blocking) oversize >{OVERSIZE}: "
              + ", ".join(f"{f}({n})" for n, f in over[:5]))

    fail = False
    if v1:
        fail = True
        print("\nV1 decorative declaration (zero-ref, not an allowlisted capstone):"
              " delete it or connect it to the critical path — renaming does nothing")
        for name, f, ln in v1:
            print(f"   {f}:{ln}  {name}")
        print(f"   -> a genuine capstone goes in {ALLOWLIST} (one name per line)")
    if v2:
        fail = True
        print("\nV2 duplicate declaration (matching statement = twin/doubled):"
              " merge into one and delete the other")
        for (name, f, ln), others in v2:
            loc = "; ".join(f"{o[0]}@{o[1]}:{o[2]}" for o in others[:3])
            print(f"   {f}:{ln}  {name}  ==  {loc}")
        print(f"   -> a confirmed non-duplicate (different ambient context) goes in"
              f" {ALLOWLIST}")
    if long_lines:
        fail = True
        print("\nV3 long line (>100 columns, added): wrap it (mathlib's longLine rule,"
              " enforced in this hook because it cannot be a lakefile build error)")
        for f, ln, w in long_lines:
            print(f"   {f}:{ln}  ({w} cols)")

    if fail and mode == "--diff":
        print("\n[audit-gate] BLOCKED. Resolve the entities above before pushing.")
        return 1
    if fail:  # --full is a report-only whole-repo scan; never changes exit code
        print("\n[audit-gate] (--full report only; not blocking)")
        return 0
    print("[audit-gate] OK (no new decorative/duplicate declarations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
