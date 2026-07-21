#!/usr/bin/env python3
r"""docs_names.py — which declaration names are recorded in the public docs.

The dead-declaration sweep asks "is this zero-reference decl written up in
`docs/index.md` / `tex/proof-guide.tex`?".  Answering that with an exact-match
grep is **wrong**: both documents record whole declaration families in a
compressed notation, so an exact grep reports a documented decl as undocumented.
That mis-classification is not academic — in the Wave-1 sweep 49 of 50
"undocumented" candidates were in fact book-facing results written up with their
Tasaki equation numbers (`spinOneRot{1,2,3}_zero`, Problem 2.1.c, ...).

Only the four compressions that the two documents actually use are expanded
(verified by grepping them; this is deliberately not a general expander):

  brace   `spinOnePiRot{1,2,3}_sq`      -> spinOnePiRot1_sq, ...2_sq, ...3_sq
          `all{Up,Down}_neelStateOf_{,complement_}orthogonal`  (empty alternative
          and several braces per token are used, so the cross product is taken)
  slash   `spinOneOpPlus/Minus_conjTranspose`
                                        -> spinOneOpPlus_conjTranspose,
                                           spinOneOpMinus_conjTranspose
          the right side is an abbreviated fragment; the shared head/tail is
          restored by cutting only at name boundaries (`_` or a camelCase hump).
  cont.   `complexConjugationSpinHalf_sq` / `_add` / `_smul`
                                        -> complexConjugationSpinHalf_add, ...
          a following code span that STARTS with `_` continues the previous one:
          its own tail segments are replaced.  A continuation that also ENDS with
          `_` is an infix replacement and keeps the base's tail
          (`..._horizontal_adjacent_eq_...` / `_vertical_adjacent_`).
  star    `spinOnePiRot{1,2,3}_comm_*`  -> prefix match `spinOnePiRot1_comm_`, ...
          honoured only when the `*` follows `_` or `.`; a bare `word*` is prose
          or markdown emphasis, never a family.

TeX escaping (`\_`, `\{`, `\}`) is undone and control sequences are dropped first.
Two filters keep prose out of the index: a name is recorded only if it is
identifier-shaped (contains `_` or a camelCase hump), and a slash token without
`_` is treated as a path or prose (`AngularMomentum/Ladder`, `add/sub`).

usage:
  docs_names.py --expand              # every documented name (one per line)
  docs_names.py --filter FILE         # keep the lines of FILE whose name is NOT
                                      # documented ('-' = stdin; name = last field)
  docs_names.py --check NAME...       # per name: 'documented' / 'undocumented'
"""
from __future__ import annotations
import os
import re
import sys

# Resolved against the repo root (this file lives in <root>/scripts/audit/), never
# against the caller's CWD: a wrong CWD must not silently yield an empty index,
# which would report every declaration as undocumented — i.e. as deletable.
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))
DOCS = [os.path.join(REPO_ROOT, p)
        for p in os.environ.get(
            "AUDIT_DOCS", "docs/index.md:tex/proof-guide.tex").split(":")]

# A token is an identifier-ish run that may carry the compressions above. The `/`
# is absorbed only when it directly abuts identifier characters, so the
# continuation notation (a closing delimiter before the slash) is left to CONT_RE.
TOKEN_RE = re.compile(
    r"[A-Za-z][A-Za-z0-9_.']*"
    r"(?:(?:\{[A-Za-z0-9_,' ]*\}|/[A-Za-z0-9_.']+|\*)[A-Za-z0-9_.']*)*")
BRACE_RE = re.compile(r"\{([A-Za-z0-9_,' ]*)\}")
# `base` followed by one or more code spans that start with `_`; the delimiters
# (backtick in markdown, brace left over from \texttt in TeX) anchor the split.
_SPAN = r"[`}]\s*/\s*[`{]"
CONT_RE = re.compile(
    r"([A-Za-z][A-Za-z0-9_.'{},/*]*)((?:" + _SPAN + r"_[A-Za-z0-9_.'{},*]+)+)")
CONT_SUFFIX_RE = re.compile(r"[`{](_[A-Za-z0-9_.'{},*]+)")
CAMEL_RE = re.compile(r"[a-z0-9][A-Z]")
EXPANSION_CAP = 200  # a pathological token must not blow up the index


def normalize(text: str) -> str:
    r"""Undo TeX escaping of `_`/braces, then drop control sequences.

    `\texttt{...}` must go: otherwise the command name glues onto the argument
    and `\texttt{mielkeHamiltonian\_isHermitian}` is indexed as one bogus token.
    The braces are kept, since they delimit code spans for CONT_RE.
    """
    text = text.replace(r"\_", "_").replace(r"\{", "{").replace(r"\}", "}")
    return re.sub(r"\\[A-Za-z]+", " ", text)


def strip_unbalanced(tok: str) -> str:
    """Drop trailing `}` that closes a delimiter rather than an alternation group
    (`\\texttt{_occupied}` captures `_occupied}`)."""
    while tok.count("}") > tok.count("{") and tok.endswith("}"):
        tok = tok[:-1]
    return tok


def identifier_shaped(name: str) -> bool:
    """True for names that look like Lean declarations, i.e. containing `_` or a
    camelCase hump. Prose words ('lemma', 'trace') must not enter the index."""
    return "_" in name or bool(CAMEL_RE.search(name))


def _boundaries(s: str) -> list[int]:
    """Indices of name-boundary positions in `s` (0, either side of `_`, camelCase
    humps). Both sides of `_` are boundaries because the separator may belong to
    the shared prefix (`becTowerState_` + `neg...`) or to the shared suffix
    (`spinOneOpPlus` + `_conjTranspose`)."""
    out = [0]
    for i in range(1, len(s)):
        if (s[i] == "_" or s[i - 1] == "_"
                or (s[i].isupper() and not s[i - 1].isupper())):
            out.append(i)
    return out


def expand_braces(token: str) -> list[str]:
    """Cross product over every `{a,b,c}` group (an empty alternative is allowed)."""
    out = [token]
    while BRACE_RE.search(out[0]):
        nxt = []
        for t in out:
            m = BRACE_RE.search(t)
            if not m:
                nxt.append(t)
                continue
            for alt in m.group(1).split(","):
                nxt.append(t[:m.start()] + alt.strip() + t[m.end():])
        out = nxt[:EXPANSION_CAP]
    return out


def expand_slash(token: str) -> list[str]:
    """Expand one `A/B` alternation, restoring the abbreviated side.

    `L/R` yields `L` itself (the left alternative is always spelled out in full,
    as in `..._basisVec_all_up/down`), `L + t` for every boundary-suffix `t` of
    `R`, and `p + R` for every NON-EMPTY boundary-prefix `p` of `L`; recursion
    handles a second slash. `R` alone is emitted only when it carries no `*`:
    a wildcard right side is an abbreviated fragment, and reading it standalone
    manufactures the over-broad `sub_*` out of `.../sub_*`, which would mark
    every `sub_…` declaration in the tree as documented.
    """
    i = token.find("/")
    if i < 0:
        return [token]
    if "_" not in token:  # a path or prose, not a declaration family
        return []
    left, right = token[:i], token[i + 1:]
    if not left or not right:
        return []
    names = {left}
    if "*" not in right:
        # The right alternative may stand alone when it is a complete name
        # (`angRaise/angLower_normSq`), never when it is a wildcard fragment.
        names.add(right)
    names |= {left + right[j:] for j in _boundaries(right) if j > 0}
    names |= {left[:p] + right for p in _boundaries(left) if p > 0}
    out = []
    for n in names:
        out.extend(expand_slash(n))
    return out[:EXPANSION_CAP]


def expand_continuation(base: str, suffix: str) -> list[str]:
    """Apply a leading-underscore continuation `suffix` to `base`.

    `base` keeps a boundary prefix and the segments after it are replaced by
    `suffix`. A `suffix` that also ends with `_` is an infix replacement, so a
    boundary tail of `base` is re-appended.
    """
    # A head must itself be identifier-shaped: cutting a family name down to its
    # first word (`rightGauge_conj_…` -> `right`) is never the intended reading and
    # yields over-broad names such as the wildcard `right_theta_*`.
    heads = [base[:p] for p in _boundaries(base) + [len(base)]
             if p > 0 and not base[:p].endswith("_") and identifier_shaped(base[:p])]
    if not suffix.endswith("_"):
        return [h + suffix for h in heads][:EXPANSION_CAP]
    tails = [base[q:] for q in _boundaries(base) if q < len(base) and base[q] != "_"]
    return [h + suffix + t for h in heads for t in tails][:EXPANSION_CAP]


def _record(name: str, exact: set, prefixes: set) -> None:
    """File one expanded token as an exact name or as a wildcard prefix."""
    name = name.strip(".")
    if not name or "{" in name or "/" in name:
        return
    if name.endswith("*"):
        stem = name[:-1]
        # A family wildcard is anchored on a separator; `word*` is prose.
        if stem and stem[-1] in "_." and "*" not in stem and identifier_shaped(stem):
            prefixes.add(stem)
        return
    if "*" in name:
        return
    if identifier_shaped(name):
        exact.add(name)
    seg = name.rsplit(".", 1)[-1]  # a qualified mention documents the decl
    if identifier_shaped(seg):
        exact.add(seg)


def _record_token(tok: str, exact: set, prefixes: set) -> None:
    """Expand one token through brace and slash, then file the results."""
    if "{" not in tok and "/" not in tok and "*" not in tok:
        _record(tok, exact, prefixes)
        return
    for braced in expand_braces(tok):
        for name in expand_slash(braced):
            _record(name, exact, prefixes)


def index_from_text(text: str):
    """Return (exact names, wildcard prefixes) documented in one (normalized) text."""
    exact, prefixes = set(), set()
    for m in CONT_RE.finditer(text):
        for base in expand_braces(strip_unbalanced(m.group(1))):
            for raw in CONT_SUFFIX_RE.findall(m.group(2)):
                for suffix in expand_braces(strip_unbalanced(raw)):
                    for name in expand_continuation(base, suffix):
                        _record_token(name, exact, prefixes)
    for m in TOKEN_RE.finditer(text):
        # A token whose left neighbour is an identifier character is the tail of a
        # continuation span (`_sub_*` -> `sub_*`); indexing it would register the
        # over-broad wildcard `sub_`. The continuation pass above handles it.
        if m.start() and (text[m.start() - 1] == "_" or text[m.start() - 1].isalnum()):
            continue
        _record_token(m.group(0), exact, prefixes)
    return exact, prefixes


def index_names(paths=None):
    """Return (exact names, wildcard prefixes) documented in `paths`.

    Fails loudly on a missing document or an empty result: silently indexing
    nothing would classify every declaration as undocumented, i.e. as deletable.
    """
    paths = list(DOCS if paths is None else paths)
    missing = [p for p in paths if not os.path.exists(p)]
    if missing:
        raise SystemExit(
            "docs_names.py: documentation not found: " + ", ".join(missing)
            + "\n  (AUDIT_DOCS paths are resolved against the repo root; an empty"
              " index would report every declaration as undocumented)")
    exact, prefixes = set(), set()
    for p in paths:
        e, w = index_from_text(normalize(open(p, encoding="utf-8").read()))
        exact |= e
        prefixes |= w
    if not exact:
        raise SystemExit("docs_names.py: the documented-name index is empty;"
                         " refusing to report every declaration as undocumented")
    return exact, prefixes


def is_documented(name: str, exact: set, prefixes: set) -> bool:
    """True if `name` (bare or qualified) is covered by the documented index."""
    if name in exact or name.rsplit(".", 1)[-1] in exact:
        return True
    return any(name.startswith(p) for p in prefixes)


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else "--expand"
    if mode not in ("--expand", "--filter", "--check"):
        print(__doc__)
        return 2
    exact, prefixes = index_names()
    if mode == "--expand":
        for n in sorted(exact):
            print(n)
        for p in sorted(prefixes):
            print(p + "*")
        return 0
    if mode == "--filter":
        if len(sys.argv) < 3:
            print("docs_names.py --filter FILE|-   ('-' reads stdin)")
            return 2
        src = sys.argv[2]
        stream = sys.stdin if src == "-" else open(src, encoding="utf-8")
        for line in stream:
            if not line.strip():
                continue
            if not is_documented(line.split()[-1], exact, prefixes):
                sys.stdout.write(line)
        return 0
    for name in sys.argv[2:]:
        print(f"{name}\t" + ("documented" if is_documented(name, exact, prefixes)
                             else "undocumented"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
