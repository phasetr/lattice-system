#!/usr/bin/env python3
"""docs_names.py — which declaration names are recorded in the public docs.

The dead-declaration sweep asks "is this zero-reference decl written up in
`docs/index.md` / `tex/proof-guide.tex`?".  Answering that with an exact-match
grep is **wrong**: both documents record whole declaration families in a
compressed notation, so an exact grep reports a documented decl as undocumented.
That mis-classification is not academic — in the Wave-1 sweep 49 of 50
"undocumented" candidates were in fact book-facing results written up with their
Tasaki equation numbers (`spinOneRot{1,2,3}_zero`, Problem 2.1.c, ...).

Only the three compressions that the two documents actually use are expanded
(verified by grepping them; this is deliberately not a general brace expander):

  brace   `spinOnePiRot{1,2,3}_sq`      -> spinOnePiRot1_sq, ...2_sq, ...3_sq
          `all{Up,Down}_neelStateOf_{,complement_}orthogonal`  (empty alternative
          and several braces per token are used, so the cross product is taken)
  slash   `spinOneOpPlus/Minus_conjTranspose`
                                        -> spinOneOpPlus_conjTranspose,
                                           spinOneOpMinus_conjTranspose
          the right side is usually an abbreviated fragment, so both readings are
          generated: `L + <tail of R>` and `<head of L> + R`, cut only at name
          boundaries (`_` or a camelCase hump).
  star    `spinOnePiRot{1,2,3}_comm_*`  -> prefix match `spinOnePiRot1_comm_`, ...
          honoured only when the `*` follows `_` or `.`; a bare `word*` is prose
          or markdown emphasis, never a family.

TeX escaping (`\\_`, `\\{`, `\\}`) is undone first.  A slash token is expanded
only if it contains `_`, which keeps file paths and prose (`AngularMomentum/Ladder`,
`add/sub`) out of the index.

usage:
  docs_names.py --expand              # every documented name (one per line)
  docs_names.py --filter FILE         # keep the lines of FILE whose name is NOT
                                      # documented (name = last whitespace field)
  docs_names.py --check NAME...       # per name: 'documented' / 'undocumented'
"""
from __future__ import annotations
import os
import re
import sys

DOCS = os.environ.get(
    "AUDIT_DOCS", "docs/index.md:tex/proof-guide.tex").split(":")

# A token is an identifier-ish run that may carry the three compressions above.
TOKEN_RE = re.compile(
    r"[A-Za-z][A-Za-z0-9_.']*"
    r"(?:(?:\{[A-Za-z0-9_,' ]*\}|/[A-Za-z0-9_.']+|\*)[A-Za-z0-9_.']*)*")
BRACE_RE = re.compile(r"\{([A-Za-z0-9_,' ]*)\}")
EXPANSION_CAP = 200  # a pathological token must not blow up the index


def unescape_tex(text: str) -> str:
    """Undo the TeX escaping of `_` and braces, then drop control sequences.

    `\\texttt{...}` must go: otherwise the command name glues onto the argument
    and `\\texttt{mielkeHamiltonian\\_isHermitian}` is indexed as one bogus token.
    """
    text = text.replace(r"\_", "_").replace(r"\{", "{").replace(r"\}", "}")
    return re.sub(r"\\[A-Za-z]+", " ", text)


def _boundaries(s: str) -> list[int]:
    """Indices of name-boundary positions in `s` (0, either side of `_`, camelCase
    humps).  Both sides of `_` are boundaries because the separator may belong to
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
    while True:
        m = BRACE_RE.search(out[0])
        if not m:
            return out
        nxt = []
        for t in out:
            m = BRACE_RE.search(t)
            if not m:
                nxt.append(t)
                continue
            for alt in m.group(1).split(","):
                nxt.append(t[:m.start()] + alt.strip() + t[m.end():])
        out = nxt[:EXPANSION_CAP]


def expand_slash(token: str) -> list[str]:
    """Expand one `A/B` alternation, restoring the abbreviated side.

    `L/R` yields `L + t` for every boundary-suffix `t` of `R` and `p + R` for
    every boundary-prefix `p` of `L`; recursion handles a second slash.
    """
    i = token.find("/")
    if i < 0:
        return [token]
    if "_" not in token:  # a path or prose, not a declaration family
        return []
    left, right = token[:i], token[i + 1:]
    if not left or not right:
        return []
    names = {left + right[j:] for j in _boundaries(right)}
    names.add(left)
    names |= {left[:p] + right for p in _boundaries(left)}
    out = []
    for n in names:
        out.extend(expand_slash(n))
    return out[:EXPANSION_CAP]


def index_names(paths=DOCS):
    """Return (exact names, wildcard prefixes) documented in `paths`."""
    exact, prefixes = set(), set()
    for p in paths:
        if not os.path.exists(p):
            continue
        text = unescape_tex(open(p, encoding="utf-8").read())
        for tok in TOKEN_RE.findall(text):
            if "{" not in tok and "/" not in tok and "*" not in tok:
                _record(tok, exact, prefixes)
                continue
            for braced in expand_braces(tok):
                for name in expand_slash(braced):
                    _record(name, exact, prefixes)
    return exact, prefixes


def _record(name: str, exact: set, prefixes: set) -> None:
    """File one expanded token as an exact name or as a wildcard prefix."""
    name = name.strip(".")
    if not name:
        return
    if name.endswith("*"):
        stem = name[:-1]
        # A family wildcard is anchored on a separator; `word*` is prose.
        if stem and stem[-1] in "_." and "*" not in stem:
            prefixes.add(stem)
        return
    if "*" in name or "{" in name or "/" in name:
        return
    exact.add(name)
    exact.add(name.rsplit(".", 1)[-1])  # a qualified mention documents the decl


def is_documented(name: str, exact: set, prefixes: set) -> bool:
    """True if `name` (bare or qualified) is covered by the documented index."""
    if name in exact or name.rsplit(".", 1)[-1] in exact:
        return True
    return any(name.startswith(p) for p in prefixes)


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else "--expand"
    exact, prefixes = index_names()
    if mode == "--expand":
        for n in sorted(exact):
            print(n)
        for p in sorted(prefixes):
            print(p + "*")
        return 0
    if mode == "--filter":
        src = sys.argv[2]
        stream = sys.stdin if src == "-" else open(src, encoding="utf-8")
        for line in stream:
            if not line.strip():
                continue
            if not is_documented(line.split()[-1], exact, prefixes):
                sys.stdout.write(line)
        return 0
    if mode == "--check":
        for name in sys.argv[2:]:
            print(f"{name}\t"
                  + ("documented" if is_documented(name, exact, prefixes)
                     else "undocumented"))
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
