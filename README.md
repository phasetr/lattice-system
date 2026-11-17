# LatticeSystem

A from-scratch formalization of mathematical physics, organized by independently
reviewed source claims. Registry records, implemented vocabulary, typed source
statements and proofs have separate acceptance gates.

## Start and resume

Check the actual checkout before using a recorded result:

```sh
git status --short --branch
git rev-parse HEAD rewrite-main origin/rewrite-main
```

Read the project `AGENTS.md` instructions and [DESIGN.md](DESIGN.md). The current
work and single next action are maintained in
[Issue #5479](https://github.com/phasetr/lattice-system/issues/5479), rather than
copied into progress histories here. An open PR is not an integrated change.

Use the existing authorities for current facts:

- [Public status and catalog](docs/index.md): generated counts, source items,
  vocabulary and binding/proof metadata, without normalized source claim text.
- [Checker capability](registry/phase.tsv) and
  [source metadata](registry/sources.tsv): the global capability and each source's
  separate lifecycle, review reference and frozen census anchors.
- [Registered production modules](registry/modules.tsv) and
  [vocabulary](registry/vocabulary.tsv): source paths and declaration identities;
  the Lean environment establishes their existence and types.
- [Correction events](registry/correction-events.tsv): accepted registry
  transitions and their exact bases and independent review references.

A recorded census or `vocabulary_ready` status does not establish source
fidelity, a closed typed physics contract, statement binding or proof.
Structural success and absent pre-R4 statement records do not certify R4.
The scope of an accepted review must be read before reusing it.

The mathematical vocabulary includes partial traces and
[finite-site and total-spin operators](LatticeSystem/Vocabulary/Spin.lean), and
[fermionic occupation-basis operators](LatticeSystem/Vocabulary/Fermion.lean).
The mathematical interfaces and source conventions in [DESIGN.md](DESIGN.md)
separate source-order spin construction from existing Mathlib reuse and the
later reduced-density definition. The fermionic interfaces distinguish the full
Fock space from fixed-particle sectors and use the stated occupation-basis signs.
Their R3 registration route preserves source
claims and requires fresh environment checks; it is distinct from R4 statement
freeze and proof implementation. It does not certify every future source contract.

Source lifecycle and reviewed corpus anchors have one physical record per source.
Counts and coverage are derived from those records and the corpus; public source
item format tags are supplied by the schema. Future-stage relation schemas live
in the typed checker until needed. Before R4 their files may be absent; a present
file must still have its exact empty schema. Skeleton and proof phases require
the physical statement, dependency and axiom relation tables and their normal gates.

## Checks and generated documentation

Use the same entrypoint locally and in CI:

```sh
lake exe checker --current --base origin/rewrite-main
```

This runs the current registry, semantic, generation and actual-transition
checks through the same Lean executable used by CI. Its first invocation builds
the checker infrastructure. Use `--full` in place of `--current` for every local
regression group; `--current` leaves regression acceptance to CI.

CI uses `--ci` to select independent regression groups from their actual reader
inputs and verified successful-run evidence. Unknown or changed inputs run the
affected groups. Runner image build labels remain audit information; reuse
still requires matching OS, architecture, native ABI, tools, compiler and reader
inputs. Independent selected groups use bounded child processes with separate
fixtures, and every child must finish before acceptance. Mathematical production
builds run when their own source,
configuration or dependency inputs change; checker and documentation changes
alone do not require that build. Required semantic imports and fixture builds
remain separate checks. The plan prints execution, verified reuse and omitted
work with reasons before running. A duplicate local full suite is not required
when the final published head receives its official CI acceptance. The required
workflow/job remains `rewrite-ci` / `verify`.

Generate and check the complete public catalog through the Lean entrypoint:

```sh
lake exe checker --docs --write
lake exe checker --docs --check
```

Repository-owned validation, derivation, generation, regression execution and CI
control are implemented in Lean. External commands provide only necessary thin
OS, Git, HTTP, archive, filesystem and compiler operations; no interpreted
implementation or embedded Python or Shell body substitutes for the Lean logic.
Pure transformations, functional folds and explicit-state recursion represent
implementation state; reference cells do not substitute for imperative local
updates. IO stays at the external boundary, preserving order and validation.
Generated files are not edited by hand. Use the declared dependencies and
pinned toolchain; a failed command is not permission to install or update them.

## Review and merge

Source review, implementation review and verification must identify their exact
revision and scope. None substitutes for the others or proves mathematical
truth outside its reviewed scope. Only the user can authorize merging
the exact PR at its current exact head SHA under the project hard merge gate. Agents leave
`USER ONLY` unchecked; CI success is not merge authority.
