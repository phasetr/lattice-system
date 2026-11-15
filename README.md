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
  [source lifecycles](registry/source-progress.tsv): recorded acceptance stages.
- [Registered production modules](registry/modules.tsv) and
  [vocabulary](registry/vocabulary.tsv): source paths and declaration identities;
  the Lean environment establishes their existence and types.
- [Correction events](registry/correction-events.tsv): accepted registry
  transitions and their exact bases and independent review references.

A recorded census or `vocabulary_ready` status does not establish source
fidelity, a closed typed physics contract, statement binding or proof.
Structural success and empty production statement tables do not certify R4.
The scope of an accepted review must be read before reusing it.

## Checks and generated documentation

Use the same entrypoint locally and in CI:

```sh
lake env lean -DwarningAsError=true --run Checker/CheckAll.lean --current --base origin/rewrite-main
```

This runs current registry, semantic, generation, transition and production-build
checks. It explicitly leaves checker regression acceptance to CI. Use `--full`
in place of `--current` for a complete local regression run. CI uses `--ci` to
select regression suites from their actual inputs and verified successful-run
evidence; changed or unverified inputs cause execution. Current-tree and actual
transition checks and the production build always run. A duplicate local full
suite is not required when the final published head receives its official CI
acceptance. The required workflow/job is `rewrite-ci` / `verify`.

Regenerate the complete public catalog with the existing generator:

```sh
python3 scripts/generate-public-docs.py --write
python3 scripts/generate-public-docs.py --check
```

Generated files are not edited by hand. Use the declared dependencies and
pinned toolchain; a failed command is not permission to install or update them.

## Review and merge

Source review, implementation review and verification must identify their exact
revision and scope. None substitutes for the others or proves mathematical
truth outside its reviewed scope. Only the user can authorize merging
the exact PR at its current exact head SHA under the project hard merge gate. Agents leave
`USER ONLY` unchecked; CI success is not merge authority.
