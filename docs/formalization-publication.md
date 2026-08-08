---
layout: page
title: "Formalization-status publication"
permalink: /formalization-publication/
---

# Formalization-status publication

This page is the reproduction and ownership runbook for the lightweight
formalization-status site. It is separate from doc-gen4, which remains disabled.

## Architecture and authority

The manifest-listed JSON under `formalization-status/v1/` is validated first.
The generator creates one revision-independent canonical aggregate and injects
human source, topic, overview, and status projections into a copied Jekyll
source tree. It also creates exactly one canonical human detail page per record
at `/formalization/records/<record-id>/`. Generated source and rendered output
live only under `.self-local/tmp/`; neither is committed.

Before copying documentation, the generator reserves both the machine
publication root and `docs/formalization/records/`; committed files may own
neither generated output tree. It requires every committed generated marker to
occur exactly once with an empty body. Explanatory prose remains outside those
markers. Missing source and topic projection pages are created dynamically from
the registries, so catalogue growth does not require committed placeholder
pages. Existing source and topic pages may retain hand-written context around
their uniquely owned marker. The checker
accepts a separately emitted validator aggregate, recomputes its framed input
digest, and requires byte equality plus exact projection membership, counts,
order, record identities, and canonical detail links. Each canonical detail is
raw HTML with an escaped heading and an ordered definition list of visible
`data-label-for` labels paired with typed `data-field` values. The checker
compares every canonical record field, including ordered topics, complete typed
provenance, source path, origin, and the proof-guide anchor. Missing, duplicate,
unrecognized, reordered, or contradictory additive fields are rejected in both
staged source and rendered HTML. The staged and rendered gates also require the
record ID set, generated filenames, permalinks, rendered directories, and
article identities to be one-to-one, and require every full record article to
occur exactly once across the human publication.

Source, topic, project-original, and status pages contain only exact counts and
compact links to those canonical details; they contain no record definition
lists. The projection grammar also rejects record-like `article`, `dl`, `dt`,
or `dd` structures, typed-field attributes, and unknown `record-*` containers,
even when canonical article identity attributes have been stripped. Every
generated marker owns one typed container whose complete staged serialization
and live serialization must match the catalogue-derived output exactly;
arbitrary tags, text, or whitespace inside that region are rejected while
hand-written prose outside the marker remains allowed. Their
projection rows retain `record-<record-id>` as an explicit element
ID, preserving the four prototype records' already published source/topic
fragments while changing the fragment target from a duplicated detail block to
the corresponding compact row. Dynamic index and projection rows use the same
escaped raw-HTML boundary with explicit identity, label, and count attributes. Braces are
numeric HTML entities in staged source, preventing catalogue text from opening
a Liquid expression while preserving the canonical visible text after parsing.
Before rendering, the generator also assigns an explicit Kramdown ID to every
heading targeted by an internal fragment link. This preserves the audited
legacy migration fragments even when inline code or Unicode would make
Kramdown's implicit heading-ID behavior differ between source assumptions and
rendered HTML. The staged checker requires each referenced fragment to have
such an explicit pin; the rendered checker still verifies the resulting HTML
ID and rejects duplicates.

The generated views visibly report the catalogue state, schema version, input
SHA-256, and build revision. The build revision is presentation metadata and is
not included in `catalog.json`, so the stable machine artifact is deterministic
for unchanged canonical inputs. Human generator version 2 introduces the
canonical record-route topology; `generation.json` records its exact record
page count and a framed digest of every record ID/route pair. While the
catalogue state is `prototype`, the
[complete interim legacy catalogue](/lattice-system/formalization/legacy/)
remains authoritative until Issue #5228 performs the audited cutover.
When the state becomes `authoritative`, the same generated metadata instead
links to and names the validated version 1 catalogue as the current authority.
The staged and rendered checkers derive this choice from `catalog_state`; a
state flip with stale prototype authority prose is rejected. In authoritative
state they scan every staged Markdown page and every rendered HTML page for the
closed stale-authority phrases exercised by negative tests, rather than merely
checking that the generated metadata itself is correct. The live checker
applies the same rule to every fetched human page.

Stable publication paths are:

- Human catalogue: `/lattice-system/formalization/`
- Canonical human record detail:
  `/lattice-system/formalization/records/<record-id>/`
- Version 1 machine catalogue:
  `/lattice-system/formalization-status/v1/catalog.json`
- Version 1 schema: `/lattice-system/formalization-status/v1/schema.json`
- Build metadata sidecar:
  `/lattice-system/formalization-status/v1/publication.json`

Within version 1 these paths and field meanings follow the compatibility policy
in the [data contract](/lattice-system/formalization-status-contract/).

## Reproduction

From the repository root, using the existing Python and Lean runtimes:

```sh
mkdir -p .self-local/tmp
python3 scripts/check_docs_hierarchy.py
python3 scripts/validate_formalization_status.py --self-test \
  --emit-aggregate .self-local/tmp/catalog.json \
  --emit-lean-check .self-local/tmp/formalization-axioms.lean
lake env lean .self-local/tmp/formalization-axioms.lean
python3 scripts/check_formalization_cutover.py --self-test
python3 scripts/generate_formalization_site.py --self-test \
  --output-dir .self-local/tmp/formalization-site \
  --revision LOCAL
python3 scripts/check_generated_site.py --self-test \
  --source-dir .self-local/tmp/formalization-site/source \
  --expected-catalog .self-local/tmp/catalog.json \
  --revision LOCAL
```

The generated Lean file uses `Lean.collectAxioms` to compare actual non-standard
axioms exactly with each record's `axiom_dependencies`. It ignores only
`propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` is never ignored. Its
committed generator regression includes both an undeclared actual dependency
and a declared-but-unused dependency.

The repository declares the `github-pages` gem in `docs/Gemfile`, but the local
bundle is not currently available in the project environment. The missing gems
were not installed for this work. Consequently, the exact local Jekyll command
is not claimed as available; the workflow uses the declared Pages build action,
then runs the rendered-site checker. The dependency-free staged-source check
above is the local pre-Jekyll reproduction path.

## CI ownership and cost boundary

Before this work, GitHub Pages reported `build_type=workflow`, but the active
workflow list contained no Pages owner; the doc-gen4 block in Lean CI was and
remains commented out. PR A introduced the build job on every pull request,
push to `main`, and manual dispatch. PR B adds the workflow's sole deploy job.
It requires that same run's successful build and uploaded `github-pages`
artifact, and its strict event guard admits only a push to `refs/heads/main`.
Pull-request and manual runs therefore build the complete artifact while the
deploy job is visibly skipped.

Only the deploy job has `pages: write` and `id-token: write`; the workflow top
level and build job remain `contents: read`, and Lean CI remains read-only with
doc-gen4 disabled. The deploy job owns the `github-pages` environment and uses
`actions/deploy-pages@v4`, the version documented by GitHub for the
`actions/upload-pages-artifact@v4` artifact service. The guarded deploy job
alone uses the `pages` concurrency group without cancelling an in-progress
deployment. Pull-request and manual builds remain outside that group, so they
cannot replace a pending `main` deployment. This is the repository's only
Pages deployment owner.

After a successful guarded deployment, a separate read-only job verifies the
live publication for that same `main` SHA. It first fetches the four stable
human entry points (`formalization/`, `status/`, `sources/`, and `topics/`) and
the three versioned JSON resources (`catalog.json`, `schema.json`, and
`publication.json`) below the fixed
`https://phasetr.github.io/lattice-system/` base. It then derives and fetches
every source/topic projection and the project-original projection from that
catalogue. It also checks the four original prototype record routes as a
permanent public-compatibility smoke set. It does not issue one HTTP request per
future record: the status page proves the exact complete record-link projection,
while the same-run rendered-artifact gate has already checked every detail page
and link. This keeps the post-deploy check bounded as the catalogue grows to
thousands of records. The standard-library checker requires HTTP 200 and the
expected content type, exact generated metadata and catalog-derived ordered
overview/source/topic/status projections, schema version 1,
a supported matching catalogue state (`prototype` or `authoritative`),
the exact closed top-level key sets and generator identity/version pairs
(`validate_formalization_status.py` version 2 and
`generate_formalization_site.py` version 2), recursive catalogue validation by
the same dependency-free schema evaluator used during generation, matching
input digests, a published schema equal to
the checked-out canonical schema, and a publication revision equal to the
triggering `main` SHA. Redirects are rejected before following, every response
has an eight-MiB hard limit, and one 240-second absolute deadline bounds complete
snapshot retries within the five-minute job. These retries accommodate Pages
propagation without any agent-side polling. Pull-request and manual runs
exercise only its in-memory self-tests and skip the live job. Run those tests
locally with:

```sh
python3 scripts/check_live_formalization_site.py --self-test
```

The build job has a five-minute timeout. The exact sum of rendered regular-file
`st_size` values is reported as **rendered uncompressed bytes** after symlinks
and non-regular entries are rejected. A value at or below 10 MiB is within the
normal budget; a larger value requires review, and a value above 25 MiB fails.
The compressed artifact size reported by the Actions API is a separate metric
and is recorded from the PR run rather than inferred from the rendered tree.
The workflow writes the uncompressed value to its step summary. The accepted
PR-A run completed the Formalization Pages workflow in 34 seconds. Its uploaded
artifact was 573,915 bytes compressed and 3,437,699 bytes uncompressed, within
both thresholds. Lean Action CI completed in 1 minute 16 seconds. These values
are the historical baseline for reviewing later cost changes; Issue #5229
records the run evidence and permission audit.

These thresholds apply only to the lightweight status site. They neither hide
nor relax the separate decision that doc-gen4 is too expensive to re-enable.
