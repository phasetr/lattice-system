#!/usr/bin/env python3
"""Current-tree gates plus input-bound checker regression selection.

Only successful rewrite-ci verify logs are evidence. No cache hit, commit
message, user-provided receipt, or skipped job can stand in for that evidence.
The Git-history-sensitive transition gate is always run on the actual base.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


VERSION = 1
MARKER = "rewrite-ci-receipt: "
WORKFLOW = ".github/workflows/rewrite-ci.yml"
SUITES = {
    "checkers": "test-checkers.sh",
    "skeleton": "test-skeleton-semantic.sh",
    "corrections": "test-claim-corrections-runtime.sh",
    "content": "test-content-amendments-runtime.sh",
    "selector": "test-base-diff-ci-runtime.sh",
}
CORPUS = {"checkers", "corrections", "content"}
SEMANTIC = {
    "phase", "source-progress", "bindings", "dependencies", "claim-context",
    "axioms", "claim-axioms", "vocabulary", "claim-vocabulary", "modules",
    "imports", "statement-modules", "statement-imports",
}
CORPUS_TABLES = {
    "tracks", "sources", "source-invariants", "pages", "claims", "source-items",
    "item-claims", "slices", "claim-vocabulary-review", "correction-events",
    "claim-normalization-reviews", "claim-corrections", "claim-successors",
    "source-item-additions", "claim-content-amendments",
}
POLICY = {"README.md", "DESIGN.md", ".github/pull_request_template.md"}
# These alter executable selection or elaboration. CI must use the declared
# production route; fixture-only override values are never printed or reused.
OVERRIDES = {
    "CHECK_BASE_DIFF", "CHECK_CORRECTIONS", "GENERATE_PUBLIC_DOCS",
    "LATTICE_TEST_ROOT", "LATTICE_SKELETON_CHECKER_DIR",
    "LATTICE_SKELETON_ACTUAL_OUT", "PYTHONOPTIMIZE", "PYTHONPATH",
    "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS", "ELAN_TOOLCHAIN",
    "BASH_ENV", "ENV", "GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL",
    "GIT_CONFIG_SYSTEM", "GIT_CONFIG_PARAMETERS",
}
SHA = re.compile(r"^[0-9a-f]{40}$")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def commit(root, ref):
    value = git(root, "rev-parse", "--verify", ref + "^{commit}").decode().strip()
    if not SHA.fullmatch(value):
        raise ValueError("invalid commit")
    return value


def parents(root, ref):
    return git(root, "show", "-s", "--format=%P", ref).decode().split()


def tree(root, ref):
    return git(root, "rev-parse", ref + "^{tree}").decode().strip()


def entries(root, ref):
    result = {}
    for record in git(root, "ls-tree", "-r", "-z", ref).split(b"\0"):
        if record:
            metadata, path = record.split(b"\t", 1)
            mode, kind, oid = metadata.decode().split()
            result[path.decode()] = (mode, kind, oid)
    return result


def projected(path):
    return path.startswith("registry/") or path.startswith("docs/") or path in POLICY


def engine(rows):
    # OIDs come from Git independently of the receipt. A different workflow or
    # test runner cannot attest that it ran the current trusted implementation.
    return digest({p: v for p, v in rows.items() if not projected(p)})


def inputs(root, ref, environment):
    rows = entries(root, ref)
    common = {"engine": engine(rows), "paths": {p: v[:2] for p, v in rows.items()},
              "environment": environment}
    headers, registry, policy = {}, {}, {}
    for path, (_, kind, oid) in rows.items():
        if kind != "blob":
            raise ValueError("non-blob tracked input")
        if path.startswith("registry/"):
            raw = git(root, "show", ref + ":" + path)
            headers[path] = raw.split(b"\n", 1)[0].hex()
            registry[path] = oid
        if path in POLICY:
            text = git(root, "show", ref + ":" + path).decode()
            # Exactly the predicates read by check-policy.sh. Its code is in
            # engine; changing the reader invalidates the previous evidence.
            policy[path] = {"exact_pr": "exact PR" in text,
                            "exact_head": "exact head SHA" in text}
            if path.endswith("pull_request_template.md"):
                policy[path].update(unchecked="- [ ] USER ONLY" in text,
                                    checked=bool(re.search(r"- \[[xX]\] USER ONLY", text)))
    common.update(headers=headers, policy=policy)
    synthetic = digest(common)
    corpus = digest(dict(common, registry=registry, historical=historical_inputs(root, ref)))
    return {name: corpus if name in CORPUS else synthetic for name in SUITES}, common["engine"]


def historical_inputs(root, ref):
    # The corpus-based suites also read immutable historical registry fixtures.
    # Check their objects exist, rather than treating a shallow/incomplete clone
    # as equivalent merely because the current files have the same contents.
    history = {"c6fb1ec6046626e14dd9a65f396a66386fcb9b7b", "cf4a289e7c766554c8821e167eddac2c3e291c2a"}
    events = git(root, "show", ref + ":registry/correction-events.tsv").decode().splitlines()
    history.update(row.split("\t")[3] for row in events[1:] if len(row.split("\t")) >= 4)
    historical = {}
    for identifier in sorted(history):
        resolved = commit(root, identifier)
        historical[identifier] = tree(root, resolved)
        objects = [value[2] for path, value in entries(root, resolved).items() if path.startswith("registry/")]
        checked = subprocess.check_output(["git", "-C", str(root), "cat-file", "--batch-check"],
                                          input="".join(oid + "\n" for oid in objects).encode()).decode().splitlines()
        if len(checked) != len(objects) or any(len(line.split()) != 3 or line.split()[1] != "blob" for line in checked):
            raise ValueError("historical fixture objects unavailable")
    return historical


def classify(root, base, head):
    """Only ordinary content edits in the known corpus/doc surface are light."""
    reasons = []
    old, new = entries(root, base), entries(root, head)
    raw = git(root, "diff", "--raw", "--no-renames", "--no-abbrev", "-z", base, head).split(b"\0")
    changes = []
    for position in range(0, len(raw) - 1, 2):
        metadata, path = raw[position], raw[position + 1].decode()
        oldmode, newmode, _, _, status = metadata.decode().split()
        oldmode = oldmode.lstrip(":")
        changes.append(path)
        if status != "M" or oldmode != newmode or newmode not in {"100644", "100755"}:
            reasons.append("non-content-change:" + path)
        elif path.startswith("registry/") and path.endswith(".tsv"):
            table = path.rsplit("/", 1)[-1][:-4]
            if table in SEMANTIC:
                reasons.append("semantic-registry:" + path)
            elif table not in CORPUS_TABLES or path != "registry/" + table + ".tsv":
                reasons.append("unknown-registry:" + path)
            before = git(root, "show", base + ":" + path).split(b"\n", 1)[0]
            after = git(root, "show", head + ":" + path).split(b"\n", 1)[0]
            if before != after:
                reasons.append("registry-header:" + path)
        elif path not in {"README.md", "DESIGN.md"} and not path.startswith("docs/"):
            reasons.append("engine-or-unknown:" + path)
    if not changes:
        reasons.append("empty-diff")
    if old.keys() != new.keys():
        reasons.append("tracked-inventory-changed")
    return changes, reasons


def environment(root):
    result = {key: os.environ.get(key, "") for key in
              ("RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion")}
    if not all(result.values()):
        raise ValueError("runner identity unavailable")
    for name, command in {"lean": ["lean", "--version"], "lake": ["lake", "--version"],
                          "python": [sys.executable, "--version"], "git": ["git", "--version"],
                          "bash": ["bash", "--version"]}.items():
        result[name] = subprocess.check_output(command, cwd=root).decode().splitlines()[0]
    return result


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, message, headers, newurl):
        redirected = super().redirect_request(request, fp, code, message, headers, newurl)
        if urllib.parse.urlsplit(newurl).scheme != "https":
            raise ValueError("non-HTTPS API redirect")
        if urllib.parse.urlsplit(newurl).netloc != "api.github.com":
            redirected.remove_header("Authorization")
        return redirected


class Evidence:
    """Bounded read-only lookup; any unavailable/invalid evidence means execute."""

    def __init__(self, repository, token):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise ValueError("invalid repository")
        self.repository, self.token = repository, token
        self.opener = urllib.request.build_opener(SafeRedirect())
        self.loaded = {}
        self.deadline = time.monotonic() + 45

    def get(self, suffix, raw=False):
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("evidence lookup budget exhausted")
        request = urllib.request.Request("https://api.github.com/repos/" + self.repository + suffix,
                                         headers={"Authorization": "Bearer " + self.token,
                                                  "Accept": "application/vnd.github+json",
                                                  "X-GitHub-Api-Version": "2022-11-28"})
        with self.opener.open(request, timeout=min(8, remaining)) as response:
            body = response.read(8_000_001)
        if len(body) > 8_000_000:
            raise ValueError("oversized evidence")
        return body if raw else json.loads(body)

    def load(self, run_id, expected_engine):
        if (run_id, expected_engine) in self.loaded:
            return self.loaded[run_id, expected_engine]
        run = self.get("/actions/runs/" + str(run_id))
        if (type(run_id) is not int or run_id <= 0 or run["id"] != run_id
                or run["status"] != "completed" or run["conclusion"] != "success"
                or run["name"] != "rewrite-ci" or run["path"] != WORKFLOW
                or run["repository"]["full_name"] != self.repository
                or run["event"] not in {"push", "pull_request"}
                or (run["event"] == "push" and run["head_branch"] != "rewrite-main")):
            raise ValueError("untrusted or unsuccessful run")
        attempt = run["run_attempt"]
        if type(attempt) is not int or attempt <= 0:
            raise ValueError("invalid run attempt")
        jobs = self.get(f"/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100")
        matching = [job for job in jobs["jobs"] if job["name"] == "verify"]
        if jobs["total_count"] != 1 or len(matching) != 1:
            raise ValueError("ambiguous verification job")
        job = matching[0]
        if (job["status"] != "completed" or job["conclusion"] != "success"
                or job["run_id"] != run_id or job.get("run_attempt", attempt) != attempt):
            raise ValueError("unsuccessful verification job")
        log = self.get(f'/actions/jobs/{job["id"]}/logs', raw=True).decode()
        markers = [line.split(MARKER, 1)[1] for line in log.splitlines() if MARKER in line]
        if len(markers) != 1:
            raise ValueError("missing or ambiguous receipt")
        receipt = json.loads(markers[0])
        fields = {"version", "run_id", "run_attempt", "head", "source_head", "base", "tree",
                  "event", "engine", "environment", "suites", "current", "transition", "build"}
        if (set(receipt) != fields or type(receipt["version"]) is not int or receipt["version"] != VERSION
                or receipt["run_id"] != run_id or receipt["run_attempt"] != attempt
                or receipt["source_head"] != run["head_sha"] or receipt["event"] != run["event"]
                or receipt["engine"] != expected_engine
                or any(receipt[key] != "success" for key in ("current", "transition", "build"))
                or set(receipt["suites"]) != set(SUITES)
                or any(not SHA.fullmatch(receipt[key]) for key in ("head", "source_head", "base", "tree"))):
            raise ValueError("receipt identity mismatch")
        actual = self.get("/git/commits/" + receipt["head"])
        parent_ids = [parent["sha"] for parent in actual["parents"]]
        if actual["tree"]["sha"] != receipt["tree"]:
            raise ValueError("checkout tree mismatch")
        if receipt["event"] == "push":
            if receipt["head"] != run["head_sha"] or parent_ids != [receipt["base"]]:
                raise ValueError("push receipt ancestry mismatch")
        elif receipt["head"] == run["head_sha"] or parent_ids != [receipt["base"], run["head_sha"]]:
            raise ValueError("PR checkout ancestry mismatch")
        remote = self.get("/git/trees/" + receipt["tree"] + "?recursive=1")
        if remote["truncated"]:
            raise ValueError("truncated engine tree")
        remote_rows = {row["path"]: (row["mode"], row["type"], row["sha"])
                       for row in remote["tree"] if row["type"] != "tree"}
        if engine(remote_rows) != expected_engine:
            raise ValueError("producer executable tree mismatch")
        for result in receipt["suites"].values():
            if (set(result) != {"input", "result", "origin"}
                    or not re.fullmatch(r"[0-9a-f]{64}", result["input"])
                    or result["result"] not in {"executed", "reused"}
                    or (result["result"] == "executed" and result["origin"] is not None)
                    or (result["result"] == "reused" and
                        (not isinstance(result["origin"], dict) or
                         set(result["origin"]) != {"run_id", "run_attempt", "job_id"}))):
                raise ValueError("invalid suite receipt")
            if result["origin"] and any(type(value) is not int or value <= 0 for value in result["origin"].values()):
                raise ValueError("invalid executed origin reference")
        value = receipt, {"run_id": run_id, "run_attempt": attempt, "job_id": job["id"]}
        self.loaded[run_id, expected_engine] = value
        return value

    def candidates(self, context):
        if context["event"] == "pull_request":
            source_head = context["base"]
            query = urllib.parse.urlencode({"event": "push", "head_sha": context["base"], "per_page": 5})
        else:
            pulls = self.get("/commits/" + context["head"] + "/pulls?per_page=10")
            matching = [pr for pr in pulls if pr["merged_at"] and pr["merge_commit_sha"] == context["head"]
                        and pr["base"]["ref"] == "rewrite-main"
                        and pr["head"]["repo"] and pr["head"]["repo"]["full_name"] == self.repository]
            if len(matching) != 1:
                return []
            source_head = matching[0]["head"]["sha"]
            query = urllib.parse.urlencode({"event": "pull_request", "head_sha": source_head,
                                           "per_page": 5})
        runs = self.get("/actions/workflows/rewrite-ci.yml/runs?" + query)
        return [{"run_id": run["id"], "source_head": source_head} for run in runs["workflow_runs"] if run["status"] == "completed"
                and run["conclusion"] == "success"][:5]

    def reuse(self, context, signatures, expected_engine, current_environment):
        accepted = {}
        for candidate in self.candidates(context):
            try:
                receipt, reference = self.load(candidate["run_id"], expected_engine)
                if receipt["environment"] != current_environment or receipt["source_head"] != candidate["source_head"]:
                    continue
                if context["event"] == "pull_request":
                    if receipt["head"] != context["base"] or receipt["event"] != "push":
                        continue
                elif receipt["event"] != "pull_request" or receipt["base"] != context["base"] or receipt["tree"] != context["tree"]:
                    continue
                for name, signature in signatures.items():
                    result = receipt["suites"][name]
                    if result["input"] != signature:
                        continue
                    origin = reference
                    if result["result"] == "reused":
                        # No recursive chain: re-open the original executed job.
                        original, origin = self.load(result["origin"]["run_id"], expected_engine)
                        if origin != result["origin"] or original["environment"] != current_environment:
                            continue
                        root_result = original["suites"][name]
                        if root_result != {"input": signature, "result": "executed", "origin": None}:
                            continue
                    accepted[name] = origin
                if len(accepted) == len(SUITES):
                    break
            except (KeyError, TypeError, ValueError, OSError, urllib.error.URLError):
                continue
        return accepted


def ci_context(root):
    event = os.environ["GITHUB_EVENT_NAME"]
    payload = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    head = commit(root, "HEAD")
    if git(root, "status", "--porcelain").strip():
        raise ValueError("CI checkout must be clean")
    if event == "push":
        base, source = payload["before"], payload["after"]
        if source != head or not SHA.fullmatch(base) or base == "0" * 40 or parents(root, head) != [base]:
            raise ValueError("push must bind its actual before/after single-parent transition")
    elif event == "pull_request":
        pr = payload["pull_request"]
        base, source = pr["base"]["sha"], pr["head"]["sha"]
        if pr["base"]["ref"] != "rewrite-main" or head == source or parents(root, head) != [base, source]:
            raise ValueError("unexpected PR checkout")
        if git(root, "merge-base", base, source).decode().strip() != base:
            raise ValueError("PR is not up to date with its declared base")
    else:
        raise ValueError("unsupported CI event")
    commit(root, base)
    return {"event": event, "head": head, "source_head": source, "base": base, "tree": tree(root, head)}


def run(root, command):
    print("check-selected: run " + " ".join(command), flush=True)
    subprocess.run(command, cwd=root, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--current", action="store_true", help="local current-tree checks; CI regressions still required")
    mode.add_argument("--full", action="store_true", help="all current and regression gates locally")
    mode.add_argument("--ci", action="store_true", help="event-bound selection with successful CI evidence")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--base", default="origin/rewrite-main")
    args = parser.parse_args()
    root = args.root.resolve()
    reused, reasons, context, signatures, engine_oid, env = {}, [], None, {}, "", {}
    if args.ci:
        present = sorted(OVERRIDES.intersection(os.environ))
        if present:
            raise ValueError("CI production overrides must be unset: " + ", ".join(present))
        context = ci_context(root)
        base = context["base"]
        changes, reasons = classify(root, base, context["head"])
        print("check-selected: changed paths " + json.dumps(changes), flush=True)
        try:
            env = environment(root)
            signatures, engine_oid = inputs(root, context["head"], env)
            # PR engine changes require new regressions. A production push can
            # instead reuse an exact already-tested merged PR tree, including
            # its new engine; it still runs the actual transition afresh.
            if not reasons or context["event"] == "push":
                evidence = Evidence(os.environ["GITHUB_REPOSITORY"], os.environ["GH_TOKEN"])
                reused = evidence.reuse(context, signatures, engine_oid, env)
        except (KeyError, TypeError, ValueError, OSError, urllib.error.URLError, subprocess.CalledProcessError):
            reasons.append("accepted-input-evidence-unavailable")
        if len(reused) != len(SUITES) and not reasons:
            reasons.append("no-matching-successful-input-evidence")
    else:
        base = commit(root, args.base)
    print("check-selected: " + ("; ".join(reasons) if reasons else "current-tree route"), flush=True)
    run(root, [sys.executable, "scripts/test-check-selected.py"])
    run(root, ["scripts/check-current.sh", str(root)])
    # This guard is intentionally outside every reuse decision, including the
    # postmerge route: origin/rewrite-main would equal HEAD on a trunk push.
    run(root, ["scripts/check-base-diff-ci.sh", str(root), base])
    results = {}
    if not args.current:
        for name, script in SUITES.items():
            if name in reused:
                print(f"check-selected: reuse {name} from run {reused[name]['run_id']} job {reused[name]['job_id']}", flush=True)
                results[name] = {"input": signatures[name], "result": "reused", "origin": reused[name]}
            else:
                run(root, ["scripts/" + script, str(root)])
                results[name] = {"input": signatures.get(name, ""), "result": "executed", "origin": None}
    run(root, ["lake", "build"])
    if args.ci:
        if not signatures or not engine_oid or not env:
            # All tests ran, but an unverifiable environment produces no reusable
            # receipt. Future runs conservatively execute again.
            print("check-selected: all gates passed; no reusable environment receipt", flush=True)
        else:
            receipt = dict(version=VERSION, run_id=int(os.environ["GITHUB_RUN_ID"]),
                           run_attempt=int(os.environ["GITHUB_RUN_ATTEMPT"]), engine=engine_oid,
                           environment=env, suites=results, current="success", transition="success",
                           build="success", **context)
            print(MARKER + json.dumps(receipt, sort_keys=True, separators=(",", ":")), flush=True)
    print("check-selected: current gates passed; regression acceptance remains required in CI" if args.current
          else "check-selected: all selected gates passed", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (KeyError, TypeError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print("check-selected: failed (" + type(error).__name__ + ")", file=sys.stderr)
        sys.exit(1)
