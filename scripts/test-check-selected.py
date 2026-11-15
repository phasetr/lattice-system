#!/usr/bin/env python3
"""Fast counterfactuals for scope, evidence, ancestry and failure propagation."""

import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import urllib.request

sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("selected", Path(__file__).with_name("check-selected.py"))
selected = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(selected)
A, B, C, D = (character * 40 for character in "abcd")
ENV = {"runner": "fixture"}
SIGNATURES = {name: "1" * 64 for name in selected.SUITES}


class ScopeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lattice-ci-selection.")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.command("init", "-q")
        self.command("config", "user.name", "Runtime Test")
        self.command("config", "user.email", "runtime@example.invalid")
        for path, text in {
            "README.md": "exact PR exact head SHA\n",
            "DESIGN.md": "exact PR exact head SHA\n",
            ".github/pull_request_template.md": "exact PR exact head SHA\n- [ ] USER ONLY\n",
            ".github/workflows/rewrite-ci.yml": "workflow\n",
            ".gitignore": "*.log\n",
            "registry/claims.tsv": "header\nbody\n",
            "registry/bindings.tsv": "header\n",
            "registry/correction-events.tsv": "event\tposition\tsource\tbase\treview\n",
            "scripts/check-all.sh": "engine\n",
            "Checker/Skeleton.lean": "engine\n",
            "LatticeSystem.lean": "engine\n",
            "lean-toolchain": "toolchain\n",
            "lake-manifest.json": "{}\n",
            "docs/index.md": "generated\n",
        }.items():
            self.write(path, text)
        self.base = self.save()

    def command(self, *args):
        return selected.git(self.root, *args).decode().strip()

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)

    def save(self):
        self.command("add", "--all")
        self.command("commit", "-qm", "fixture")
        return self.command("rev-parse", "HEAD")

    def signatures(self, ref):
        with patch.object(selected, "historical_inputs", return_value={"fixture": A}):
            return selected.inputs(self.root, ref, ENV)[0]

    def test_corpus_change_runs_three_copy_suites_but_preserves_synthetic_inputs(self):
        before = self.signatures(self.base)
        self.write("registry/claims.tsv", "header\ncorrected body\n")
        head = self.save()
        paths, reasons = selected.classify(self.root, self.base, head)
        self.assertEqual(paths, ["registry/claims.tsv"])
        self.assertEqual(reasons, [])
        after = self.signatures(head)
        for name in selected.SUITES:
            self.assertEqual(before[name] == after[name], name not in selected.CORPUS)

    def test_policy_prose_and_generated_bytes_are_not_fixture_inputs(self):
        before = self.signatures(self.base)
        self.write("README.md", "prose changed; exact PR exact head SHA\n")
        self.write("DESIGN.md", "other prose; exact PR exact head SHA\n")
        self.write("docs/index.md", "regenerated content\n")
        head = self.save()
        self.assertEqual(selected.classify(self.root, self.base, head)[1], [])
        self.assertEqual(before, self.signatures(head))

    def test_policy_predicate_change_invalidates_inputs(self):
        before = self.signatures(self.base)
        self.write("README.md", "missing gates\n")
        self.assertNotEqual(before, self.signatures(self.save()))

    def test_all_engine_and_semantic_edits_force_full(self):
        for path in ("scripts/check-all.sh", "Checker/Skeleton.lean", "LatticeSystem.lean",
                     "lean-toolchain", "lake-manifest.json", ".gitignore",
                     ".github/workflows/rewrite-ci.yml", "registry/bindings.tsv"):
            with self.subTest(path=path):
                self.command("reset", "--hard", self.base)
                self.write(path, "changed\n")
                self.assertTrue(selected.classify(self.root, self.base, self.save())[1])

    def test_header_edit_forces_full(self):
        self.write("registry/claims.tsv", "new header\nbody\n")
        self.assertIn("registry-header:registry/claims.tsv",
                      selected.classify(self.root, self.base, self.save())[1])

    def test_added_unknown_deleted_renamed_and_mode_inputs_force_full(self):
        cases = ("add", "unknown", "delete", "rename", "mode", "symlink")
        for case in cases:
            with self.subTest(case=case):
                self.command("reset", "--hard", self.base)
                self.command("clean", "-fdq")
                if case in {"add", "unknown"}:
                    self.write("registry/new.tsv" if case == "add" else "unknown", "new\n")
                elif case == "delete":
                    (self.root / "README.md").unlink()
                elif case == "rename":
                    (self.root / "README.md").rename(self.root / "docs/moved.md")
                elif case == "mode":
                    (self.root / "README.md").chmod(0o755)
                else:
                    (self.root / "README.md").unlink()
                    (self.root / "README.md").symlink_to("DESIGN.md")
                paths, reasons = selected.classify(self.root, self.base, self.save())
                self.assertTrue(reasons)
                if case == "rename":
                    self.assertIn("README.md", paths)
                    self.assertIn("docs/moved.md", paths)

    def test_empty_diff_full_and_missing_base_errors(self):
        self.assertIn("empty-diff", selected.classify(self.root, self.base, self.base)[1])
        with self.assertRaises(subprocess.CalledProcessError):
            selected.classify(self.root, "nonexistent", self.base)

    def test_historical_objects_are_required(self):
        with self.assertRaises(subprocess.CalledProcessError):
            selected.historical_inputs(self.root, self.base)


def receipt(event="push"):
    return dict(version=selected.VERSION, run_id=7, run_attempt=2, head=A,
                source_head=A if event == "push" else C, base=B, tree=D, event=event,
                engine="engine", environment=ENV, current="success", transition="success", build="success",
                suites={name: {"input": signature, "result": "executed", "origin": None}
                        for name, signature in SIGNATURES.items()})


class EvidenceTests(unittest.TestCase):
    def evidence(self, value=None, run_changes=None, job_changes=None, log=None, remote_engine="engine"):
        value = value or receipt()
        run = {"id": 7, "status": "completed", "conclusion": "success", "name": "rewrite-ci",
               "path": selected.WORKFLOW, "repository": {"full_name": "owner/repo"},
               "event": value["event"], "run_attempt": 2, "head_sha": value["source_head"],
               "head_branch": "rewrite-main"}
        run.update(run_changes or {})
        job = {"id": 11, "run_id": 7, "run_attempt": 2, "name": "verify", "status": "completed", "conclusion": "success"}
        job.update(job_changes or {})
        answers = {
            "/actions/runs/7": run,
            "/actions/runs/7/attempts/2/jobs?per_page=100": {"total_count": 1, "jobs": [job]},
            "/actions/jobs/11/logs": log if log is not None else
                ("timestamp " + selected.MARKER + json.dumps(value) + "\n").encode(),
            "/git/commits/" + A: {"tree": {"sha": D}, "parents": [{"sha": B}] +
                                   ([{"sha": C}] if value["event"] == "pull_request" else [])},
            "/git/trees/" + D + "?recursive=1": {"truncated": False, "tree": []},
        }
        result = selected.Evidence("owner/repo", "fixture-token")
        result.get = lambda suffix, raw=False: copy.deepcopy(answers[suffix])
        return result, patch.object(selected, "engine", return_value=remote_engine)

    def test_successful_exact_producer(self):
        evidence, engine = self.evidence()
        with engine:
            value, origin = evidence.load(7, "engine")
        self.assertEqual(origin, {"run_id": 7, "run_attempt": 2, "job_id": 11})
        self.assertEqual(value, receipt())

    def test_incomplete_cancelled_skipped_wrong_workflow_repository_and_attempt_rejected(self):
        mutations = ({"status": "in_progress"}, {"conclusion": "failure"}, {"conclusion": "cancelled"},
                     {"conclusion": "skipped"}, {"name": "other"}, {"path": "other.yml"},
                     {"repository": {"full_name": "other/repo"}}, {"event": "workflow_dispatch"},
                     {"head_sha": B}, {"run_attempt": 1})
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                evidence, engine = self.evidence(run_changes=mutation)
                with engine, self.assertRaises((ValueError, KeyError)):
                    evidence.load(7, "engine")
        for conclusion in ("failure", "cancelled", "skipped", "timed_out", "neutral"):
            evidence, engine = self.evidence(job_changes={"conclusion": conclusion})
            with engine, self.assertRaises(ValueError):
                evidence.load(7, "engine")

    def test_missing_multiple_malformed_or_inexact_receipts_rejected(self):
        for log in (b"no receipt", (selected.MARKER + "{}\n").encode(),
                    (selected.MARKER + "bad-json\n").encode(),
                    ((selected.MARKER + json.dumps(receipt()) + "\n") * 2).encode()):
            evidence, engine = self.evidence(log=log)
            with engine, self.assertRaises(ValueError):
                evidence.load(7, "engine")
        for field, value in (("version", 0), ("run_id", 8), ("run_attempt", 1), ("source_head", B),
                             ("tree", C), ("base", C), ("engine", "other"), ("current", "skip"),
                             ("transition", "failure"), ("build", "skipped")):
            mutated = receipt()
            mutated[field] = value
            evidence, engine = self.evidence(value=mutated)
            with engine, self.assertRaises((ValueError, KeyError)):
                evidence.load(7, "engine")
        for key in ("extra", "suites"):
            mutated = receipt()
            if key == "extra":
                mutated[key] = "invalid"
            else:
                mutated[key]["unknown"] = mutated[key].pop("skeleton")
            evidence, engine = self.evidence(value=mutated)
            with engine, self.assertRaises(ValueError):
                evidence.load(7, "engine")

    def test_producer_engine_independently_checked(self):
        evidence, engine = self.evidence(remote_engine="changed executable tree")
        with engine, self.assertRaises(ValueError):
            evidence.load(7, "engine")

    def test_exact_postmerge_new_engine_reuse_and_fresh_base_binding(self):
        value = receipt("pull_request")
        evidence = selected.Evidence("owner/repo", "fixture-token")
        evidence.candidates = lambda context: [{"run_id": 7, "source_head": C}]
        evidence.load = lambda run, engine: (value, {"run_id": 7, "run_attempt": 2, "job_id": 11})
        context = {"event": "push", "head": "e" * 40, "base": B, "tree": D}
        self.assertEqual(set(evidence.reuse(context, SIGNATURES, "new-engine", ENV)), set(selected.SUITES))
        for key in ("base", "tree"):
            altered = dict(context, **{key: "f" * 40})
            self.assertEqual(evidence.reuse(altered, SIGNATURES, "new-engine", ENV), {})
        self.assertEqual(evidence.reuse(context, SIGNATURES, "new-engine", {"runner": "other"}), {})
        value["source_head"] = "f" * 40  # Same tree is insufficient for a different PR source head.
        self.assertEqual(evidence.reuse(context, SIGNATURES, "new-engine", ENV), {})

    def test_corpus_input_mismatch_selects_copy_suites(self):
        value = receipt()
        value["head"] = B
        evidence = selected.Evidence("owner/repo", "fixture-token")
        evidence.candidates = lambda context: [{"run_id": 7, "source_head": A}]
        evidence.load = lambda run, engine: (value, {"run_id": 7, "run_attempt": 2, "job_id": 11})
        signatures = dict(SIGNATURES, **{name: "2" * 64 for name in selected.CORPUS})
        context = {"event": "pull_request", "base": B}
        self.assertEqual(set(evidence.reuse(context, signatures, "engine", ENV)), {"skeleton", "selector"})

    def test_only_direct_executed_origins_can_be_reused(self):
        value = receipt()
        value["head"] = B
        reference = {"run_id": 8, "run_attempt": 1, "job_id": 12}
        for result in value["suites"].values():
            result.update(result="reused", origin=reference)
        root = receipt()
        evidence = selected.Evidence("owner/repo", "fixture-token")
        evidence.candidates = lambda context: [{"run_id": 7, "source_head": A}]
        evidence.load = lambda run, engine: (value, {}) if run == 7 else (root, reference)
        context = {"event": "pull_request", "base": B}
        self.assertEqual(set(evidence.reuse(context, SIGNATURES, "engine", ENV)), set(selected.SUITES))
        root["suites"]["skeleton"].update(result="reused", origin=reference)
        self.assertNotIn("skeleton", evidence.reuse(context, SIGNATURES, "engine", ENV))
        root["suites"]["content"]["input"] = "3" * 64
        self.assertNotIn("content", evidence.reuse(context, SIGNATURES, "engine", ENV))
        for key in ("run_attempt", "job_id"):
            wrong_reference = dict(reference, **{key: reference[key] + 1})
            evidence.load = lambda run, engine: (value, {}) if run == 7 else (root, wrong_reference)
            self.assertEqual(evidence.reuse(context, SIGNATURES, "engine", ENV), {})

    def test_pr_direct_source_checkout_is_not_receipt_evidence(self):
        value = receipt("pull_request")
        value["head"] = value["source_head"]
        evidence, engine = self.evidence(value=value)
        evidence.get = lambda suffix, raw=False: ({"tree": {"sha": D}, "parents": [{"sha": B}]}
                                                 if suffix == "/git/commits/" + C else original(suffix, raw))
        original = self.evidence(value=value)[0].get
        with engine, self.assertRaises(ValueError):
            evidence.load(7, "engine")

    def test_external_redirect_drops_authorization(self):
        request = urllib.request.Request("https://api.github.com/repos/owner/repo/actions/jobs/11/logs",
                                         headers={"Authorization": "Bearer fixture-token"})
        redirected = selected.SafeRedirect().redirect_request(request, None, 302, "Found", {},
                                                              "https://example.invalid/signed-log")
        self.assertFalse(redirected.has_header("Authorization"))
        with self.assertRaises(ValueError):
            selected.SafeRedirect().redirect_request(request, None, 302, "Found", {}, "http://example.invalid/log")

    def test_evidence_lookup_budget_falls_back_without_network(self):
        evidence = selected.Evidence("owner/repo", "fixture-token")
        evidence.deadline = 0
        with patch.object(evidence.opener, "open") as opened, self.assertRaises(TimeoutError):
            evidence.get("/actions/runs/7")
        opened.assert_not_called()


class RouteTests(unittest.TestCase):
    def test_push_uses_event_before_even_when_origin_equals_head(self):
        payload = {"before": B, "after": A}
        with patch.dict(os.environ, {"GITHUB_EVENT_NAME": "push", "GITHUB_EVENT_PATH": "fixture"}), \
             patch.object(Path, "read_text", return_value=json.dumps(payload)), \
             patch.object(selected, "commit", side_effect=lambda root, ref: A if ref == "HEAD" else ref), \
             patch.object(selected, "parents", return_value=[B]), \
             patch.object(selected, "tree", return_value=D), patch.object(selected, "git", return_value=b""):
            self.assertEqual(selected.ci_context(Path("."))["base"], B)
            for before in ("0" * 40, C):
                payload["before"] = before
                with patch.object(Path, "read_text", return_value=json.dumps(payload)), self.assertRaises(ValueError):
                    selected.ci_context(Path("."))

    def test_pr_source_base_and_synthetic_checkout_are_separate(self):
        payload = {"pull_request": {"base": {"sha": B, "ref": "rewrite-main"}, "head": {"sha": C}}}
        with patch.dict(os.environ, {"GITHUB_EVENT_NAME": "pull_request", "GITHUB_EVENT_PATH": "fixture"}), \
             patch.object(Path, "read_text", return_value=json.dumps(payload)), \
             patch.object(selected, "commit", side_effect=lambda root, ref: A if ref == "HEAD" else ref), \
             patch.object(selected, "parents", return_value=[B, C]), patch.object(selected, "tree", return_value=D), \
             patch.object(selected, "git", side_effect=lambda root, *args: B.encode() if args[0] == "merge-base" else b""):
            self.assertEqual(selected.ci_context(Path(".")),
                             {"event": "pull_request", "head": A, "source_head": C, "base": B, "tree": D})
            with patch.object(selected, "parents", return_value=[B, D]), self.assertRaises(ValueError):
                selected.ci_context(Path("."))

    def main_route(self, event, full_reason, accepted, failure=None, input_error=None):
        calls = []
        context = {"event": event, "head": A, "source_head": A, "base": B, "tree": D}
        def run(root, command):
            calls.append(command)
            if failure and any(failure in part for part in command):
                raise subprocess.CalledProcessError(1, command)
        arguments = ["check-selected.py", "--ci"]
        env = {"GITHUB_REPOSITORY": "owner/repo", "GH_TOKEN": "fixture-token",
               "GITHUB_RUN_ID": "9", "GITHUB_RUN_ATTEMPT": "1"}
        with patch.object(sys, "argv", arguments), patch.dict(os.environ, env, clear=True), \
             patch.object(selected, "ci_context", return_value=context), \
             patch.object(selected, "classify", return_value=(["scripts/check-selected.py"], full_reason)), \
             patch.object(selected, "environment", return_value=ENV), \
             patch.object(selected, "inputs", return_value=(SIGNATURES, "engine"), side_effect=input_error), \
             patch.object(selected.Evidence, "reuse", side_effect=accepted if isinstance(accepted, Exception) else None,
                          return_value={} if isinstance(accepted, Exception) else accepted) as reuse, \
             patch.object(selected, "run", side_effect=run), patch("sys.stdout", new=io.StringIO()):
            if failure:
                with self.assertRaises(subprocess.CalledProcessError):
                    selected.main()
            else:
                selected.main()
        return calls, reuse.call_count

    def test_engine_changed_pr_runs_full_without_using_old_evidence(self):
        calls, reuse_calls = self.main_route("pull_request", ["engine-change"], {})
        self.assertEqual(reuse_calls, 0)
        for script in selected.SUITES.values():
            self.assertTrue(any(command[0] == "scripts/" + script for command in calls))

    def test_new_engine_postmerge_reuses_pr_but_runs_current_transition_build(self):
        accepted = {name: {"run_id": 7, "run_attempt": 2, "job_id": 11} for name in selected.SUITES}
        calls, reuse_calls = self.main_route("push", ["engine-change"], accepted)
        self.assertEqual(reuse_calls, 1)
        self.assertFalse(any(command[0] == "scripts/" + script for command in calls for script in selected.SUITES.values()))
        self.assertIn(["scripts/check-base-diff-ci.sh", str(Path(__file__).resolve().parent.parent), B], calls)
        self.assertTrue(any(command[0] == "scripts/check-current.sh" for command in calls))
        self.assertEqual(calls[-1], ["lake", "build"])

    def test_missing_evidence_runs_all_and_failed_selected_gate_propagates(self):
        calls, _ = self.main_route("pull_request", [], {})
        self.assertEqual(sum(command[0].startswith("scripts/test-") for command in calls), 5)
        for failure in ("test-check-selected.py", "check-current", "check-base-diff-ci", "test-checkers",
                        "test-skeleton", "test-claim-corrections", "test-content", "test-base-diff-ci", "lake"):
            self.main_route("pull_request", [], {}, failure=failure)

    def test_api_lookup_failure_and_missing_history_execute_full(self):
        calls, _ = self.main_route("pull_request", [], OSError("unavailable API"))
        self.assertEqual(sum(command[0].startswith("scripts/test-") for command in calls), 5)
        calls, reuse_calls = self.main_route("pull_request", [], {},
                                             input_error=subprocess.CalledProcessError(1, ["git", "show"]))
        self.assertEqual(reuse_calls, 0)
        self.assertEqual(sum(command[0].startswith("scripts/test-") for command in calls), 5)


if __name__ == "__main__":
    unittest.main(verbosity=2)
