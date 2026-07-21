#!/usr/bin/env python3
"""Regression tests for audit_gate.py's V4 build-root reachability check.

Run: python3 scripts/audit/test_audit_gate_reachability.py

The check exists because of a real, green-build regression (PR #5099): deleting
one `import` line — the only in-repo reference to a module — dropped two modules
out of the import-closure of `defaultTargets`, so lake stopped compiling them and
they left the warning / `#print axioms` / sorry-free perimeter without any error.

`TestGateExitCodes` drives the real `scripts/audit_gate.py` **through `main()` and
its exit code** in a throwaway `git worktree` of the current commit: a gate that
silently passes is worse than no gate, and helper-level unit tests cannot see a
wiring mistake in `main()` (the first round of this check had two — HEAD's roots
were applied to the base graph, and an unreadable lakefile made V4 a no-op; both
were green at helper level). Every case asserts BOTH directions: a tree that
really orphans a module must exit 1, and one that does not must exit 0.
"""
from __future__ import annotations
import copy
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
GATE = str(REPO_ROOT / "scripts" / "audit_gate.py")
sys.path.insert(0, str(REPO_ROOT / "scripts"))
import audit_gate as A  # noqa: E402

# The PR #5099 regression, verbatim: the importer, the import line that was
# deleted, and the two modules that silently left the build.
HNE_PATH = ("LatticeSystem/Quantum/SpinS/"
            "AnisotropicHeisenbergSpinHalfObligation2AxiomaticV3Hne.lean")
HNE = A.module_of_path(HNE_PATH)
DELETED_IMPORT = ("LatticeSystem.Quantum.SpinS."
                  "AnisotropicHeisenbergCrossingDualSectorGroundExplicit")
COLLATERAL = ("LatticeSystem.Quantum.SpinS."
              "AnisotropicHeisenbergParametricGapCrossingGeneric")

ROOTS = ["LatticeSystem", "LatticeSystem.Tests"]

BLOCKED, FAILED_CLOSED = 1, 2


def drop_edge(graph, importer, imported):
    """A copy of `graph` with one import line removed (what PR #5099 did)."""
    out = copy.deepcopy(graph)
    out[importer] = [d for d in out[importer] if d != imported]
    return out


class TestLakefileRoots(unittest.TestCase):
    """Roots come from the lakefile; they are never hardcoded in the gate."""

    def test_real_lakefile(self):
        text = (REPO_ROOT / "lakefile.toml").read_text(encoding="utf-8")
        self.assertEqual(A.build_roots(text), ROOTS)

    def test_single_quoted_toml(self):
        # TOML accepts either quote; reading only one form would drop the roots
        # and (before the fail-closed rule) make V4 pass on any tree at all.
        self.assertEqual(
            A.build_roots("defaultTargets = ['LatticeSystem', 'LatticeSystem.Tests']"),
            ROOTS)

    def test_multiline_array(self):
        self.assertEqual(
            A.build_roots('defaultTargets = [\n  "A",\n  "B",\n]'), ["A", "B"])

    def test_absent_default_targets_reads_no_roots(self):
        self.assertEqual(A.build_roots('name = "X"\n[leanOptions]\n'), [])

    def test_lakefile_lean_reads_no_roots(self):
        # A migration to the Lean DSL must be *detected* (callers fail closed),
        # not read as "zero roots, nothing to check" — even if the file's text
        # would happen to match the TOML shape.
        self.assertEqual(A.roots_from_lakefile(
            "lakefile.lean", 'defaultTargets = ["LatticeSystem"]'), [])
        self.assertEqual(A.roots_from_lakefile(
            "lakefile.toml", 'defaultTargets = ["LatticeSystem"]'), ["LatticeSystem"])
        self.assertEqual(A.roots_from_lakefile(None, None), [])

    def test_roots_are_read_not_assumed(self):
        self.assertEqual(A.build_roots('defaultTargets = ["Only.One"]'), ["Only.One"])


class TestModulePaths(unittest.TestCase):
    def test_round_trip(self):
        p = "LatticeSystem/Quantum/SpinS/Foo.lean"
        self.assertEqual(A.module_of_path(p), "LatticeSystem.Quantum.SpinS.Foo")
        self.assertEqual(A.path_of_module("LatticeSystem.Quantum.SpinS.Foo"), p)

    def test_umbrella_root_module(self):
        self.assertEqual(A.module_of_path("LatticeSystem.lean"), "LatticeSystem")


class TestImportParsing(unittest.TestCase):
    def test_real_imports(self):
        self.assertEqual(
            A.imports_of_text("import Mathlib.Data.Real.Basic\n"
                              "import LatticeSystem.Math.FinCases\n\ntheorem x : True\n"),
            ["LatticeSystem.Math.FinCases"])

    def test_commented_out_imports_are_not_edges(self):
        # A docstring quoting an import must not keep a module alive on paper.
        self.assertEqual(A.imports_of_text(
            "/-- usage:\nimport LatticeSystem.Ghost\n-/\n"
            "-- import LatticeSystem.AlsoGhost\n"
            "import LatticeSystem.Real\n"), ["LatticeSystem.Real"])


class TestSyntheticGraphs(unittest.TestCase):
    """Minimal graphs shaped like the real one (two roots, a chain below)."""

    BASE = {
        "LatticeSystem": ["LatticeSystem.A"],
        "LatticeSystem.Tests": ["LatticeSystem.T"],
        "LatticeSystem.A": ["LatticeSystem.B"],
        "LatticeSystem.B": [],
        "LatticeSystem.T": ["LatticeSystem.B"],
        "LatticeSystem.Orphan": [],
    }

    def regressions(self, head, head_roots=ROOTS, base_roots=ROOTS):
        return A.reachability_regressions(self.BASE, base_roots, head, head_roots)

    def test_pre_existing_orphan_is_grandfathered(self):
        # Orphan is unreachable at base AND at HEAD: the ratchet must stay quiet.
        self.assertEqual(A.unreachable_modules(self.BASE, ROOTS),
                         {"LatticeSystem.Orphan"})
        self.assertEqual(self.regressions(dict(self.BASE)), [])

    def test_sole_importer_edge_deletion_fails(self):
        head = drop_edge(self.BASE, "LatticeSystem", "LatticeSystem.A")
        self.assertEqual(self.regressions(head), ["LatticeSystem.A"])

    def test_transitive_collateral_is_reported(self):
        head = drop_edge(self.BASE, "LatticeSystem", "LatticeSystem.A")
        head = drop_edge(head, "LatticeSystem.T", "LatticeSystem.B")
        self.assertEqual(self.regressions(head),
                         ["LatticeSystem.A", "LatticeSystem.B"])

    def test_surviving_importer_means_no_regression(self):
        # B keeps its test-side importer, so dropping A -> B changes nothing.
        head = drop_edge(self.BASE, "LatticeSystem.A", "LatticeSystem.B")
        self.assertEqual(self.regressions(head), [])

    def test_test_root_counts_as_a_root(self):
        head = drop_edge(self.BASE, "LatticeSystem.Tests", "LatticeSystem.T")
        self.assertEqual(self.regressions(head), ["LatticeSystem.T"])

    def test_deleting_a_build_root_is_a_regression(self):
        # The strictly worse form of #5099: one lakefile line orphans a subtree.
        # Each side must use its OWN roots, or this is invisible.
        self.assertEqual(self.regressions(dict(self.BASE),
                                          head_roots=["LatticeSystem"]),
                         ["LatticeSystem.T", "LatticeSystem.Tests"])

    def test_adding_a_build_root_is_not_a_regression(self):
        self.assertEqual(
            self.regressions(dict(self.BASE),
                             head_roots=ROOTS + ["LatticeSystem.Orphan"]), [])

    def test_new_unwired_module_is_caught(self):
        head = dict(self.BASE)
        head["LatticeSystem.Fresh"] = []
        self.assertEqual(self.regressions(head), ["LatticeSystem.Fresh"])

    def test_new_wired_module_passes(self):
        head = dict(self.BASE)
        head["LatticeSystem.Fresh"] = []
        head["LatticeSystem.B"] = ["LatticeSystem.Fresh"]
        self.assertEqual(self.regressions(head), [])

    def test_deleting_a_module_is_not_a_regression(self):
        head = drop_edge(self.BASE, "LatticeSystem.A", "LatticeSystem.B")
        head = drop_edge(head, "LatticeSystem.T", "LatticeSystem.B")
        del head["LatticeSystem.B"]
        self.assertEqual(self.regressions(head), [])


class TestRealTree(unittest.TestCase):
    """Real data: the tree as it stands, and the PR #5099 replay on it."""

    @classmethod
    def setUpClass(cls):
        os.chdir(REPO_ROOT)
        cls.graph = A.import_graph_worktree()

    def test_tree_is_indexed(self):
        # An empty graph would make every later assertion vacuously true.
        self.assertGreater(len(self.graph), 1000)
        self.assertIn(HNE, self.graph)

    def test_current_tree_has_no_unreachable_module(self):
        self.assertEqual(sorted(A.unreachable_modules(self.graph, ROOTS)), [])

    def test_git_reader_agrees_with_the_worktree_reader(self):
        # The base-ref side is read with git, the HEAD side from the filesystem;
        # on a clean tree the two must produce the same graph.
        at_head = A.import_graph_at_ref("HEAD")
        self.assertEqual({k: sorted(v) for k, v in at_head.items()},
                         {k: sorted(v) for k, v in self.graph.items()})

    def test_pr5099_import_deletion_is_detected(self):
        self.assertIn(DELETED_IMPORT, self.graph[HNE])
        head = drop_edge(self.graph, HNE, DELETED_IMPORT)
        self.assertEqual(
            A.reachability_regressions(self.graph, ROOTS, head, ROOTS),
            sorted([DELETED_IMPORT, COLLATERAL]))

    def test_removing_a_redundant_import_is_allowed(self):
        # The gate must not veto real import cleanups, only orphaning ones.
        importers = {}
        for m, deps in self.graph.items():
            for d in deps:
                importers.setdefault(d, []).append(m)
        target, ms = next((d, ms) for d, ms in sorted(importers.items())
                          if len(ms) >= 2)
        head = drop_edge(self.graph, sorted(ms)[0], target)
        self.assertEqual(A.reachability_regressions(self.graph, ROOTS, head, ROOTS),
                         [])


class TestGateExitCodes(unittest.TestCase):
    """End-to-end: run the real gate and assert its exit code.

    Each case mutates a throwaway `git worktree` of the current commit and runs
    `audit_gate.py --diff main` there, so `main()`'s wiring — which roots go with
    which graph, what happens when the lakefile is unreadable, whether an
    uncommitted lakefile is trusted — is actually exercised.
    """

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="audit-gate-v4-")
        cls.wt = os.path.join(cls.tmp, "wt")
        cls.base = cls._git(REPO_ROOT, "rev-parse", "HEAD").strip()
        cls._git(REPO_ROOT, "worktree", "add", "--detach", "-q", cls.wt, cls.base)

    @classmethod
    def tearDownClass(cls):
        cls._git(REPO_ROOT, "worktree", "remove", "--force", cls.wt)
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @staticmethod
    def _git(cwd, *args):
        return subprocess.run(["git", *args], cwd=str(cwd), capture_output=True,
                              text=True, check=True).stdout

    def setUp(self):
        self._git(self.wt, "reset", "--hard", "-q", self.base)
        self._git(self.wt, "clean", "-qfd")

    def commit(self, message):
        self._git(self.wt, "add", "-A")
        self._git(self.wt, "-c", "core.hooksPath=/dev/null",
                  "commit", "-q", "-m", message)

    def edit(self, relpath, transform):
        p = Path(self.wt) / relpath
        p.write_text(transform(p.read_text(encoding="utf-8")), encoding="utf-8")

    def orphan_the_module(self):
        """Exactly the PR #5099 diff: drop the only in-repo import of a module.
        (It was reverted before that PR merged, so the replay is made here.)"""
        self.edit(HNE_PATH, lambda t: "".join(
            l for l in t.splitlines(True)
            if not l.startswith(f"import {DELETED_IMPORT}")))

    def gate(self):
        r = subprocess.run([sys.executable, GATE, "--diff", "main"], cwd=self.wt,
                           capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    # --- the tree as pushed --------------------------------------------------

    def test_clean_head_passes(self):
        code, out = self.gate()
        self.assertEqual(code, 0, out)
        self.assertIn("OK", out)

    # --- V4 blocks ------------------------------------------------------------

    def test_pr5099_import_deletion_exits_blocked(self):
        self.orphan_the_module()
        self.commit("repro: delete the PR #5099 import line")
        code, out = self.gate()
        self.assertEqual(code, BLOCKED, out)
        self.assertIn("V4 newly unreachable module", out)
        self.assertIn(A.path_of_module(DELETED_IMPORT), out)
        self.assertIn(A.path_of_module(COLLATERAL), out)

    def test_deleting_a_build_root_exits_blocked(self):
        self.edit("lakefile.toml", lambda t: t.replace(
            'defaultTargets = ["LatticeSystem", "LatticeSystem.Tests"]',
            'defaultTargets = ["LatticeSystem"]'))
        self.commit("repro: drop a build root")
        code, out = self.gate()
        self.assertEqual(code, BLOCKED, out)
        self.assertIn("V4 newly unreachable module", out)

    def test_new_unwired_module_exits_blocked(self):
        (Path(self.wt) / "LatticeSystem" / "Math" / "GateV4Probe.lean").write_text(
            "import LatticeSystem.Math.FinCases\n", encoding="utf-8")
        self.commit("repro: add a module no root imports")
        code, out = self.gate()
        self.assertEqual(code, BLOCKED, out)
        self.assertIn("LatticeSystem/Math/GateV4Probe.lean", out)

    def test_wiring_the_new_module_in_passes(self):
        (Path(self.wt) / "LatticeSystem" / "Math" / "GateV4Probe.lean").write_text(
            "import LatticeSystem.Math.FinCases\n", encoding="utf-8")
        self.edit("LatticeSystem.lean",
                  lambda t: "import LatticeSystem.Math.GateV4Probe\n" + t)
        self.commit("repro: add a module and wire it into the root")
        code, out = self.gate()
        self.assertEqual(code, 0, out)

    # --- fail closed rather than no-op ---------------------------------------

    def test_missing_default_targets_fails_closed(self):
        self.edit("lakefile.toml", lambda t: "".join(
            l for l in t.splitlines(True) if "defaultTargets" not in l))
        self.commit("repro: remove defaultTargets")
        code, out = self.gate()
        self.assertEqual(code, FAILED_CLOSED, out)
        self.assertIn("no build roots readable", out)

    def test_lakefile_lean_migration_fails_closed(self):
        self._git(self.wt, "mv", "lakefile.toml", "lakefile.lean")
        self.commit("repro: migrate to lakefile.lean")
        code, out = self.gate()
        self.assertEqual(code, FAILED_CLOSED, out)
        self.assertIn("lakefile.lean", out)

    def test_both_lakefiles_present_follows_lake_and_fails_closed(self):
        # Lake builds from lakefile.lean when both exist (Package.lean:68-76), so
        # an added .lean config silently re-targets the build. Reading the TOML
        # first would leave the gate reporting on roots lake no longer uses.
        (Path(self.wt) / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\n\npackage «LatticeSystem»\n\n"
            "@[default_target]\nlean_lib «LatticeSystem»\n", encoding="utf-8")
        self.commit("repro: add lakefile.lean next to lakefile.toml")
        code, out = self.gate()
        self.assertEqual(code, FAILED_CLOSED, out)
        self.assertIn("lakefile.lean", out)

    def test_single_quoted_toml_still_reads_the_roots(self):
        # The alternative quote form must be understood: not fail closed, and not
        # silently pass — an orphaning tree written this way still has to block.
        self.edit("lakefile.toml", lambda t: t.replace(
            'defaultTargets = ["LatticeSystem", "LatticeSystem.Tests"]',
            "defaultTargets = ['LatticeSystem', 'LatticeSystem.Tests']"))
        self.commit("repro: single-quoted defaultTargets")
        code, out = self.gate()
        self.assertEqual(code, 0, out)
        self.orphan_the_module()
        self.commit("repro: ... and orphan a module")
        code, out = self.gate()
        self.assertEqual(code, BLOCKED, out)

    def test_uncommitted_lakefile_is_not_trusted(self):
        # Orphan committed, then "fixed" only in the working tree: the pushed
        # state still orphans the module, so the gate must not accept it.
        self.orphan_the_module()
        self.commit("repro: orphan a module")
        self.edit("lakefile.toml", lambda t: t.replace(
            '"LatticeSystem.Tests"]',
            f'"LatticeSystem.Tests", "{DELETED_IMPORT}"]'))
        code, out = self.gate()
        self.assertEqual(code, FAILED_CLOSED, out)
        self.assertIn("lakefile", out)

    def test_uncommitted_lean_change_is_not_trusted(self):
        # The pre-existing fail-closed rule must keep working unchanged.
        self.edit(HNE_PATH, lambda t: t + "\n-- scratch\n")
        code, out = self.gate()
        self.assertEqual(code, FAILED_CLOSED, out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
