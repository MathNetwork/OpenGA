"""Offline checks: python3 -m unittest discover -s PoincareConjecture -p 'test_*.py'."""

import json
from pathlib import Path
import tempfile
import unittest

from sync import Client, MISSION_ID, collect, expand_dependency_graph, install, module_name, resolve_additional_theorems, review_status


class SyncTests(unittest.TestCase):
    def test_structural_definitions_in_graph_are_mirrored_without_proof_imports(self):
        client = Client.__new__(Client)
        client.pages = lambda path, key, **params: ([{"id": MISSION_ID,
            "main_theorem": {"theorem_id": "root"}}] if path == "/missions" else [])
        graph = {"root_id": "root", "nodes": [
            {"node_type": "theorem", "theorem_id": "root", "mathlib_rev": "rev"},
            {"node_type": "theorem", "theorem_id": "definition", "status": "Definition"}],
            "edges": [{"source": "definition", "target": "root", "kind": "structural"}]}
        responses = {
            "/theorems/root/graph": graph,
            "/theorems/root": {"theorem_id": "root", "theorem_name": "Target",
                "status": "Open", "mathlib_rev": "rev", "preamble": "", "formal_statement": "theorem Target : True := by sorry"},
            "/theorems/definition": {"theorem_id": "definition", "theorem_name": "Data",
                "status": "Definition", "mathlib_rev": "rev", "definition": "def Data := Nat\n"},
            "/theorems/root/decompositions": {"decompositions": []},
            "/environments": {"environments": [{"mathlib_rev": "rev"}]}}
        client.request = responses.__getitem__
        files, snapshot = collect(client)
        self.assertEqual(files["Definitions/Def_Data.lean"], b"def Data := Nat\n")
        self.assertIn("definition", snapshot["nodes"])

    def test_folded_dependency_frontiers_are_expanded_without_inventing_edges(self):
        root = {"root_id": "root", "nodes": [
            {"theorem_id": "root"}, {"theorem_id": "budget", "has_more_children": True}],
            "edges": [{"source": "budget", "target": "root", "kind": "structural"}]}
        branches = {
            "/theorems/budget/graph": {"nodes": [
                {"theorem_id": "budget", "has_more_children": False},
                {"theorem_id": "model", "has_more_children": True}],
                "edges": [{"source": "model", "target": "budget", "kind": "structural"}]},
            "/theorems/model/graph": {"nodes": [
                {"theorem_id": "model", "has_more_children": False},
                {"theorem_id": "density", "has_more_children": False}],
                "edges": [{"source": "density", "target": "model", "kind": "structural"}]}}
        client = Client.__new__(Client)
        calls = []
        def request(path):
            calls.append(path)
            return branches[path]
        client.request = request
        expanded = expand_dependency_graph(client, root)
        self.assertEqual(calls, list(branches))
        self.assertEqual({n["theorem_id"] for n in expanded["nodes"]},
                         {"root", "budget", "model", "density"})
        self.assertEqual(expanded["edges"], root["edges"] +
                         branches[calls[0]]["edges"] + branches[calls[1]]["edges"])
        with self.assertRaisesRegex(RuntimeError, "incomplete"):
            expand_dependency_graph(client, root, max_expansions=1)

    def test_exact_bytes_and_repeat_sync(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = {"Solutions/Sol_example.lean": "-- π\n\ntheorem solution : True := by trivial\n".encode()}
            self.assertEqual(install(root, files, {"nodes": {}}), 1)
            self.assertEqual((root / "Solutions/Sol_example.lean").read_bytes(), files["Solutions/Sol_example.lean"])
            self.assertEqual(install(root, files, {"nodes": {}}), 0)

    def test_local_changes_abort_before_any_write(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = {"Theorems/A.lean": b"original", "Solutions/B.lean": b"original"}
            install(root, files, {})
            (root / "Solutions/B.lean").write_bytes(b"local proof")
            previous_manifest = (root / "sync.json").read_bytes()
            with self.assertRaisesRegex(RuntimeError, "Local changes"):
                install(root, {"Theorems/A.lean": b"new", "Solutions/B.lean": b"remote proof"}, {})
            self.assertEqual((root / "Theorems/A.lean").read_bytes(), b"original")
            self.assertEqual((root / "Solutions/B.lean").read_bytes(), b"local proof")
            self.assertEqual((root / "sync.json").read_bytes(), previous_manifest)

    def test_unlisted_sources_are_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            install(root, {"Solutions/Old.lean": b"old"}, {})
            install(root, {"Solutions/New.lean": b"new"}, {})
            self.assertEqual((root / "Solutions/Old.lean").read_bytes(), b"old")
            manifest = json.loads((root / "sync.json").read_text())
            self.assertEqual(manifest["retained_files"], ["Solutions/Old.lean"])

    def test_symlink_and_path_traversal_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "destination").mkdir()
            (root / "Solutions").symlink_to(root / "destination")
            with self.assertRaisesRegex(RuntimeError, "symlink"):
                install(root, {"Solutions/Test.lean": b"bad"}, {})
            with self.assertRaises(ValueError):
                install(root, {"../outside.lean": b"bad"}, {})
            with self.assertRaises(ValueError):
                module_name("../../outside")

    def test_both_pagination_shapes(self):
        for nested in (False, True):
            client = Client.__new__(Client)
            responses = [{"rows": [1, 2]}, {"rows": [3]}]
            for response in responses:
                if nested:
                    response["pagination"] = {"total": 3}
                else:
                    response["total"] = 3
            paths = []

            def request(path):
                paths.append(path)
                return responses.pop(0)

            client.request = request
            self.assertEqual(client.pages("/test", "rows"), [1, 2, 3])
            self.assertIn("offset=2", paths[1])

    def test_incomplete_pagination_fails(self):
        client = Client.__new__(Client)
        client.request = lambda path: {"rows": [], "total": 2}
        with self.assertRaisesRegex(RuntimeError, "Incomplete pagination"):
            client.pages("/test", "rows")


class AdditionalTargetTests(unittest.TestCase):
    def test_exact_name_and_environment_are_used_and_duplicates_are_deduplicated(self):
        client = Client.__new__(Client)
        calls = []

        def pages(path, key, **params):
            calls.append((path, key, params))
            return [
                {"theorem_name": "OpenGA.result_helper", "mathlib_rev": "rev", "theorem_id": "other"},
                {"theorem_name": "OpenGA.result", "mathlib_rev": "rev", "theorem_id": "wanted"},
                {"theorem_name": "OpenGA.result", "mathlib_rev": "old-rev", "theorem_id": "old"},
            ]

        client.pages = pages
        self.assertEqual(resolve_additional_theorems(client, ["OpenGA.result", "OpenGA.result"], "rev"),
                         {"OpenGA.result": "wanted"})
        self.assertEqual(calls, [("/theorems", "theorems", {"theorem_name": "OpenGA.result", "env": "rev"})])

    def test_missing_deprecated_and_ambiguous_targets_are_rejected(self):
        row = {"theorem_name": "OpenGA.result", "mathlib_rev": "rev", "theorem_id": "id"}
        for rows in ([], [dict(row, deprecated_at="date")], [row, dict(row, theorem_id="second")],
                     [dict(row, mathlib_rev="old-rev")]):
            with self.subTest(rows=rows):
                client = Client.__new__(Client)
                client.pages = lambda *args, **kwargs: rows
                with self.assertRaisesRegex(RuntimeError, "one active theorem"):
                    resolve_additional_theorems(client, ["OpenGA.result"], "rev")

    def test_invalid_names_are_rejected_before_network_access(self):
        client = Client.__new__(Client)
        for name in ("../escape", "OpenGA.result?env=old", "OpenGA..result", "", 3):
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, "Invalid additional theorem name"):
                    resolve_additional_theorems(client, [name], "rev")


class ReviewTests(unittest.TestCase):
    def setUp(self):
        self.snapshot = {"mission": {"id": "mission"},
                         "nodes": {"theorem": {"mathlib_rev": "rev"}},
                         "submissions": {"proof": {"theorem_id": "theorem", "status": "ACCEPTED",
                                                    "local_path": "Solutions/Proof.lean"}},
                         "file_hashes": {"Solutions/Proof.lean": "hash"}}
        self.review = {"mission_id": "mission", "reviews": {
            "proof": {"status": "integrated", "source_theorem_id": "theorem",
                      "source_status": "ACCEPTED", "source_mathlib_rev": "rev", "source_sha256": "hash"}}}

    def test_new_proof_is_never_automatically_integrated(self):
        status = review_status(self.snapshot, {})
        self.assertEqual(status["new_proofs"], ["proof"])
        self.assertEqual(status["integrated"], [])

    def test_reviewed_proof_is_recognized(self):
        self.assertEqual(review_status(self.snapshot, self.review)["integrated"], ["proof"])

    def test_changed_source_requires_review(self):
        self.snapshot["file_hashes"]["Solutions/Proof.lean"] = "changed"
        self.assertEqual(review_status(self.snapshot, self.review)["needs_review"], ["proof"])

    def test_deprecated_or_missing_source_requires_review(self):
        self.snapshot["nodes"]["theorem"]["deprecated_at"] = "today"
        self.assertEqual(review_status(self.snapshot, self.review)["needs_review"], ["proof"])
        self.snapshot["submissions"] = {}
        self.assertEqual(review_status(self.snapshot, self.review)["needs_review"], ["proof"])

    def test_completed_sketch_is_reconsidered(self):
        self.review["reviews"]["proof"]["source_status"] = "SKETCH_ACCEPTED"
        self.review["reviews"]["proof"]["status"] = "partially_integrated"
        self.assertEqual(review_status(self.snapshot, self.review)["needs_review"], ["proof"])


if __name__ == "__main__":
    unittest.main()
