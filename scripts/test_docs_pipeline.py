#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Regression tests for R2 publication, SQLite snapshots and portal validation."""

from __future__ import annotations

import ast
from contextlib import contextmanager
import io
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import build_site
import docs_cache as cache

SOURCE = Path(__file__).resolve().parents[1]


@contextmanager
def fixture():
    previous = Path.cwd()
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        os.chdir(root)
        try:
            for name in cache.INPUTS:
                if name == "Qatlib":
                    continue
                path = Path(name)
                path.parent.mkdir(parents=True, exist_ok=True)
                if name in ("lake-manifest.json", "docbuild/lake-manifest.json"):
                    path.write_text('{"packages": []}\n')
                else:
                    path.write_text("fixture\n")
            Path("Qatlib").mkdir()
            Path("Qatlib/Example.lean").write_text("def example := 1\n")
            Path("lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
            subprocess.run(["git", "init", "-q"], check=True)
            subprocess.run(["git", "add", "."], check=True)
            yield root
        finally:
            os.chdir(previous)


def api_files(root: Path, doc: Path) -> None:
    names = ["index.html", "navbar.html", "style.css", "search.html", "search.js",
             "declaration-data.js", "references.html", "Qatlib.html",
             "declarations/declaration-data.bmp"]
    names.extend(str(p.relative_to(root).with_suffix(".html")) for p in (root / "Qatlib").rglob("*.lean"))
    for name in names:
        path = doc / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("raw API\n")


@contextmanager
def snapshot_store():
    objects = {}

    def download(key, path):
        key = key.split("?", 1)[0]
        if key not in objects:
            return False
        path.write_bytes(objects[key])
        return True

    with patch.object(cache, "put", side_effect=lambda key, path: objects.update({key: path.read_bytes()})), \
            patch.object(cache, "get", side_effect=download):
        yield objects


def analysis_files() -> None:
    cache.BUILD.mkdir(parents=True)
    data = cache.BUILD / "doc-data"
    data.mkdir()
    (data / "Qatlib.Example.doc").write_text("analysis marker")
    with cache.database(cache.BUILD / "api-docs.db") as connection:
        connection.execute("CREATE TABLE modules(name TEXT PRIMARY KEY, source_url TEXT)")
        connection.execute("INSERT INTO modules VALUES ('Qatlib.Example', 'old-url')")


class DocsPipelineTests(unittest.TestCase):
    def test_portal_inputs_reuse_html_but_bibliography_and_lean_invalidate_it(self):
        with fixture():
            original = cache.identity()
            for name in ("README.md", "scripts/build_site.py", "docs/architecture.md"):
                path = Path(name)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("portal change")
                subprocess.run(["git", "add", name], check=True)
            self.assertEqual(cache.identity(), original)
            Path("docs/references.bib").write_text("new bibliography")
            subprocess.run(["git", "add", "docs/references.bib"], check=True)
            changed = cache.identity()
            self.assertNotEqual(changed[1], original[1])
            self.assertEqual(changed[2], original[2])
            Path("Qatlib/Example.lean").write_text("def example := 2\n")
            subprocess.run(["git", "add", "Qatlib/Example.lean"], check=True)
            self.assertNotEqual(cache.identity()[1], changed[1])
            Path("docbuild/lake-manifest.json").write_text('{"packages": [1]}')
            self.assertNotEqual(cache.identity()[2], original[2])

    def test_html_round_trip_and_corruption_leave_existing_output_untouched(self):
        with fixture() as root:
            doc = cache.BUILD / "doc"
            api_files(root, doc)

            def retire(path):
                if path.exists():
                    shutil.move(str(path), root / ("retired-" + path.name))

            with snapshot_store() as objects, patch.object(cache, "trash", side_effect=retire):
                cache.publish("html")
                prefix, fingerprint, _ = cache.identity()
                self.assertEqual(set(objects), {f"{prefix}/html/{fingerprint}.tar.gz",
                                                f"{prefix}/html/{fingerprint}.json"})
                self.assertTrue(cache.restore("html"))
                self.assertEqual((doc / "Qatlib.html").read_text(), "raw API\n")
                key = next(k for k in objects if k.endswith(".tar.gz"))
                objects[key] = b"corrupt"
                with self.assertRaisesRegex(RuntimeError, "checksum"):
                    cache.restore("html")
                self.assertTrue((doc / "Qatlib.html").is_file())
                objects.clear()
                self.assertFalse(cache.restore("html"))

    def test_analysis_backup_includes_wal_and_only_analysis_markers(self):
        with fixture() as root:
            cache.BUILD.mkdir(parents=True)
            data = cache.BUILD / "doc-data"
            data.mkdir()
            for name in ("Qatlib.Example.doc", "Qatlib.Example.doc.trace", "core-Init.doc",
                         "references.json", "Qatlib--library.docs_built", "backrefs-old.json"):
                (data / name).write_text(name)
            (data / "Qatlib.Example.doc.trace").write_text(json.dumps(
                {"schemaVersion": "2025-09-10", "depHash": "0123456789abcdef"}))
            connection = sqlite3.connect(cache.BUILD / "api-docs.db")
            connection.execute("PRAGMA journal_mode=WAL")
            connection.execute("CREATE TABLE modules(name TEXT PRIMARY KEY, source_url TEXT)")
            connection.execute("INSERT INTO modules VALUES ('Qatlib.Example', 'old-url')")
            connection.commit()
            with snapshot_store() as objects:
                cache.publish("analysis")
            connection.close()
            self.assertTrue(next(reversed(objects)).endswith("/latest.json"))
            prefix, _, compatible = cache.identity()
            self.assertEqual(set(objects), {f"{prefix}/analysis/{compatible}/latest.tar.gz",
                                            f"{prefix}/analysis/{compatible}/latest.json"})
            archive = objects[f"{prefix}/analysis/{compatible}/latest.tar.gz"]
            with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as tar:
                names = tar.getnames()
                self.assertIn("doc-data/Qatlib.Example.doc.trace", names)
                self.assertNotIn("doc-data/Qatlib--library.docs_built", names)
                self.assertNotIn("doc-data/backrefs-old.json", names)
                tar.extractall(root / "backup", filter="data")
            with cache.database(root / "backup/api-docs.db") as backup:
                self.assertEqual(backup.execute("PRAGMA quick_check").fetchone(), ("ok",))
                url, = backup.execute("SELECT source_url FROM modules").fetchone()
                self.assertEqual(url, f"https://github.com/{cache.REPO}/blob/main/Qatlib/Example.lean")

    def test_analysis_traces_drop_working_paths_without_changing_dependency_hashes(self):
        with fixture() as root, snapshot_store() as objects:
            analysis_files()
            data = cache.BUILD / "doc-data"
            repo = "qatlib-" + "staging"
            workspace = "/" + "/".join(("home", "runner", "work", repo, repo))
            meta = {"schemaVersion": "2025-09-10", "depHash": "0123456789abcdef",
                    "inputs": [[workspace + "/module.olean", "fedcba9876543210"]],
                    "log": [{"level": "info", "message": workspace + "/module.lean"}],
                    "outputs": {"path": workspace + "/marker"}, "synthetic": False}
            names = ("QuantumInfo.ForMathlib.LinearEquiv.doc.trace", "core-Init.doc.trace",
                     "references.json.trace")
            for name in names:
                (data / name).write_text(json.dumps(meta))
            with self.assertRaisesRegex(RuntimeError, "private URL or machine path"):
                cache.verify_public([data])
            cache.publish("analysis")
            archive = next(value for key, value in objects.items() if key.endswith(".tar.gz"))
            with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as tar:
                tar.extractall(root / "backup", filter="data")
            cache.verify_public([root / "backup"])
            for name in names:
                self.assertEqual(json.loads((root / "backup/doc-data" / name).read_text()),
                                 {"schemaVersion": meta["schemaVersion"], "depHash": meta["depHash"]})
                # Publication sanitizes the copy and leaves local trace logs intact.
                self.assertEqual(json.loads((data / name).read_text()), meta)

    def test_analysis_trace_schema_changes_fail_before_upload(self):
        for meta in ("not JSON", '{"schemaVersion": "future", "depHash": "0123456789abcdef"}',
                     '{"schemaVersion": "2025-09-10", "depHash": "bad"}'):
            with self.subTest(meta=meta), fixture():
                analysis_files()
                (cache.BUILD / "doc-data/Qatlib.Example.doc.trace").write_text(meta)
                with patch.object(cache, "put") as upload:
                    with self.assertRaisesRegex(RuntimeError, "Lake analysis trace"):
                        cache.publish("analysis")
                    upload.assert_not_called()

    def test_database_and_html_publication_still_reject_machine_paths(self):
        with fixture() as root:
            analysis_files()
            api_files(root, cache.BUILD / "doc")
            private_path = "/" + "/".join(("home", "runner", "workspace"))
            with cache.database(cache.BUILD / "api-docs.db") as connection:
                connection.execute("INSERT INTO modules VALUES ('QuantumInfo.Example', ?)", (private_path,))
            (cache.BUILD / "doc/index.html").write_text(private_path)
            with patch.object(cache, "put") as upload:
                for kind in ("analysis", "html"):
                    with self.subTest(kind=kind), self.assertRaisesRegex(RuntimeError, "private URL or machine path"):
                        cache.publish(kind)
                upload.assert_not_called()

    def test_prune_commits_cascade_before_checkpoint_and_removes_stale_traces(self):
        with fixture() as root:
            cache.BUILD.mkdir(parents=True)
            data = cache.BUILD / "doc-data"
            data.mkdir()
            for name in ("Qatlib.Removed.doc", "Qatlib.Removed.doc.trace", "Qatlib.Example.doc"):
                (data / name).write_text("marker")
            with cache.database(cache.BUILD / "api-docs.db") as connection:
                connection.execute("PRAGMA journal_mode=WAL")
                connection.execute("CREATE TABLE modules(name TEXT PRIMARY KEY, source_url TEXT)")
                connection.execute("CREATE TABLE children(module TEXT REFERENCES modules(name) ON DELETE CASCADE)")
                connection.executemany("INSERT INTO modules(name) VALUES (?)", [("Qatlib.Removed",), ("Qatlib.Example",)])
                connection.execute("INSERT INTO children VALUES ('Qatlib.Removed')")

            def retire(path):
                shutil.move(str(path), root / path.name)

            with patch.object(cache, "trash", side_effect=retire):
                cache.prune()
            with cache.database(cache.BUILD / "api-docs.db") as connection:
                self.assertEqual(connection.execute("SELECT name FROM modules").fetchall(), [("Qatlib.Example",)])
                self.assertEqual(connection.execute("SELECT * FROM children").fetchall(), [])
            self.assertFalse((data / "Qatlib.Removed.doc.trace").exists())
            self.assertTrue((data / "Qatlib.Example.doc").exists())

    def test_busy_checkpoint_is_rejected(self):
        connection = unittest.mock.Mock()
        connection.execute.return_value.fetchone.return_value = (1, 10, 0)
        with self.assertRaisesRegex(RuntimeError, "busy"):
            cache.checkpoint(connection)
        connection.commit.assert_called_once()
        self.assertEqual(connection.method_calls[0][0], "commit")

    def test_upload_failure_does_not_publish_pointer(self):
        with fixture() as root:
            api_files(root, cache.BUILD / "doc")
            with patch.object(cache, "put", side_effect=RuntimeError("upload failed")) as upload:
                with self.assertRaisesRegex(RuntimeError, "upload failed"):
                    cache.publish("html")
                self.assertEqual(upload.call_count, 1)
                self.assertIn("/html/", upload.call_args.args[0])
                self.assertTrue(upload.call_args.args[0].endswith(".tar.gz"))

    def test_archives_are_deterministic_across_file_metadata_and_creation_order(self):
        with fixture() as root, snapshot_store() as objects:
            doc = cache.BUILD / "doc"
            api_files(root, doc)
            shutil.move(str(doc / "Qatlib.html"), root / "original-Qatlib.html")
            os.link(doc / "index.html", doc / "Qatlib.html")
            cache.publish("html")
            key = next(k for k in objects if k.endswith(".tar.gz"))
            first = objects[key]
            # Recreate identical files with a different order, modes, times and inodes.
            shutil.move(str(doc), root / "old-doc")
            for old in sorted((root / "old-doc").rglob("*"), reverse=True):
                target = doc / old.relative_to(root / "old-doc")
                if old.is_file():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(old.read_bytes())
                    target.chmod(0o600)
                    os.utime(target, (123456789, 123456789))
            cache.publish("html")
            self.assertEqual(first, objects[key])
            self.assertEqual(int.from_bytes(first[4:8], "little"), 0)
            self.assertFalse(first[3] & 8)  # No gzip filename header.
            with tarfile.open(fileobj=io.BytesIO(first), mode="r:gz") as tar:
                self.assertEqual(tar.getnames(), sorted(tar.getnames()))
                for member in tar.getmembers():
                    self.assertEqual((member.mtime, member.uid, member.gid, member.uname, member.gname),
                                     (0, 0, 0, "", ""))

    def test_legacy_analysis_restores_and_republishes_only_direct_archives(self):
        with fixture() as root, snapshot_store() as objects:
            analysis_files()
            cache.publish("analysis")
            prefix, _, compatible = cache.identity()
            base = f"{prefix}/analysis/{compatible}/latest"
            metadata = objects[f"{base}.json"]
            sha = json.loads(metadata)["sha256"]
            legacy = f"{prefix}/objects/{sha}.tar.gz"
            objects[legacy] = objects.pop(f"{base}.tar.gz")
            shutil.move(str(cache.BUILD), root / "original-build")
            # Matches the previous writer's format, compatibility key and pointer.
            self.assertTrue(cache.restore("analysis"))
            self.assertEqual((cache.BUILD / "doc-data/Qatlib.Example.doc").read_text(), "analysis marker")
            with cache.database(cache.BUILD / "api-docs.db") as connection:
                self.assertEqual(connection.execute("SELECT name FROM modules").fetchall(), [("Qatlib.Example",)])
            objects.clear()
            cache.publish("analysis")
            self.assertEqual(set(objects), {f"{base}.tar.gz", f"{base}.json"})
            shutil.move(str(cache.BUILD), root / "migrated-build")
            self.assertTrue(cache.restore("analysis"))

    def test_analysis_mismatch_preserves_local_pair_and_never_uses_legacy(self):
        with fixture(), snapshot_store() as objects:
            analysis_files()
            cache.publish("analysis")
            prefix, _, compatible = cache.identity()
            base = f"{prefix}/analysis/{compatible}/latest"
            sha = json.loads(objects[f"{base}.json"])["sha256"]
            objects[f"{prefix}/objects/{sha}.tar.gz"] = objects[f"{base}.tar.gz"]
            objects[f"{base}.tar.gz"] = b"corrupt"
            before = (cache.BUILD / "api-docs.db").read_bytes()
            with patch.object(cache, "trash") as retire:
                with self.assertRaisesRegex(RuntimeError, "checksum"):
                    cache.restore("analysis")
                retire.assert_not_called()
            self.assertEqual((cache.BUILD / "api-docs.db").read_bytes(), before)
            self.assertTrue((cache.BUILD / "doc-data/Qatlib.Example.doc").is_file())

    def test_upload_readback_failure_preserves_metadata_for_both_kinds(self):
        for kind in ("html", "analysis"):
            with self.subTest(kind=kind), fixture() as root, snapshot_store() as objects:
                api_files(root, cache.BUILD / "doc")
                if kind == "analysis":
                    # The HTML fixture has already created the build directory.
                    shutil.move(str(cache.BUILD), root / "html-build")
                    analysis_files()
                cache.publish(kind)
                metadata = {k: v for k, v in objects.items() if k.endswith(".json")}
                for invalid in (None, b"corrupt"):
                    def download(key, path):
                        if invalid is None:
                            return False
                        path.write_bytes(invalid)
                        return True

                    with patch.object(cache, "get", side_effect=download), patch.object(cache, "put") as upload:
                        with self.assertRaisesRegex(RuntimeError, "checksum verification"):
                            cache.publish(kind)
                        self.assertEqual(upload.call_count, 1)
                        self.assertTrue(upload.call_args.args[0].endswith(".tar.gz"))
                    self.assertEqual(metadata, {k: v for k, v in objects.items() if k.endswith(".json")})

    def test_schema_changes_fail_with_upgrade_instructions_before_mutation(self):
        schemas = ("name TEXT PRIMARY KEY", "name INTEGER PRIMARY KEY, source_url TEXT",
                   "name TEXT, source_url TEXT", "name TEXT PRIMARY KEY, source_url BLOB",
                   "name TEXT PRIMARY KEY, source_url TEXT NOT NULL",
                   "name TEXT PRIMARY KEY, source_url TEXT DEFAULT ''",
                   "name TEXT PRIMARY KEY, source_url TEXT, extra TEXT")
        for columns in schemas:
            with self.subTest(columns=columns), fixture():
                cache.BUILD.mkdir(parents=True)
                with cache.database(cache.BUILD / "api-docs.db") as connection:
                    connection.execute(f"CREATE TABLE modules({columns})")
                before = (cache.BUILD / "api-docs.db").read_bytes()
                with patch.object(cache, "put") as upload, patch.object(cache, "trash") as retire:
                    for operation in (cache.prune, lambda: cache.publish("analysis")):
                        with self.assertRaisesRegex(RuntimeError, "After a Lean/doc-gen4 upgrade"):
                            operation()
                    upload.assert_not_called()
                    retire.assert_not_called()
                self.assertEqual((cache.BUILD / "api-docs.db").read_bytes(), before)

    def test_schema_guard_requires_cascading_deletes(self):
        with cache.database(":memory:") as connection:
            connection.execute("CREATE TABLE modules(name TEXT PRIMARY KEY, source_url TEXT)")
            connection.execute("CREATE TABLE child(module TEXT REFERENCES modules(name))")
            with self.assertRaisesRegex(RuntimeError, "ON DELETE CASCADE"):
                cache.assert_analysis_schema(connection)

    def test_invalid_analysis_contents_leave_local_pair_untouched(self):
        for invalid in ("schema", "markers"):
            with self.subTest(invalid=invalid), fixture() as root, snapshot_store() as objects:
                analysis_files()
                cache.publish("analysis")
                key = next(k for k in objects if k.endswith(".tar.gz"))
                unpacked = root / "changed"
                with tarfile.open(fileobj=io.BytesIO(objects[key]), mode="r:gz") as tar:
                    tar.extractall(unpacked, filter="data")
                if invalid == "schema":
                    with cache.database(unpacked / "api-docs.db") as connection:
                        connection.execute("ALTER TABLE modules RENAME COLUMN source_url TO url")
                else:
                    shutil.move(str(unpacked / "doc-data"), root / "retired-markers")
                archive = root / "changed.tar.gz"
                with tarfile.open(archive, "w:gz") as tar:
                    for path in unpacked.iterdir():
                        tar.add(path, arcname=path.name)
                objects[key] = archive.read_bytes()
                meta_key = key.removesuffix(".tar.gz") + ".json"
                meta = json.loads(objects[meta_key])
                meta["sha256"] = cache.digest(archive)
                objects[meta_key] = json.dumps(meta).encode()
                before = (cache.BUILD / "api-docs.db").read_bytes()
                with patch.object(cache, "trash") as retire:
                    with self.assertRaisesRegex(RuntimeError, "schema|doc-data markers"):
                        cache.restore("analysis")
                    retire.assert_not_called()
                self.assertEqual((cache.BUILD / "api-docs.db").read_bytes(), before)
                self.assertTrue((cache.BUILD / "doc-data/Qatlib.Example.doc").is_file())

    def test_archive_rejects_traversal_and_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, kind in (("../escape", tarfile.REGTYPE), ("link", tarfile.SYMTYPE)):
                archive = root / "unsafe.tar.gz"
                with tarfile.open(archive, "w:gz") as tar:
                    member = tarfile.TarInfo(name)
                    member.type = kind
                    member.linkname = "outside"
                    tar.addfile(member)
                with self.assertRaisesRegex(RuntimeError, "Unsafe"):
                    cache.extract(archive, root / "out")

    def test_publication_rejects_private_urls_and_machine_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "example.html"
            for value in ("qatlib-" + "dev", "/" + "home" + "/someone/workspace"):
                path.write_text(value)
                with self.assertRaisesRegex(RuntimeError, "private URL or machine path"):
                    cache.verify_public([path])

    def test_incomplete_api_fails_and_nested_portal_links_are_checked(self):
        with fixture() as root:
            doc = root / "raw"
            api_files(root, doc)
            self.assertEqual(build_site.verify_docgen(root, doc), [])
            shutil.move(str(doc / "Qatlib/Example.html"), root / "retired.html")
            self.assertIn("Qatlib/Example.html", " ".join(build_site.verify_docgen(root, doc)))
            with self.assertRaisesRegex(RuntimeError, "Incomplete"):
                build_site.build_site(root, root / "out", doc, False, False, True)
            nested = root / "out/units"
            nested.mkdir(parents=True)
            (nested / "example.html").write_text('<a href="missing.html">broken</a>')
            self.assertEqual(len(build_site.verify_portal_links(root / "out")), 1)

    def test_checked_in_lock_matches_root_dependencies(self):
        root = json.loads((SOURCE / "lake-manifest.json").read_text())
        docs = json.loads((SOURCE / "docbuild/lake-manifest.json").read_text())
        locked = {p["name"]: p for p in docs["packages"]}
        for package in root["packages"]:
            self.assertEqual(locked[package["name"]]["rev"], package["rev"])

    def test_selector_covers_all_build_triggers(self):
        workflow = (SOURCE / ".github/workflows/docs.yml").read_text()
        selector = workflow.split("          patterns = ", 1)[1].split("          run = True", 1)[0]
        patterns = ast.literal_eval(selector.strip())
        build = (SOURCE / ".github/workflows/build.yml").read_text()
        paths = build.split("paths: &build-paths\n", 1)[1].split("  pull_request:", 1)[0]
        expected = [line.split("'", 2)[1] for line in paths.splitlines() if "- '" in line]
        self.assertEqual(set(patterns), set(expected))


if __name__ == "__main__":
    unittest.main()
