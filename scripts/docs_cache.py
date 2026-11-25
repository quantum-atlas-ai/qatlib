#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Self-maintained doc-gen4 snapshots, scoped by toolchain under docs/<repo>/tc/<tc>.

html/<fingerprint>.{tar.gz,json} stores exact raw HTML; analysis/<compatible>/
latest.{tar.gz,json} stores a SQLite backup and its analysis markers together.
Analysis .trace JSON keeps only schemaVersion/depHash: Lake v4.35 marker checks
need the hash and marker existence; input captions and replay logs may hold paths.
Archives have sorted entries, normalized ownership/modes and zero tar/gzip times.
Upload and read back the archive before publishing SHA-256 metadata. Readers
reject mismatched pairs before replacing local output; writers must be serialized.
Only analysis has a read-only fallback to the previous metadata/object layout.
Keep FORMAT stable for that migration. On Lean/doc-gen4 upgrades, review srcUri
generation, DB/Schema.lean, Lake/Build/Common.lean trace parsing, marker selection
and assert_analysis_schema, then
recheck cold/warm builds and source links; bump FORMAT for incompatible semantics.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import tarfile
import tempfile
import tomllib

from build_site import DEPENDENCY_GRAPH_ASSET, PANEL_LAYERS, read_lean_toolchain

REPO = "quantum-atlas-ai/qatlib"
CDN = "https://lake-cache.quantum-atlas.ai"
FORMAT = "docs-v1-disable-equations"
INPUTS = ("Qatlib", "Qatlib.lean", "lakefile.toml", "lake-manifest.json",
          "lean-toolchain", "docbuild/lakefile.toml", "docbuild/lake-manifest.json",
          "docs/references.bib", "scripts/docs_cache.py", "scripts/build_docs.sh",
          "scripts/build_dependency_graph.py", "scripts/export_theorem_dependencies.lean")
BUILD = Path("docbuild/.lake/build")
TRASH_BATCH_SIZE = 128


@contextmanager
def database(path: Path):
    connection = sqlite3.connect(path)
    try:
        with connection:
            yield connection
    finally:
        connection.close()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def identity() -> tuple[str, str, str]:
    tree = subprocess.check_output(["git", "ls-files", "-s", "--", *INPUTS])
    graph_settings = json.dumps([DEPENDENCY_GRAPH_ASSET, PANEL_LAYERS]).encode()
    fingerprint = hashlib.sha256(FORMAT.encode() + graph_settings + tree).hexdigest()
    lock = hashlib.sha256(FORMAT.encode())
    for name in ("lean-toolchain", "lake-manifest.json", "docbuild/lakefile.toml",
                 "docbuild/lake-manifest.json"):
        lock.update(Path(name).read_bytes())
    tc = read_lean_toolchain(Path(".")).replace("/", "--").replace(":", "---")
    return f"docs/{REPO}/tc/{tc}", fingerprint, lock.hexdigest()


def verify_public(paths: list[Path]) -> None:
    """Reject private source URLs or machine paths before publishing snapshots."""
    forbidden = re.compile(rb"qatlib-(?:dev|staging)|/(?:home|mnt|Users|var/lib)/", re.IGNORECASE)
    for root in paths:
        for path in ([root] if root.is_file() else root.rglob("*")):
            if path.is_symlink():
                raise RuntimeError(f"Snapshot contains a symlink: {path.name}")
            if not path.is_file():
                continue
            # Streaming keeps checks bounded even for large SQLite databases.
            with path.open("rb") as stream:
                tail = b""
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    if forbidden.search(tail + chunk):
                        raise RuntimeError(f"Snapshot contains a private URL or machine path: {path.name}")
                    tail = chunk[-128:]


def trash(path: Path) -> None:
    trash_many([path])


def trash_many(paths: list[Path]) -> None:
    targets = [str(path) for path in dict.fromkeys(paths)
               if path.exists() or path.is_symlink()]
    for offset in range(0, len(targets), TRASH_BATCH_SIZE):
        subprocess.run(["trash-put", "--", *targets[offset:offset + TRASH_BATCH_SIZE]], check=True)


def get(key: str, out: Path) -> bool:
    result = subprocess.run([
        "curl", "--silent", "--show-error", "--location", "--retry", "3",
        "--connect-timeout", "10", "--max-time", "1800", "--output", str(out),
        "--write-out", "%{http_code}", f"{CDN}/{key}",
    ], capture_output=True, text=True, check=True)
    if result.stdout == "404":
        return False
    if result.stdout != "200":
        raise RuntimeError(f"CDN returned HTTP {result.stdout} for {key}: {result.stderr}")
    return True


def put(key: str, path: Path) -> None:
    credential = os.environ.get("LAKE_CACHE_KEY", "").strip()
    if not credential or ":" not in credential or any(c in credential for c in '\r\n"\\'):
        raise RuntimeError("LAKE_CACHE_KEY must contain the S3 access key and secret separated by ':'")
    config = tomllib.loads(Path("lake-cache.toml").read_text())
    service = next(s for s in config["cache"]["service"] if s["name"] == "qatlib-r2-upload")
    bucket = service["revisionEndpoint"].removesuffix("/revisions")
    # Credentials go through stdin, never the process argument list or logs.
    subprocess.run([
        "curl", "--fail", "--silent", "--show-error", "--retry", "3",
        "--connect-timeout", "15", "--max-time", "1800", "--aws-sigv4", "aws:amz:auto:s3",
        "--config", "-", "--upload-file", str(path), f"{bucket}/{key}",
    ], input=f'user = "{credential}"\n', text=True, check=True)


def extract(archive: Path, destination: Path) -> None:
    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        for member in members:
            name = Path(member.name)
            if name.is_absolute() or ".." in name.parts or not (member.isfile() or member.isdir()):
                raise RuntimeError(f"Unsafe snapshot member: {member.name}")
        tar.extractall(destination, members=members, filter="data")


def assert_analysis_schema(connection: sqlite3.Connection) -> None:
    """Guard the doc-gen4 v4.35 SQL boundary before reading or mutating modules."""
    def changed(detail: str) -> None:
        raise RuntimeError(
            "Unsupported doc-gen4 analysis schema: " + detail + ". "
            "After a Lean/doc-gen4 upgrade, review DocGen4/DB/Schema.lean and "
            "source URL/marker handling in scripts/docs_cache.py; update this guard "
            "and FORMAT if needed before rebuilding analysis with docs_cache.py reset.")

    columns = [(row[1], row[2].upper(), row[3], row[4], row[5])
               for row in connection.execute("PRAGMA table_info(modules)")]
    if columns != [("name", "TEXT", 0, None, 1), ("source_url", "TEXT", 0, None, 0)]:
        changed(f"expected modules(name TEXT PRIMARY KEY, source_url TEXT), got {columns!r}")
    # Pruning relies on dependent rows cascading when a module is deleted.
    for name, in connection.execute("SELECT name FROM sqlite_master WHERE type = 'table'"):
        quoted = '"' + name.replace('"', '""') + '"'
        for foreign in connection.execute(f"PRAGMA foreign_key_list({quoted})"):
            if foreign[6].upper() != "CASCADE":
                changed(f"{name} must use ON DELETE CASCADE for dependent rows")


def restore(kind: str) -> bool:
    prefix, fingerprint, compatible = identity()
    key = (f"{prefix}/html/{fingerprint}.json" if kind == "html"
           else f"{prefix}/analysis/{compatible}/latest.json")
    with tempfile.TemporaryDirectory(dir=os.environ.get("RUNNER_TEMP")) as directory:
        tmp = Path(directory)
        if not get(key, tmp / "manifest.json"):
            return False
        meta = json.loads((tmp / "manifest.json").read_text())
        if (meta["format"] != FORMAT or meta["compatible"] != compatible or
                (kind == "html" and meta["fingerprint"] != fingerprint)):
            raise RuntimeError("Incompatible documentation snapshot")
        sha = meta["sha256"]
        if not re.fullmatch(r"[0-9a-f]{64}", sha):
            raise RuntimeError("Invalid snapshot digest")
        archive_key = (f"{prefix}/html/{fingerprint}.tar.gz" if kind == "html"
                       else f"{prefix}/analysis/{compatible}/latest.tar.gz")
        if not get(f"{archive_key}?sha256={sha}", tmp / "snapshot.tar.gz"):
            # Read the previous analysis layout once; the next publish migrates it.
            if kind != "analysis" or not get(f"{prefix}/objects/{sha}.tar.gz", tmp / "snapshot.tar.gz"):
                raise RuntimeError("Snapshot metadata points at a missing archive")
        if digest(tmp / "snapshot.tar.gz") != sha:
            raise RuntimeError("Snapshot checksum mismatch")
        extract(tmp / "snapshot.tar.gz", tmp / "unpacked")
        unpacked = tmp / "unpacked"
        if kind == "html":
            errors = verify_html_files(unpacked / "doc")
            if errors:
                raise RuntimeError("Incomplete HTML snapshot: " + "; ".join(errors[:5]))
            trash(BUILD / "doc")
            BUILD.mkdir(parents=True, exist_ok=True)
            shutil.move(str(unpacked / "doc"), BUILD / "doc")
        else:
            db = unpacked / "api-docs.db"
            with database(db) as connection:
                if connection.execute("PRAGMA quick_check").fetchone() != ("ok",):
                    raise RuntimeError("Invalid analysis database")
                assert_analysis_schema(connection)
            if not (unpacked / "doc-data").is_dir():
                raise RuntimeError("Analysis snapshot is missing its doc-data markers")
            # DB and markers are one unit. Never combine a new DB with old markers.
            reset_analysis()
            BUILD.mkdir(parents=True, exist_ok=True)
            shutil.move(str(db), BUILD / "api-docs.db")
            shutil.move(str(unpacked / "doc-data"), BUILD / "doc-data")
        print(f"Restored {kind} snapshot")
        return True


def checkpoint(connection: sqlite3.Connection) -> None:
    connection.commit()
    busy, log, done = connection.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchone()
    if busy or (log >= 0 and log != done):
        raise RuntimeError(f"SQLite checkpoint is busy or incomplete: {(busy, log, done)}")


def reset_analysis() -> None:
    for path in BUILD.glob("api-docs.db*"):
        trash(path)
    trash(BUILD / "doc-data")


def copy_analysis_trace(source: Path, destination: Path) -> None:
    """Keep only Lake v4.35's path-free marker validation data in the snapshot."""
    try:
        meta = json.loads(source.read_text())
    except json.JSONDecodeError as error:
        raise RuntimeError(f"Invalid Lake analysis trace JSON: {source.name}") from error
    if (not isinstance(meta, dict) or meta.get("schemaVersion") != "2025-09-10" or
            not isinstance(meta.get("depHash"), str) or
            not re.fullmatch(r"[0-9a-fA-F]{16}", meta["depHash"])):
        raise RuntimeError(
            f"Unsupported Lake analysis trace schema: {source.name}. "
            "After a Lean upgrade, review BuildMetadata and marker up-to-date checks "
            "in Lake/Build/Common.lean before updating copy_analysis_trace.")
    # buildFileUnlessUpToDate' uses depHash + marker existence. BuildMetadata
    # defaults inputs/log to empty and outputs to none; no timestamps are parsed.
    destination.write_text(json.dumps({key: meta[key] for key in ("schemaVersion", "depHash")},
                                     sort_keys=True) + "\n")


def prune() -> None:
    live = {"Qatlib", *(".".join(p.with_suffix("").parts) for p in Path("Qatlib").rglob("*.lean"))}
    for root in Path(".lake/packages").glob("*/.lake/build/lib/lean"):
        live.update(".".join(p.relative_to(root).with_suffix("").parts) for p in root.rglob("*.olean"))

    def valid(module: str) -> bool:
        return module.split(".", 1)[0] in {"Init", "Std", "Lake", "Lean"} or module in live

    db = BUILD / "api-docs.db"
    if not db.is_file():
        trash(BUILD / "doc-data")
        return
    with database(db) as connection:
        assert_analysis_schema(connection)
        connection.execute("PRAGMA foreign_keys = ON")
        stale = [name for name, in connection.execute("SELECT name FROM modules") if not valid(name)]
        connection.executemany("DELETE FROM modules WHERE name = ?", [(name,) for name in stale])
        checkpoint(connection)  # commit before checkpoint, including the cascade deletes
    for marker in (BUILD / "doc-data").glob("*.doc"):
        if not marker.stem.startswith("core-") and not valid(marker.stem):
            for path in marker.parent.glob(f"{marker.name}*"):
                trash(path)
    print(f"Pruned {len(stale)} stale database modules")


def normalize_analysis(connection: sqlite3.Connection) -> None:
    """Use canonical public source links for both read-only and publishing builds."""
    assert_analysis_schema(connection)
    # DOCGEN_SRC=github and origin set the repo, but srcUri.github always uses
    # getProjectCommit; doc-gen4 v4.35 has no revision override.
    connection.execute(
        "UPDATE modules SET source_url = ? || replace(name, '.', '/') || '.lean' "
        "WHERE name = 'Qatlib' OR name LIKE 'Qatlib.%'",
        (f"https://github.com/{REPO}/blob/main/",))
    checkpoint(connection)


def verify_html_files(doc: Path) -> list[str]:
    from build_site import verify_docgen
    errors = verify_docgen(Path.cwd(), doc)
    graph = doc / DEPENDENCY_GRAPH_ASSET
    if not graph.is_file() or graph.stat().st_size == 0:
        errors.append(f"missing or empty API output: {DEPENDENCY_GRAPH_ASSET}")
    return errors


def verify_html() -> None:
    """Validate complete, public HTML even when no R2 publication is requested."""
    errors = verify_html_files(BUILD / "doc")
    if errors:
        raise RuntimeError("Incomplete doc-gen4 output: " + "; ".join(errors[:5]))
    verify_public([BUILD / "doc"])


def publish(kind: str) -> None:
    prefix, fingerprint, compatible = identity()
    with tempfile.TemporaryDirectory(dir=os.environ.get("RUNNER_TEMP")) as directory:
        tmp = Path(directory)
        if kind == "analysis":
            with database(BUILD / "api-docs.db") as connection:
                normalize_analysis(connection)
                with database(tmp / "api-docs.db") as backup:
                    connection.backup(backup)
                    if backup.execute("PRAGMA quick_check").fetchone() != ("ok",):
                        raise RuntimeError("Analysis backup failed integrity check")
            data = tmp / "doc-data"
            data.mkdir()
            for path in (BUILD / "doc-data").iterdir():
                if path.is_file() and ((".doc" in path.name and ".docs" not in path.name) or
                                       path.name.startswith("references.json")):
                    if path.suffix == ".trace":
                        copy_analysis_trace(path, data / path.name)
                    else:
                        shutil.copy2(path, data / path.name)
            paths = [tmp / "api-docs.db", data]
            base = f"{prefix}/analysis/{compatible}/latest"
        else:
            verify_html()
            paths = [BUILD / "doc"]
            base = f"{prefix}/html/{fingerprint}"
        verify_public(paths)
        archive = tmp / "snapshot.tar.gz"
        with archive.open("wb") as stream, gzip.GzipFile(
                filename="", mode="wb", fileobj=stream, compresslevel=1, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", dereference=True) as tar:
                for root in sorted(paths):
                    for path in sorted([root, *root.rglob("*")], key=lambda p: p.as_posix()):
                        entry = tar.gettarinfo(path, arcname=str(path.relative_to(root.parent)))
                        entry.mtime = entry.uid = entry.gid = 0
                        entry.uname = entry.gname = ""
                        entry.mode = 0o755 if entry.isdir() else 0o644
                        entry.pax_headers = {}
                        if entry.isfile():
                            with path.open("rb") as content:
                                tar.addfile(entry, content)
                        else:
                            tar.addfile(entry)
        sha = digest(archive)
        put(f"{base}.tar.gz", archive)
        # The digest query avoids serving a previous cached latest.tar.gz.
        uploaded = tmp / "uploaded.tar.gz"
        if not get(f"{base}.tar.gz?sha256={sha}", uploaded) or digest(uploaded) != sha:
            raise RuntimeError("Uploaded snapshot checksum verification failed")
        metadata = tmp / "manifest.json"
        metadata.write_text(json.dumps(dict(format=FORMAT, fingerprint=fingerprint,
                                            compatible=compatible, sha256=sha)) + "\n")
        # A partial publication fails closed at restore, preserving local output.
        put(f"{base}.json", metadata)
        print(f"Published {kind} snapshot ({archive.stat().st_size // 1048576} MiB)")


def clean_html() -> None:
    paths = [BUILD / "doc"]
    for pattern in ("*.docs_built*", "*docsHeader_built*", "declaration-data-*.bmp*", "backrefs-*.json*"):
        paths.extend((BUILD / "doc-data").glob(pattern))
    trash_many(paths)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("probe", "restore-analysis", "publish-analysis",
                                           "publish-html", "normalize-analysis", "verify-html",
                                           "prune", "reset", "clean-html", "identity"))
    args = parser.parse_args()
    if args.action == "probe":
        hit = restore("html")
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            output.write(f"hit={str(hit).lower()}\n")
    elif args.action == "restore-analysis":
        if not restore("analysis"):
            reset_analysis()
            print("No compatible analysis snapshot; starting clean")
    elif args.action == "normalize-analysis":
        with database(BUILD / "api-docs.db") as connection:
            normalize_analysis(connection)
    elif args.action == "verify-html":
        verify_html()
    elif args.action.startswith("publish-"):
        publish(args.action.removeprefix("publish-"))
    elif args.action == "prune":
        prune()
    elif args.action == "reset":
        reset_analysis()
    elif args.action == "clean-html":
        clean_html()
    else:
        print(*identity(), sep="\n")


if __name__ == "__main__":
    main()
