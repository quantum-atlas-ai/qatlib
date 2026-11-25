#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Pack public theorem dependencies from compiled Lean modules into a site asset."""

from __future__ import annotations

import argparse
from collections import defaultdict
from collections.abc import Iterable, Iterator
import gzip
import json
import logging
import os
from pathlib import Path
import subprocess

from build_site import DEPENDENCY_GRAPH_ASSET, PANEL_LAYERS, parse_references_bib, read_lean_toolchain
BATCH_SIZE = 128


def lean_env(repo_root: Path) -> dict[str, str]:
    """Bind Lean subprocesses to the target repository's toolchain."""
    return {**os.environ, "ELAN_TOOLCHAIN": read_lean_toolchain(repo_root)}


def extract(repo_root: Path, artifacts: Path, sources: list[Path]) -> Iterator[tuple[str, str, list[str]]]:
    exporter = Path(__file__).with_name("export_theorem_dependencies.lean")
    env = lean_env(repo_root)
    for offset in range(0, len(sources), BATCH_SIZE):
        batch = sources[offset:offset + BATCH_SIZE]
        rows = subprocess.check_output(
            ["lean", "--run", str(exporter), str(artifacts), *(p.as_posix() for p in batch)],
            text=True, env=env,
        )
        for row in rows.splitlines():
            yield tuple(json.loads(row))


def source_group(source: Path) -> tuple[int, str]:
    _, layer, group, *_ = source.with_suffix("").parts
    return PANEL_LAYERS.index(layer), group


def pack(records: Iterable[tuple[str, str, list[str]]], sources: Iterable[Path],
         titles: dict[str, str]) -> dict:
    """Assign deterministic IDs and retain only edges between displayed theorems."""
    records = sorted(records, key=lambda record: (record[0], record[1]))
    origins: dict[str, list[str]] = defaultdict(list)
    for source, name, _ in records:
        origins[name].append(source)
    # Proof references identify constants by name. Parallel modules can use the
    # same name locally, so neither the node nor an edge to it has a unique target.
    ambiguous = {name for name, sources in origins.items() if len(sources) > 1}
    for name in sorted(ambiguous):
        logging.warning("Omitting ambiguous theorem %s (%s)", name, ", ".join(origins[name]))
    records = [record for record in records if record[1] not in ambiguous]
    ids = {name: i for i, (_, name, _) in enumerate(records)}

    group_keys = sorted({source_group(source) for source in sources})
    group_ids = {key: i for i, key in enumerate(group_keys)}
    groups = [
        [layer, group, titles.get(group, "") if PANEL_LAYERS[layer] == "Papers" else ""]
        for layer, group in group_keys
    ]
    modules, nodes = [], []
    module_ids: dict[str, int] = {}
    for i, (source, name, references) in enumerate(records):
        if source not in module_ids:
            path = Path(source)
            module_ids[source] = len(modules)
            modules.append([path.with_suffix("").as_posix(), group_ids[source_group(path)]])
        dependencies = sorted({ids[ref] for ref in references if ref in ids and ids[ref] != i})
        nodes.append([name, module_ids[source], dependencies])
    return {"version": 1, "groups": groups, "modules": modules, "nodes": nodes,
            "ambiguousNames": sorted(ambiguous)}


def write_asset(path: Path, graph: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(graph, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    with path.open("wb") as stream, gzip.GzipFile(filename="", mode="wb", fileobj=stream, mtime=0) as archive:
        archive.write(payload)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--olean-dir", type=Path, help="Compiled modules (default: .lake/build/lib/lean under --repo-root)")
    output = parser.add_mutually_exclusive_group(required=True)
    output.add_argument("--output", type=Path, help="Write the asset to this path")
    output.add_argument("--output-dir", type=Path, help=f"Write {DEPENDENCY_GRAPH_ASSET} in this directory")
    args = parser.parse_args()
    sources = sorted(path.relative_to(args.repo_root) for layer in PANEL_LAYERS
                     for path in (args.repo_root / "Qatlib" / layer).rglob("*.lean"))
    _, bibliography = parse_references_bib(args.repo_root / "docs/references.bib")
    titles = {entry["key"]: entry["title"] for entry in bibliography}
    artifacts = args.olean_dir if args.olean_dir is not None else args.repo_root / ".lake/build/lib/lean"
    graph = pack(extract(args.repo_root, artifacts, sources), sources, titles)
    if not graph["nodes"]:
        raise SystemExit("No public theorems were found in the compiled Qatlib modules")
    asset = args.output if args.output is not None else args.output_dir / DEPENDENCY_GRAPH_ASSET
    write_asset(asset, graph)
    size = asset.stat().st_size
    edges = sum(len(dependencies) for _, _, dependencies in graph["nodes"])
    print(f"Packed {len(graph['nodes']):,} theorems and {edges:,} edges in {size:,} bytes")


if __name__ == "__main__":
    main()
