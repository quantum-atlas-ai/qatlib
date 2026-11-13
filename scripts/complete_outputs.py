#!/usr/bin/env python3
"""Repair Lake 4.35.0's platform-independent ``-o`` manifest."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def rows(path: Path) -> tuple[str, list[list[object]]]:
    if not path.is_file():
        return "", []
    lines = [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not lines:
        return "", []
    result: list[list[object]] = []
    for line in lines[1:]:
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(row, list) and len(row) >= 2 and isinstance(row[0], str) and row[0]:
            result.append(row)
    return lines[0], result


def ltar(value: object) -> str | None:
    if isinstance(value, dict):
        value = value.get("ltar")
    if isinstance(value, str) and value.endswith(".ltar") and Path(value).name == value:
        return value
    return None


def mapping(path: Path | None) -> dict[str, str]:
    if path is None:
        return {}
    _header, result = rows(path)
    out: dict[str, str] = {}
    for row in result:
        descr = ltar(row[1])
        if descr:
            out[str(row[0])] = descr
    return out


def local_mapping(cache: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    for path in (cache / "outputs").rglob("*.json"):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(payload, dict):
            descr = ltar(payload.get("data"))
            if descr:
                out[path.stem] = descr
    return out


def traces(project: Path) -> list[tuple[Path, Path, str]]:
    root = project / ".lake/build/lib/lean"
    if not root.is_dir():
        return []
    out = []
    for trace in sorted(root.rglob("*.trace")):
        rel = trace.relative_to(root)
        source = project / rel.with_suffix(".lean")
        if not source.is_file() or ".lake/packages" in trace.parts:
            continue
        if not (root / rel.with_suffix(".olean")).is_file() \
                and not (project / ".lake/build/ir" / rel.with_suffix(".c")).is_file() \
                and not (project / ".lake/build/ir" / rel.with_suffix(".ltar")).is_file():
            continue
        try:
            payload = json.loads(trace.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        dep_hash = payload.get("depHash")
        if isinstance(dep_hash, str) and dep_hash:
            out.append((trace, source, dep_hash))
    return out


def archive_hash(path: Path, project: Path) -> str | None:
    sidecar = Path(str(path) + ".hash")
    if sidecar.is_file():
        value = sidecar.read_text(encoding="utf-8").strip()
        if len(value) == 16 and all(char in "0123456789abcdefABCDEF" for char in value):
            return value.lower() + ".ltar"
    with tempfile.TemporaryDirectory(prefix="qatlib-lake-hash-") as directory:
        helper = Path(directory) / "hash.lean"
        helper.write_text(
            "import Lake\nopen Lake System\n"
            "def main : IO Unit := do\n"
            "  let file? ← IO.getEnv \"HASH_FILE\"\n"
            "  match file? with\n"
            "  | some file => let h ← computeBinFileHash (FilePath.mk file); IO.println h.hex\n"
            "  | none => pure ()\n",
            encoding="utf-8",
        )
        try:
            value = subprocess.check_output(
                ["lake", "env", "lean", "--run", str(helper)], cwd=project,
                env={**os.environ, "HASH_FILE": str(path)}, text=True,
            ).strip()
        except (OSError, subprocess.CalledProcessError):
            return None
    return value.lower() + ".ltar" if len(value) == 16 else None


def ensure_archive(project: Path, cache: Path, trace: Path, source: Path, descr: str) -> None:
    artifact = cache / "artifacts" / descr
    if artifact.is_file():
        return
    build = project / ".lake/build"
    archive = build / "ir" / trace.relative_to(build / "lib/lean").with_suffix(".ltar")
    if not archive.is_file():
        env = {**os.environ, "LAKE_ARTIFACT_CACHE": "true"}
        subprocess.run(["lake", "--no-cache", "build", source.relative_to(project).as_posix() + ":ltar"],
                       cwd=project, env=env, check=False)
        if not archive.is_file():
            module_name = ".".join(source.relative_to(project).with_suffix("").parts)
            subprocess.run(["lake", "--no-cache", "build", "+" + module_name + ":ltar"],
                           cwd=project, env=env, check=False)
    if not archive.is_file():
        pack_ltar_direct(project, trace)
    if not archive.is_file():
        raise SystemExit(f"missing .ltar for root module {source}: {descr}")
    artifact.parent.mkdir(parents=True, exist_ok=True)
    try:
        os.link(archive, artifact)
    except FileExistsError:
        pass
    except OSError:
        shutil.copy2(archive, artifact)


def pack_ltar_direct(project: Path, trace: Path) -> None:
    build = project / ".lake/build"
    lean = build / "lib/lean"
    ir = build / "ir"
    relative = trace.relative_to(lean)
    archive = ir / relative.with_suffix(".ltar")
    required = [lean / relative.with_suffix(ext) for ext in (".olean", ".ilean")]
    required.append(ir / relative.with_suffix(".c"))
    if not all(path.is_file() for path in required):
        return
    archive.parent.mkdir(parents=True, exist_ok=True)
    args = ["lake", "env", "leantar", "-s", "-C", str(lean), "-C", str(ir), str(archive),
            str(relative.with_suffix(".trace"))]
    for ext in (".olean", ".olean.server", ".olean.private", ".ilean", ".ir.sig", ".ir"):
        if (lean / relative.with_suffix(ext)).is_file():
            args += ["-i", "0", str(relative.with_suffix(ext))]
    for ext in (".c", ".bc"):
        if (ir / relative.with_suffix(ext)).is_file():
            args += ["-i", "1", str(relative.with_suffix(ext))]
    subprocess.run(args, cwd=project, check=False)


def repair(project: Path, output: Path, cache: Path, candidate: Path | None) -> int:
    header, current = rows(output)
    manifest = {str(row[0]): descr for row in current if (descr := ltar(row[1]))}
    if not header:
        header = "2026-03-17"
    root_traces = traces(project)
    if not root_traces:
        return len(manifest)
    candidates = mapping(candidate)
    cached = local_mapping(cache)
    for trace, source, dep_hash in root_traces:
        descr = manifest.get(dep_hash) or candidates.get(dep_hash) or cached.get(dep_hash)
        archive = project / ".lake/build/ir" / trace.relative_to(project / ".lake/build/lib/lean").with_suffix(".ltar")
        if not descr and not archive.is_file():
            env = {**os.environ, "LAKE_ARTIFACT_CACHE": "true"}
            subprocess.run(["lake", "--no-cache", "build", source.relative_to(project).as_posix() + ":ltar"],
                           cwd=project, env=env, check=False)
            if not archive.is_file():
                module_name = ".".join(source.relative_to(project).with_suffix("").parts)
                subprocess.run(["lake", "--no-cache", "build", "+" + module_name + ":ltar"],
                               cwd=project, env=env, check=False)
            if not archive.is_file():
                pack_ltar_direct(project, trace)
            if archive.is_file():
                descr = archive_hash(archive, project)
        if not descr and archive.is_file():
            descr = archive_hash(archive, project)
        if not descr:
            raise SystemExit(f"no .ltar descriptor for root module {source} ({dep_hash})")
        manifest[dep_hash] = descr
        ensure_archive(project, cache, trace, source, descr)
    if len(manifest) < len(root_traces) or any(dep not in manifest for _trace, _source, dep in root_traces):
        raise SystemExit("incomplete root-package output manifest")
    output.write_text(
        header + "\n" + "\n".join(json.dumps([dep, manifest[dep]], separators=(",", ":"))
        for dep in sorted(manifest)) + "\n", encoding="utf-8"
    )
    return len(manifest)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("project", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("cache", type=Path)
    parser.add_argument("candidate", type=Path, nargs="?", default=None)
    args = parser.parse_args()
    count = repair(args.project.resolve(), args.output.resolve(), args.cache.resolve(),
                   args.candidate.resolve() if args.candidate else None)
    if traces(args.project.resolve()) and count == 0:
        raise SystemExit("root package has built modules but output manifest is empty")
    print(f"Repaired root-package output mappings: {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
