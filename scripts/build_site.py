#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Build the unified Qatlib GitHub Pages portal and integrate doc-gen4 API docs.

Single source of truth:
  - English & Chinese guides are rendered directly from README{.en,}.md,
    docs/getting-started{.en,}.md, docs/architecture{.en,}.md,
    CONTRIBUTING{.en,}.md, scripts/README.md, CITATION.cff, and lean-toolchain.
  - Module statistics, topic/paper directory explorers, docstring summaries,
    and bibliography cross-references are extracted dynamically from Qatlib/
    and docs/references.bib at build time.
  - doc-gen4 static output (if present) is mounted under _site/docs/ with an
    upgraded API landing page (_site/docs/index.html), a return-to-portal link
    in _site/docs/navbar.html, and directory index pages under _site/docs/Qatlib/.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
from functools import cache
import gzip
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
from posixpath import relpath
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from typing import Any
from urllib.parse import quote, unquote, urlsplit

from site_docgen import adapt_docgen

GITHUB_REPO_URL = "https://github.com/quantum-atlas-ai/qatlib"
CACHE_CDN_URL = "https://lake-cache.quantum-atlas.ai"

DECLARATION_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "opaque",
    "instance",
    "axiom",
)
LEAN_NAME_PART = r"(?:[^\W\d][\w'!?]*|«[^»]+»)"
LEAN_NAME = rf"{LEAN_NAME_PART}(?:\.{LEAN_NAME_PART})*"
NAME_PART_RE = re.compile(LEAN_NAME_PART)
DECLARATION_RE = re.compile(
    r"[ \t]*(?:(?:@\[[^\]]*\]|(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local|public|meta))\s+)*"
    rf"(?P<kind>{'|'.join(DECLARATION_KINDS)})(?=\s|[:(\[{{]|$)"
    rf"(?:\s+(?P<name>{LEAN_NAME}))?"
)
HEADER_DIRECTIVE_RE = re.compile(
    rf"\s*(?:module\b|prelude\b|(?:public\s+)?(?:meta\s+)?import\s+"
    rf"(?:all\s+)?(?P<imported>{LEAN_NAME}))"
)
SCOPE_RE = re.compile(
    r"^\s*(?:(?:@\[[^\]]*\]|public|noncomputable|meta)\s+)*"
    rf"(?P<kind>namespace|section|end)\b(?:\s+(?P<name>{LEAN_NAME}))?\s*$"
)
SCOPE_NAME_RE = re.compile(rf"\s+({LEAN_NAME})\s*$")
RAW_STRING_RE = re.compile(r'r(#*)"')
INTERPOLATED_STRING_START = r'(?<![\w\'!?])(?:[sfm]!|(?:e?print(?:ln)?!)|dbg_trace)\s*"'
TRIVIA_START = rf'/[-]|--|«|(?<![\w\'!?])r#*"|{INTERPOLATED_STRING_START}|"|(?<![\w\'!?])\''
SOURCE_TRIVIA_RE = re.compile(TRIVIA_START)
INTERPOLATION_RE = re.compile(rf"{TRIVIA_START}|[{{}}]")
BLOCK_DELIMITER_RE = re.compile(r"/-|-/")
CHAR_LITERAL_RE = re.compile(r"'(?:[^'\\\n]|\\(?:x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|[^\n]))'")
SOURCE_HIGHLIGHT_RE = re.compile(
    r"\b(counterexample|refutation|refuted|erratum|errata|corrected|correction|invalid|false|caveat)\b",
    re.IGNORECASE,
)
PANEL_LAYERS = ("Foundations", "Concepts", "Papers")
DEPENDENCY_GRAPH_PAGE = "dependencies.html"
DEPENDENCY_GRAPH_ASSET = "theorem-dependencies.json.gz"
DEPENDENCY_GRAPH_SCRIPT = "dependency-graph.js"
DEPENDENCY_GRAPH_STYLES = "dependency-graph.css"
DEPENDENCY_GRAPH_API = "dependency-graph-api.js"
DEPENDENCY_GRAPH_PORTAL_ASSETS = (
    DEPENDENCY_GRAPH_STYLES, DEPENDENCY_GRAPH_SCRIPT, "dependency-nebula.js", "dependency-layers.js",
)
SITE_ASSETS = Path(__file__).with_name("site")
DEFAULT_SITE_URL = "https://quantum-atlas-ai.github.io/qatlib/"
DEFAULT_LOCALE = "zh"
LOCALES = {
    "zh": {"tag": "zh-Hans", "name": "中文", "og": "zh_CN", "md_suffix": "", "prefix": ""},
    "en": {"tag": "en", "name": "English", "og": "en_US", "md_suffix": ".en", "prefix": "en/"},
}
SOCIAL_IMAGE = "qatlib-social-preview.png"
BRAND_ASSETS = Path(".github/assets")
FAVICON_ASSETS = Path(__file__).resolve().parents[1] / BRAND_ASSETS / "favicon"
ADAPTIVE_FAVICON = "favicon-adaptive.svg"
NAV_PAGES = {
    "index.html": "nav_overview",
    "getting-started.html": "nav_getting_started",
    "architecture.html": "nav_architecture",
    "modules.html": "nav_modules",
    "papers.html": "nav_papers",
    DEPENDENCY_GRAPH_PAGE: "nav_graph",
    "contributing.html": "nav_contributing",
    "changelog.html": "nav_changelog",
}
GUIDE_PAGES = {
    "README": "index.html",
    "docs/getting-started": "getting-started.html",
    "docs/architecture": "architecture.html",
    "CONTRIBUTING": "contributing.html",
    "scripts/README": "architecture.html#tooling",
}


@cache
def strings_for(locale: str) -> dict[str, Any]:
    path = SITE_ASSETS / "locales" / f"{LOCALES[locale]['tag']}.json"
    return json.loads(path.read_text(encoding="utf-8"))


def url_for(locale: str, page: str = "index.html") -> str:
    """Return the locale route relative to the site root, using directory URLs for homes."""
    path, sep, anchor = page.partition("#")
    return f"{LOCALES[locale]['prefix']}{'' if path == 'index.html' else quote(path)}{sep}{anchor}"


def root_relative(page: str) -> str:
    return "../" * page.count("/") or "./"


def relative_url(from_page: str, target: str) -> str:
    path = relpath(target or ".", start=from_page.rpartition("/")[0] or ".")
    if path == ".":
        return "./"
    prefix = "" if path == ".." or path.startswith("../") else "./"
    return f"{prefix}{path}{'/' if not target or target.endswith('/') else ''}"

def render_wordmark(root_prefix: str, css_class: str) -> str:
    """Render the full wordmark in the colors for the active portal theme."""
    assets = f"{root_prefix}assets"
    return (
        f'<span class="brand-wordmark {css_class}">'
        f'<img class="wordmark-light" src="{assets}/qatlib-wordmark.svg" alt="Qatlib" width="480" height="115">'
        f'<img class="wordmark-dark" src="{assets}/qatlib-wordmark-dark.svg" alt="Qatlib" width="480" height="115">'
        '</span>'
    )


def render_favicon_links(root_prefix: str) -> str:
    """Render the icons with paths relative to the portal root."""
    links = [f'<link rel="icon" href="{root_prefix}favicon.ico" sizes="any">']
    links.extend(
        f'<link rel="icon" type="image/png" sizes="{size}" '
        f'href="{root_prefix}favicon-{theme}-{size}.png" '
        f'media="(prefers-color-scheme: {theme})">'
        for theme in ("light", "dark")
        for size in ("32x32", "16x16")
    )
    links.extend((
        f'<link rel="icon" type="image/svg+xml" href="{root_prefix}{ADAPTIVE_FAVICON}" sizes="any">',
        f'<link rel="apple-touch-icon" sizes="180x180" href="{root_prefix}apple-touch-icon.png">',
    ))
    return "\n".join(f"  {link}" for link in links)


# ---------------------------------------------------------------------------
# TeX / BibTeX cleaning & parsing
# ---------------------------------------------------------------------------

LATEX_ACCENTS = {
    r"\'a": "á", r"\'e": "é", r"\'i": "í", r"\'\i": "í", r"\'o": "ó", r"\'u": "ú",
    r"\'y": "ý", r"\'c": "ć", r"\'n": "ń", r"\'s": "ś", r"\'z": "ź",
    r"\'A": "Á", r"\'E": "É", r"\'I": "Í", r"\'O": "Ó", r"\'U": "Ú", r"\'S": "Ś",
    r"\`a": "à", r"\`e": "è", r"\`i": "ì", r"\`o": "ò", r"\`u": "ù",
    r'\"a': "ä", r'\"e': "ë", r'\"i': "ï", r'\"\i': "ï", r'\"o': "ö", r'\"u': "ü",
    r'\"A': "Ä", r'\"O': "Ö", r'\"U': "Ü",
    r"\^a": "â", r"\^e": "ê", r"\^i": "î", r"\^\i": "î", r"\^o": "ô", r"\^u": "û",
    r"\~a": "ã", r"\~n": "ñ", r"\~o": "õ", r"\~N": "Ñ",
    r"\=a": "ā", r"\=A": "Ā", r"\=e": "ē", r"\=E": "Ē",
    r"\=i": "ī", r"\=\i": "ī", r"\=I": "Ī", r"\=o": "ō", r"\=O": "Ō",
    r"\=u": "ū", r"\=U": "Ū",
    r"\v{s}": "š", r"\v{S}": "Š", r"\v{c}": "č", r"\v{C}": "Č", r"\v{z}": "ž", r"\v{Z}": "Ž",
    r"\v{r}": "ř", r"\v{e}": "ě",
    r"\u{g}": "ğ", r"\u{a}": "ă",
    r"\c{c}": "ç", r"\c{C}": "Ç", r"\c{s}": "ş", r"\c{S}": "Ş",
    r"\c{n}": "ņ", r"\c{N}": "Ņ", r"\c{k}": "ķ", r"\c{l}": "ļ", r"\c{g}": "ģ",
    r"\H{o}": "ő", r"\H{u}": "ű",
    r"\.z": "ż", r"\.Z": "Ż", r"\.I": "İ",
    r"\l": "ł", r"\L": "Ł", r"\o": "ø", r"\O": "Ø", r"\aa": "å", r"\AA": "Å",
    r"\ae": "æ", r"\AE": "Æ", r"\ss": "ß",
}

BIB_SECTION_TITLES_ZH = {
    "01": "量子信息与量子计算总论",
    "02": "算子代数、泛函分析与数学物理",
    "03": "矩阵分析、正定性与迹理想",
    "04": "量子信道、扩张、测量与开放系统生成元",
    "05": "熵、相对熵、保真度与可区分性",
    "06": "量子纠缠、非定域性与量子通信",
    "07": "量子纠错、稳定子、Clifford 理论与费米子编码",
    "08": "量子电路模型、基于测量的量子计算与 ZX 演算",
    "09": "量子算法、搜索、计数与振幅放大",
    "10": "查询复杂度、对手方法、多项式方法与参数估计",
    "11": "量子游走、图算法与布尔公式求值",
    "12": "哈密顿量模拟、乘积公式与量子信号处理",
    "13": "量子线性代数、微分方程与数值算法",
    "14": "量子学习、层析、Gibbs 采样、半正定规划与量子金融",
    "15": "绝热算法、哈密顿量复杂性与量子证明系统",
    "16": "多体量子系统、张量网络、量子化学与变分算法",
    "17": "隐藏子群、Fourier 采样、数论与密码分析",
    "18": "拓扑量子计算与纽结不变量",
    "19": "跨方向算法、复杂性、优化与开放量子系统",
}


def clean_tex(s: str) -> str:
    """Convert BibTeX/LaTeX escapes and protective braces into clean UTF-8 text."""
    if not s:
        return ""
    out = s.strip()
    # Normalize braced accent forms like {\"o} or {\'e} or {\=A}
    out = re.sub(r"\{\\([`'\"^~=.])\{?([A-Za-z]|\\i)\}?\}", r"\\\1\2", out)
    out = re.sub(r"\\([`'\"^~=.])\{([A-Za-z]|\\i)\}", r"\\\1\2", out)
    for k, v in sorted(LATEX_ACCENTS.items(), key=lambda kv: -len(kv[0])):
        out = out.replace("{" + k + "}", v).replace(k, v)
    # Clean common inline math macros before stripping braces
    out = re.sub(r"\\tilde\s*\{?O\}?", "Õ", out)
    out = (
        out.replace(r"\delta", "δ")
        .replace(r"\epsilon", "ε")
        .replace(r"\varepsilon", "ε")
        .replace(r"\Delta", "Δ")
        .replace(r"\Omega", "Ω")
        .replace(r"\Theta", "Θ")
        .replace(r"\alpha", "α")
        .replace(r"\beta", "β")
        .replace(r"\gamma", "γ")
        .replace(r"\lambda", "λ")
    )
    out = re.sub(
        r"\\sqrt\s*\{([^{}]+)\}",
        lambda m: f"√{m.group(1)}" if len(m.group(1)) == 1 else f"√({m.group(1)})",
        out,
    )
    out = re.sub(r"\\sqrt\s+([A-Za-z0-9])", r"√\1", out)
    out = out.replace("---", "—").replace("--", "–").replace("~", " ")
    out = out.replace(r"\&", "&").replace(r"\%", "%").replace(r"\_", "_")
    # Strip inline $...$ math delimiters lightly while keeping symbols readable
    out = re.sub(r"\$([^$]+)\$", r"\1", out)
    # Remove remaining protective braces
    out = out.replace("{", "").replace("}", "")
    out = re.sub(r"\s+", " ", out).strip()
    return out


def format_authors(raw_author: str) -> str:
    if not raw_author:
        return ""
    parts = [clean_tex(p) for p in re.split(r"\s+and\s+", raw_author.replace("\n", " ")) if p.strip()]
    formatted = []
    for p in parts:
        if "," in p:
            last, first = [x.strip() for x in p.split(",", 1)]
            formatted.append(f"{first} {last}".strip())
        else:
            formatted.append(p)
    if len(formatted) > 6:
        return ", ".join(formatted[:5]) + " et al."
    if len(formatted) == 2:
        return f"{formatted[0]} and {formatted[1]}"
    if len(formatted) > 2:
        return ", ".join(formatted[:-1]) + ", and " + formatted[-1]
    return formatted[0]


def parse_references_bib(bib_path: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Parse docs/references.bib into (sections, entries)."""
    if not bib_path.is_file():
        return [], []
    lines = bib_path.read_text(encoding="utf-8").splitlines()
    sections: list[dict[str, Any]] = []
    entries: list[dict[str, Any]] = []

    current_sec_id = "00"
    current_sec_title = "General"
    pending_related: list[str] = []

    i = 0
    n = len(lines)
    sec_re = re.compile(r"^%\s*(\d+)\.\s+(.+?)\s*$")
    entry_start_re = re.compile(r"^@(\w+)\{([^,\s]+)\s*,\s*$")

    while i < n:
        line = lines[i]
        m_sec = sec_re.match(line)
        if m_sec:
            current_sec_id = m_sec.group(1).zfill(2)
            current_sec_title = m_sec.group(2).strip()
            sections.append({"id": current_sec_id, "title": current_sec_title, "count": 0})
            pending_related = []
            i += 1
            continue

        if line.startswith("% Related:"):
            rel_lines = [line[len("% Related:"):].strip()]
            i += 1
            while i < n and lines[i].startswith("%") and not lines[i].startswith("% ---"):
                m_next = sec_re.match(lines[i])
                if m_next:
                    break
                rel_lines.append(lines[i].lstrip("%").strip())
                i += 1
            rel_text = " ".join(rel_lines)
            pending_related = extract_related_paths(rel_text)
            continue

        m_ent = entry_start_re.match(line)
        if m_ent:
            etype = m_ent.group(1).lower()
            citekey = m_ent.group(2).strip()
            raw_block_lines = [line]
            fields: dict[str, str] = {}
            i += 1
            while i < n:
                raw_block_lines.append(lines[i])
                if lines[i].strip() == "}":
                    i += 1
                    break
                m_f = re.match(r"^\s*([A-Za-z0-9_-]+)\s*=\s*\{(.*)", lines[i])
                if m_f:
                    fname = m_f.group(1).lower()
                    val_lines = [m_f.group(2)]
                    # Balance braces across multi-line field values
                    depth = 1 + m_f.group(2).count("{") - m_f.group(2).count("}")
                    while depth > 0 and i + 1 < n:
                        i += 1
                        raw_block_lines.append(lines[i])
                        val_lines.append(lines[i].strip())
                        depth += lines[i].count("{") - lines[i].count("}")
                    joined = " ".join(val_lines).rstrip().rstrip(",").rstrip()
                    if joined.endswith("}"):
                        joined = joined[:-1]
                    fields[fname] = joined.strip()
                i += 1

            venue = (
                clean_tex(fields.get("journal", ""))
                or clean_tex(fields.get("booktitle", ""))
                or clean_tex(fields.get("series", ""))
                or clean_tex(fields.get("publisher", ""))
                or clean_tex(fields.get("school", ""))
                or clean_tex(fields.get("howpublished", ""))
            )
            if not venue and fields.get("eprint"):
                venue = f"arXiv:{clean_tex(fields['eprint'])}"

            entry = {
                "key": citekey,
                "type": etype,
                "section_id": current_sec_id,
                "section_title": current_sec_title,
                "authors": format_authors(fields.get("author", "") or fields.get("editor", "")),
                "title": clean_tex(fields.get("title", citekey)),
                "year": clean_tex(fields.get("year", "")),
                "venue": venue,
                "volume": clean_tex(fields.get("volume", "")),
                "pages": clean_tex(fields.get("pages", "")),
                "doi": clean_tex(fields.get("doi", "")),
                "eprint": clean_tex(fields.get("eprint", "")),
                "url": clean_tex(fields.get("url", "")),
                "note": clean_tex(fields.get("note", "")),
                "section_related": list(pending_related),
                "cited_by_dirs": [],
                "raw_bibtex": "\n".join(raw_block_lines),
            }
            entries.append(entry)
            if sections and sections[-1]["id"] == current_sec_id:
                sections[-1]["count"] += 1
            continue

        i += 1

    return sections, entries


def extract_related_paths(rel_text: str) -> list[str]:
    """Parse '% Related: Foundations/PureStateMath; Concepts/ChannelTheory, QuantumEntropy'."""
    results: list[str] = []
    for clause in rel_text.split(";"):
        clause = clause.strip().rstrip(".")
        current_layer = None
        for item in clause.split(","):
            tok = item.strip()
            if not tok:
                continue
            m = re.match(r"^(Foundations|Concepts|Papers)/([A-Za-z0-9_]+)$", tok)
            if m:
                current_layer = m.group(1)
                results.append(f"Qatlib/{current_layer}/{m.group(2)}")
            elif current_layer and re.match(r"^[A-Z][A-Za-z0-9]*$", tok):
                results.append(f"Qatlib/{current_layer}/{tok}")
    return results


# ---------------------------------------------------------------------------
# Repository scanning: Qatlib/{Foundations,Concepts,Papers}
# ---------------------------------------------------------------------------

DOCSTRING_BLOCK_RE = re.compile(r"/-\!\s*([\s\S]*?)-/")
BRACKET_KEY_RE = re.compile(r"\[([A-Za-z][A-Za-z0-9:_-]{2,60})\]")


def choose_entry_file(lean_files: list[Path], dir_path: Path) -> Path:
    """Pick the most representative .lean file in a topic/paper directory."""
    # Prefer shallowest MainResults/*.lean, then Basic.lean / Defs.lean, then shallowest path
    main_res = [p for p in lean_files if "MainResults" in p.relative_to(dir_path).parts]
    if main_res:
        return sorted(main_res, key=lambda p: (len(p.parts), str(p)))[0]
    for preferred in ("Basic.lean", "Defs.lean"):
        matches = [p for p in lean_files if p.name == preferred]
        if matches:
            return sorted(matches, key=lambda p: (len(p.parts), str(p)))[0]
    return sorted(lean_files, key=lambda p: (len(p.parts), str(p)))[0]


def extract_module_summary(lean_file: Path) -> tuple[str, str]:
    """Extract (# Heading, first prose sentence) from a Lean /-! ... -/ module docstring."""
    try:
        head_txt = lean_file.read_text(encoding="utf-8", errors="ignore")[:32768]
    except OSError:
        return "", ""
    m = DOCSTRING_BLOCK_RE.search(head_txt)
    if not m:
        return "", ""
    body = m.group(1).strip()
    title = ""
    prose_lines: list[str] = []
    for raw_line in body.splitlines():
        line = raw_line.strip()
        if not line:
            if prose_lines:
                break
            continue
        if line.startswith("#"):
            if not title:
                title = line.lstrip("#").strip()
            elif prose_lines:
                break
            continue
        if line.startswith(("*", "- ", "|", "```")):
            if prose_lines:
                break
            continue
        prose_lines.append(line)
        if len(" ".join(prose_lines)) > 200:
            break
    summary = " ".join(prose_lines)
    summary = re.sub(r"`([^`]+)`", r"\1", summary)
    summary = re.sub(r"\[([^\]]+)\]\([^\)]+\)", r"\1", summary)
    summary = re.sub(r"\s+", " ", summary).strip()
    if len(summary) > 210:
        summary = summary[:207].rsplit(" ", 1)[0] + "..."
    return title, summary


def scan_qatlib_tree(repo_root: Path, bib_keys: set[str]) -> dict[str, Any]:
    """Scan Qatlib/{Foundations,Concepts,Papers} for live statistics and directory metadata."""
    qatlib_dir = repo_root / "Qatlib"
    layers_meta: dict[str, dict[str, Any]] = {}
    all_dirs: list[dict[str, Any]] = []
    cite_to_dirs: dict[str, set[str]] = {k: set() for k in bib_keys}

    for layer in ("Foundations", "Concepts", "Papers"):
        layer_path = qatlib_dir / layer
        subdirs = sorted([p for p in layer_path.iterdir() if p.is_dir()]) if layer_path.is_dir() else []
        layer_file_count = 0
        for d in subdirs:
            lean_files = sorted(d.rglob("*.lean"))
            if not lean_files:
                continue
            layer_file_count += len(lean_files)
            rel_dir = f"Qatlib/{layer}/{d.name}"
            entry_file = choose_entry_file(lean_files, d)
            entry_rel_html = entry_file.relative_to(repo_root).with_suffix(".html").as_posix()
            entry_mod = entry_file.relative_to(repo_root).with_suffix("").as_posix().replace("/", ".")
            doc_title, doc_summary = extract_module_summary(entry_file)
            if not doc_title and not doc_summary:
                for alt_lf in lean_files:
                    if alt_lf != entry_file:
                        doc_title, doc_summary = extract_module_summary(alt_lf)
                        if doc_title or doc_summary:
                            break

            # Collect featured modules (up to 6: MainResults first, then Basic/Defs/others)
            featured_files = sorted(
                lean_files,
                key=lambda p: (
                    0 if "MainResults" in p.relative_to(d).parts else (1 if p.name in ("Basic.lean", "Defs.lean") else 2),
                    len(p.parts),
                    str(p),
                ),
            )[:6]
            featured_mods = [
                {
                    "label": p.relative_to(d).with_suffix("").as_posix().replace("/", "."),
                    "html_path": p.relative_to(repo_root).with_suffix(".html").as_posix(),
                }
                for p in featured_files
            ]

            # Scan files in this directory for [Citekey] matches against references.bib
            cited: set[str] = set()
            if bib_keys:
                for lf in lean_files:
                    try:
                        txt = lf.read_text(encoding="utf-8", errors="ignore")
                    except OSError:
                        continue
                    for cand in BRACKET_KEY_RE.findall(txt):
                        if cand in bib_keys:
                            cited.add(cand)
                            cite_to_dirs[cand].add(rel_dir)

            all_dirs.append(
                {
                    "layer": layer,
                    "name": d.name,
                    "rel_dir": rel_dir,
                    "module_count": len(lean_files),
                    "entry_mod": entry_mod,
                    "entry_html": entry_rel_html,
                    "title": doc_title,
                    "summary": doc_summary,
                    "featured_mods": featured_mods,
                    "citations": sorted(cited),
                    "all_lean_rel": [
                        p.relative_to(repo_root).with_suffix("").as_posix() for p in lean_files
                    ],
                }
            )

        layers_meta[layer] = {
            "dir_count": len(subdirs),
            "module_count": layer_file_count,
        }

    total_modules = sum(v["module_count"] for v in layers_meta.values()) + (
        1 if (repo_root / "Qatlib.lean").is_file() else 0
    )
    return {
        "layers": layers_meta,
        "total_modules": total_modules,
        "total_dirs": len(all_dirs),
        "dirs": all_dirs,
        "cite_to_dirs": cite_to_dirs,
    }


def _first_sentence(text: str) -> str:
    """Return a compact first sentence for an inline Lean docstring."""
    compact = re.sub(r"\s+", " ", text or "").strip()
    if not compact:
        return ""
    match = re.search(r"(?<![A-Za-z]\.)\.\s", compact)
    return compact[: match.end()].strip() if match else compact


def _module_doc(text: str) -> tuple[str, str, str]:
    """Extract module title, summary, and source highlights from a module docstring."""
    match = re.search(r"/-!([\s\S]*?)-/", text)
    if not match:
        return "", "", ""
    body = match.group(1).strip()
    title = ""
    prose: list[str] = []
    for raw in body.splitlines():
        line = raw.strip().lstrip("*").strip()
        if not line:
            if prose:
                break
            continue
        if line.startswith("#") and not title:
            title = line.lstrip("#").strip()
            continue
        if line.startswith(("- ", "* ", "|")):
            if prose:
                break
            continue
        prose.append(line)
        if len(" ".join(prose)) > 240:
            break
    summary = _first_sentence(" ".join(prose))
    highlights = ", ".join(sorted(set(m.group(1).lower() for m in SOURCE_HIGHLIGHT_RE.finditer(body))))
    return title, summary, highlights


def _trivia_end(text: str, marker: re.Match[str]) -> int:
    start, pos = marker.span()
    token = marker.group()
    if token == "/-":
        depth = 1
        while depth:
            delimiter = BLOCK_DELIMITER_RE.search(text, pos)
            if delimiter is None:
                return len(text)
            depth += 1 if delimiter.group() == "/-" else -1
            pos = delimiter.end()
        return pos
    if token == "--":
        end = text.find("\n", pos)
        return len(text) if end < 0 else end
    if token == "«":
        closing = "»"
    elif raw := RAW_STRING_RE.fullmatch(token):
        closing = '"' + raw.group(1)
    elif token.endswith('"'):
        return _string_end(text, pos, interpolated=(token != '"'))
    else:
        char = CHAR_LITERAL_RE.match(text, start)
        return char.end() if char else pos
    end = text.find(closing, pos)
    return len(text) if end < 0 else end + len(closing)


def _string_end(text: str, pos: int, *, interpolated: bool) -> int:
    while pos < len(text):
        char = text[pos]
        pos += 1
        if char == '"':
            return pos
        if char == "\\":
            pos += 1
        elif interpolated and char == "{":
            # An interpolated term may contain nested braces, strings and comments.
            depth = 1
            while depth and (marker := INTERPOLATION_RE.search(text, pos)):
                token = marker.group()
                if token in ("{", "}"):
                    depth += 1 if token == "{" else -1
                    pos = marker.end()
                else:
                    pos = _trivia_end(text, marker)
            if depth:
                return len(text)
    return len(text)


def _source_code(text: str) -> tuple[str, dict[int, str]]:
    """Mask Lean comments and literals while retaining source offsets and docstrings."""
    code = list(text)
    docs: dict[int, str] = {}
    pos = line = 0
    while pos < len(text):
        marker = SOURCE_TRIVIA_RE.search(text, pos)
        if marker is None:
            break
        line += text[pos:marker.start()].count("\n")
        start = marker.start()
        pos = _trivia_end(text, marker)
        line += text[start:pos].count("\n")
        # A quoted identifier and a prime in an ordinary identifier are code.
        if marker.group() == "«" or (marker.group() == "'" and pos == marker.end()):
            continue
        if text.startswith("/--", start):
            docs[line] = text[start + 3:pos - 2].strip()
        for index in range(start, pos):
            if code[index] not in "\r\n":
                code[index] = " "
    return "".join(code), docs


def _header_imports(code: str) -> list[str]:
    """Read the leading header, including Lean 4.35 public/meta/all modifiers."""
    imports: list[str] = []
    pos = 0
    while match := HEADER_DIRECTIVE_RE.match(code, pos):
        if imported := match.group("imported"):
            imports.append(imported)
        pos = match.end()
    return sorted(set(imports))


def _module_components(name: str) -> list[str]:
    """Decode Lean import names into individual filesystem path components."""
    return [part.removeprefix("«").removesuffix("»") for part in NAME_PART_RE.findall(name)]


def _parse_source_file(job: tuple[Path, Path]) -> dict[str, Any]:
    """Worker-process parser for one public Lean source file."""
    path, repo_root = job
    text = path.read_text(encoding="utf-8", errors="ignore")
    rel = path.relative_to(repo_root).as_posix()
    parts = Path(rel).parts
    layer = parts[1] if len(parts) > 1 else "Other"
    unit = parts[2] if len(parts) > 2 else path.stem
    unit_dir = Path(*parts[:3]) if len(parts) >= 3 else Path(rel).parent
    after_unit = parts[3:]
    block = after_unit[0] if len(after_unit) > 1 else "(root)"
    module_name = Path(rel).with_suffix("").as_posix().replace("/", ".")
    title, summary, module_highlights = _module_doc(text)
    code, docstrings = _source_code(text)
    imports = _header_imports(code)
    layer_imports: dict[str, list[str]] = {name: [] for name in PANEL_LAYERS}
    for imported in imports:
        components = _module_components(imported)
        if len(components) >= 3 and components[0] == "Qatlib" and components[1] in layer_imports:
            layer_imports[components[1]].append(imported)
    citations = sorted(set(BRACKET_KEY_RE.findall(text)))

    declarations: list[dict[str, Any]] = []
    # Lean creates one scope per dotted name component. Sections affect the
    # scope stack but do not contribute components to declaration namespaces.
    scopes: list[tuple[str, bool]] = []
    pending_doc = ""
    code_lines = code.removesuffix("\n").split("\n") if code else []
    line_offsets = [0]
    for raw in code_lines:
        line_offsets.append(line_offsets[-1] + len(raw) + 1)
    line_no = 0
    while line_no < len(code_lines):
        raw = code_lines[line_no]
        stripped = raw.strip()
        if line_no in docstrings:
            pending_doc = docstrings[line_no]
        if not stripped:
            line_no += 1
            continue
        scope_match = SCOPE_RE.match(raw)
        if scope_match:
            kind = scope_match.group("kind")
            name = scope_match.group("name")
            next_line = line_no + 1
            if name is None:
                while next_line < len(code_lines) and not code_lines[next_line].strip():
                    next_line += 1
                if next_line < len(code_lines):
                    continuation = code_lines[next_line]
                    suffix = SCOPE_NAME_RE.fullmatch(continuation)
                    if suffix and suffix.start(1) > len(raw) - len(raw.lstrip()):
                        candidate = suffix.group(1)
                        parts = NAME_PART_RE.findall(candidate)
                        if kind != "end" or parts == [part for part, _ in scopes[-len(parts):]]:
                            name = candidate
                            line_no = next_line
            parts = NAME_PART_RE.findall(name or "") or [""]
            if kind == "end":
                if parts == [part for part, _ in scopes[-len(parts):]]:
                    del scopes[-len(parts):]
            else:
                scopes.extend((part, kind == "namespace") for part in parts)
            pending_doc = ""
            line_no += 1
            continue
        if stripped == "mutual":
            scopes.append(("", False))
            pending_doc = ""
            line_no += 1
            continue
        declaration_match = DECLARATION_RE.match(code, line_offsets[line_no])
        if declaration_match:
            kind = declaration_match.group("kind")
            name = declaration_match.group("name") or f"anonymous_{line_no + 1}"
            last_line = line_no + code.count("\n", declaration_match.start(), declaration_match.end())
            prefix = [part for part, is_namespace in scopes if is_namespace]
            fqn = name[7:] if name.startswith("_root_.") else ".".join([*prefix, name])
            highlight_text = f"{pending_doc} {' '.join(code_lines[line_no:last_line + 1])}"
            highlights = sorted(
                set(m.group(1).lower() for m in SOURCE_HIGHLIGHT_RE.finditer(highlight_text))
            )
            declarations.append(
                {
                    "name": name,
                    "fqn": fqn,
                    "kind": kind,
                    "line": line_no + 1,
                    "doc": _first_sentence(pending_doc),
                    "source": rel,
                    "highlights": highlights,
                }
            )
            pending_doc = ""
            line_no = last_line + 1
            continue
        pending_doc = ""
        line_no += 1

    return {
        "path": rel,
        "layer": layer,
        "unit": unit,
        "unit_path": "/".join(unit_dir.parts),
        "block": block,
        "module": module_name,
        "title": title,
        "summary": summary,
        "loc": len(code_lines),
        "imports": imports,
        "layer_imports": {key: sorted(set(value)) for key, value in layer_imports.items()},
        "citations": citations,
        "highlights": sorted(set(module_highlights.split(", ") if module_highlights else [])),
        "declarations": declarations,
    }


def scan_catalog_sources(repo_root: Path) -> dict[str, Any]:
    """Build the source-first panel inventory using worker processes."""
    paths = sorted(
        path
        for layer in PANEL_LAYERS
        for path in (repo_root / "Qatlib" / layer).rglob("*.lean")
    )
    jobs = [(path, repo_root) for path in paths]
    if jobs:
        workers = min(8, os.cpu_count() or 1, len(jobs))
        try:
            with ProcessPoolExecutor(max_workers=workers) as pool:
                modules = list(pool.map(_parse_source_file, jobs, chunksize=16))
        except (OSError, RuntimeError):
            modules = [_parse_source_file(job) for job in jobs]
    else:
        modules = []

    units: dict[str, dict[str, Any]] = {}
    layers: dict[str, dict[str, Any]] = {
        layer: {
            "dir_count": 0,
            "module_count": 0,
            "loc": 0,
            "kind_counts": {kind: 0 for kind in DECLARATION_KINDS},
            "highlights": [],
        }
        for layer in PANEL_LAYERS
    }
    seen_units: dict[str, set[str]] = defaultdict(set)
    for module in modules:
        layer = module["layer"]
        unit_key = module["unit"]
        unit = units.setdefault(
            unit_key,
            {
                "id": unit_key,
                "level": layer,
                "title": unit_key,
                "path": module["unit_path"],
                "depends_on": [],
                "blocks": {},
                "modules": [],
                "loc": 0,
                "kind_counts": {kind: 0 for kind in DECLARATION_KINDS},
                "highlights": [],
                "citations": set(),
                "imports": {name: set() for name in PANEL_LAYERS},
            },
        )
        unit["modules"].append(module)
        unit["loc"] += module["loc"]
        unit["citations"].update(module["citations"])
        unit["highlights"].extend(module["highlights"])
        for imported_layer, imported in module["layer_imports"].items():
            unit["imports"][imported_layer].update(imported)
        block = unit["blocks"].setdefault(
            module["block"],
            {
                "id": module["block"],
                "title": module["block"],
                "content": "",
                "boundary": "",
                "goal-rank": "",
                "modules": [],
                "loc": 0,
                "kind_counts": {kind: 0 for kind in DECLARATION_KINDS},
                "declarations": [],
                "highlights": [],
            },
        )
        block["modules"].append(module)
        block["loc"] += module["loc"]
        block["declarations"].extend(module["declarations"])
        block["highlights"].extend(module["highlights"])
        for declaration in module["declarations"]:
            kind = declaration["kind"]
            if kind in DECLARATION_KINDS:
                unit["kind_counts"][kind] += 1
                block["kind_counts"][kind] += 1
                layers[layer]["kind_counts"][kind] += 1
        layers[layer]["module_count"] += 1
        layers[layer]["loc"] += module["loc"]
        seen_units[layer].add(unit_key)
        layers[layer]["highlights"].extend(module["highlights"])

    for layer in PANEL_LAYERS:
        layers[layer]["dir_count"] = len(seen_units[layer])
        layers[layer]["highlights"] = sorted(set(layers[layer]["highlights"]))
    for unit in units.values():
        unit["modules"].sort(key=lambda item: item["path"])
        for block in unit["blocks"].values():
            block["modules"].sort(key=lambda item: item["path"])
            block["declarations"].sort(key=lambda item: (item["line"], item["fqn"]))
            block["highlights"] = sorted(set(block["highlights"]))
        unit["blocks"] = sorted(unit["blocks"].values(), key=lambda item: item["id"])
        unit["citations"] = sorted(unit["citations"])
        unit["highlights"] = sorted(set(unit["highlights"]))
        unit["imports"] = {key: sorted(value) for key, value in unit["imports"].items()}
    return {
        "layers": layers,
        "units": sorted(units.values(), key=lambda item: (item["level"], item["id"])),
        "modules": modules,
        "total_modules": len(modules),
        "total_dirs": sum(value["dir_count"] for value in layers.values()),
    }


def load_panel_metadata(metadata_dir: Path | None) -> dict[str, Any]:
    """Read optional Unit/Paper metadata without requiring it in the public tree."""
    if metadata_dir is None:
        return {"units": [], "papers": [], "units_index": {}}
    if not metadata_dir.is_dir():
        raise ValueError(f"metadata directory does not exist: {metadata_dir}")
    units_index: dict[str, Any] = {}
    index_path = metadata_dir / "units.json"
    if index_path.is_file():
        units_index = json.loads(index_path.read_text(encoding="utf-8"))
    papers_index: dict[str, Any] = {}
    papers_index_path = metadata_dir / "papers.json"
    if papers_index_path.is_file():
        papers_index = json.loads(papers_index_path.read_text(encoding="utf-8"))
    units: list[dict[str, Any]] = []
    for path in sorted((metadata_dir / "units").glob("*/*.json")):
        data = dict(json.loads(path.read_text(encoding="utf-8")))
        data["_source_file"] = path.as_posix()
        data["_index"] = units_index.get(data.get("id", ""), {})
        units.append(data)
    papers: list[dict[str, Any]] = []
    for path in sorted((metadata_dir / "papers").glob("*.json")):
        data = dict(json.loads(path.read_text(encoding="utf-8")))
        data["_source_file"] = path.as_posix()
        data["_index"] = papers_index.get(data.get("id", ""), {})
        papers.append(data)
    return {
        "units": units,
        "papers": papers,
        "units_index": units_index,
        "papers_index": papers_index,
    }


def apply_panel_metadata(catalog: dict[str, Any], metadata: dict[str, Any]) -> dict[str, Any]:
    """Overlay structured Unit/Paper fields onto the source-first inventory."""
    by_public_path: dict[str, dict[str, Any]] = {}
    metadata_by_id: dict[str, dict[str, Any]] = {}
    for data in metadata.get("units", []):
        metadata_by_id[data.get("id", "")] = data
        index = data.get("_index", {})
        paths = list(index.get("public_paths", []))
        for path_key in (index.get("frozen_path"), index.get("dev_path")):
            if path_key:
                paths.append(path_key)
        for path_key in paths:
            norm_path = re.sub(
                r"^[^/]+/(?=(?:Foundations|Concepts|Papers|OpenQuestions)/)",
                "Qatlib/",
                str(path_key),
            )
            by_public_path[norm_path] = data

    matched: set[str] = set()
    for unit in catalog["units"]:
        data = by_public_path.get(unit["path"]) or metadata_by_id.get(unit["id"])
        if data is None:
            continue
        matched.add(data.get("id", ""))
        unit["metadata"] = data
        unit["title"] = data.get("title", unit["title"])
        unit["depends_on"] = list(data.get("depends_on", []))
        meta_blocks = {block.get("id"): block for block in data.get("blocks", [])}
        for block in unit["blocks"]:
            overlay = meta_blocks.get(block["id"])
            if overlay:
                for key in ("title", "content", "boundary", "goal-rank"):
                    if key in overlay:
                        block[key] = overlay[key]
        for block_id, overlay in meta_blocks.items():
            if not any(block["id"] == block_id for block in unit["blocks"]):
                unit["blocks"].append(
                    {
                        "id": block_id,
                        "title": overlay.get("title", block_id),
                        "content": overlay.get("content", ""),
                        "boundary": overlay.get("boundary", ""),
                        "goal-rank": overlay.get("goal-rank", ""),
                        "modules": [],
                        "loc": 0,
                        "kind_counts": {kind: 0 for kind in DECLARATION_KINDS},
                        "declarations": [],
                        "highlights": [],
                    }
                )
        unit["blocks"].sort(key=lambda item: item["id"])

    for data in metadata.get("units", []):
        if data.get("id") in matched:
            continue
        index = data.get("_index", {})
        source_paths = index.get("public_paths", []) or []
        unit = {
            "id": data.get("id", "Unknown"),
            "level": data.get("level", "Foundations"),
            "title": data.get("title", data.get("id", "Unknown")),
            "path": source_paths[0] if source_paths else "",
            "depends_on": list(data.get("depends_on", [])),
            "blocks": [],
            "modules": [],
            "loc": 0,
            "kind_counts": {kind: 0 for kind in DECLARATION_KINDS},
            "highlights": [],
            "citations": [],
            "imports": {name: [] for name in PANEL_LAYERS},
            "metadata": data,
        }
        for block in data.get("blocks", []):
            unit["blocks"].append(
                {
                    "id": block.get("id", "Block"),
                    "title": block.get("title", block.get("id", "Block")),
                    "content": block.get("content", ""),
                    "boundary": block.get("boundary", ""),
                    "goal-rank": block.get("goal-rank", ""),
                    "modules": [],
                    "loc": 0,
                    "kind_counts": {kind: 0 for kind in DECLARATION_KINDS},
                    "declarations": [],
                    "highlights": [],
                }
            )
        catalog["units"].append(unit)

    catalog["units"].sort(key=lambda item: (item["level"], item["id"]))
    catalog["metadata_mode"] = True
    catalog["metadata"] = metadata
    return catalog


def build_panel_papers(
    bib_entries: list[dict[str, Any]], catalog: dict[str, Any], metadata: dict[str, Any]
) -> list[dict[str, Any]]:
    """Merge bibliography entries, source paper units, and optional claims."""
    by_key = {entry["key"]: dict(entry) for entry in bib_entries}
    source_papers = {
        unit["id"]: unit for unit in catalog["units"] if unit["level"] == "Papers"
    }
    metadata_papers = {paper.get("id"): paper for paper in metadata.get("papers", [])}
    for key, paper in metadata_papers.items():
        record = by_key.setdefault(
            key,
            {
                "key": key,
                "title": key,
                "authors": "",
                "year": "",
                "venue": "",
                "doi": "",
                "eprint": "",
                "url": "",
                "section_id": "00",
                "section_title": "General",
                "raw_bibtex": "",
            },
        )
        record["metadata"] = paper
        identity = paper.get("identity", {})
        for field, source_field in (
            ("title", "title"),
            ("year", "year"),
            ("venue", "venue"),
            ("eprint", "arxiv_id"),
            ("doi", "doi"),
        ):
            if identity.get(source_field) and not record.get(field):
                record[field] = identity[source_field]
        if identity.get("authors") and not record.get("authors"):
            record["authors"] = ", ".join(identity["authors"])
    for record in by_key.values():
        record["source_unit"] = source_papers.get(record["key"])
        record.setdefault("metadata", metadata_papers.get(record["key"]))
        record["claims"] = (record.get("metadata") or {}).get("claims", [])
        record["references"] = (record.get("metadata") or {}).get("references", [])
        record["cited_by"] = (
            (record.get("metadata") or {}).get("cited_by")
            or (record.get("metadata") or {}).get("_index", {}).get("cited_by", [])
        )
    return sorted(by_key.values(), key=lambda item: item.get("key", ""))


def _badge(label: str, tone: str = "neutral") -> str:
    return f'<span class="panel-badge panel-badge-{html.escape(tone)}">{html.escape(label)}</span>'


def _coverage_badges(claim: dict[str, Any]) -> str:
    badges: list[str] = []
    claim_text = " ".join(
        str(claim.get(key) or "")
        for key in ("label", "statement", "content")
    ).lower()
    for marker in ("theorem", "lemma", "proposition", "corollary", "counterexample", "erratum", "refutation"):
        if marker in claim_text:
            badges.append(_badge(marker, "partial" if marker in {"counterexample", "erratum", "refutation"} else "neutral"))
    rank = claim.get("claim-rank")
    if rank:
        badges.append(_badge(f"claim-rank {rank}", "rank"))
    if claim.get("status"):
        badges.append(_badge(str(claim["status"]), "status"))
    coverages = sorted(
        set(item.get("coverage", "") for item in claim.get("covered_by", []) if item.get("coverage"))
    )
    for coverage in coverages:
        tone = (
            "full"
            if coverage in {"full", "equivalent"}
            else "partial"
            if coverage in {"partial_support", "restricted"}
            else "neutral"
        )
        badges.append(_badge(coverage.replace("_", " "), tone))
    return " ".join(badges)


def _unit_href(unit_id: str, lang: str, root_prefix: str) -> str:
    return root_prefix + url_for(lang, f"units/{unit_id}.html")


def _paper_href(paper_id: str, lang: str, root_prefix: str) -> str:
    return root_prefix + url_for(lang, f"papers/{paper_id}.html")


def build_catalog_kpi_panel(*, lang: str, tree_stats: dict[str, Any]) -> str:
    t = strings_for(lang)["inventory"]
    kinds = ("theorem", "lemma", "def", "structure", "instance")
    columns = "".join(f"<th>{html.escape(label)}</th>" for label in (*t["columns"], *kinds))
    rows: list[str] = []
    for layer in PANEL_LAYERS:
        stats = tree_stats["catalog"]["layers"][layer]
        values = [stats["module_count"], stats["loc"]] + [
            stats["kind_counts"].get(kind, 0) for kind in kinds
        ]
        rows.append(
            f'<tr><th>{html.escape(layer)}</th>'
            + "".join(f"<td>{value:,}</td>" for value in values)
            + "</tr>"
        )
    return f'''<section class="section panel-kpi-section">
      <div class="section-header"><div class="section-eyebrow">{t["heading"]}</div>
      <h2>{t["title"]}</h2>
      <p>{t["description"]}</p></div>
      <div class="panel-table-wrap"><table class="panel-table"><thead><tr>{columns}</tr></thead><tbody>{"".join(rows)}</tbody></table></div>
    </section>'''


def build_unit_detail_body(
    *, unit: dict[str, Any], lang: str, root_prefix: str, all_unit_ids: set[str]
) -> str:
    page_prefix = root_prefix + url_for(lang)
    t = strings_for(lang)["unit"]
    heading = t["heading"].format(id=unit["id"])

    depends = "".join(
        f'<a class="dir-chip" href="{_unit_href(item, lang, root_prefix)}">{html.escape(item)}</a>'
        for item in unit.get("depends_on", [])
        if item in all_unit_ids
    )
    depends_html = (
        f'<div class="panel-links"><span class="panel-muted">{t["depends_label"]}:</span>{depends}</div>'
        if depends
        else ""
    )
    imports_html: list[str] = []
    for layer, imports in unit.get("imports", {}).items():
        if not imports:
            continue
        links = []
        for imported in imports[:30]:
            components = _module_components(imported)
            if len(components) >= 3:
                fragment = quote("/".join(components[:3]))
                links.append(f'<a class="dir-chip" href="{page_prefix}modules.html#{fragment}">{html.escape(imported)}</a>')
        chips = "".join(links)
        if chips:
            imports_html.append(f'<div class="panel-links"><span class="panel-muted">{html.escape(layer)}:</span>{chips}</div>')
    imports_section = (
        f'<div><div class="panel-muted">{t["imports_label"]}</div>{"".join(imports_html)}</div>'
        if imports_html
        else ""
    )

    columns = "".join(f"<th>{html.escape(label)}</th>" for label in t["columns"])
    block_cards: list[str] = []
    for block in unit.get("blocks", []):
        rank_badge = _badge(f"goal-rank {block.get('goal-rank')}", "rank") if block.get("goal-rank") else ""
        highlight_badges = " ".join(_badge(item, "partial") for item in block.get("highlights", []))
        declarations = block.get("declarations", [])
        rows: list[str] = []
        for declaration in declarations:
            source_link = f'{GITHUB_REPO_URL}/blob/main/{declaration["source"]}#L{declaration["line"]}'
            badges = " ".join(_badge(item, "partial") for item in declaration.get("highlights", []))
            rows.append(
                f'<tr><td>{html.escape(declaration["kind"])}</td>'
                f'<td><a href="{source_link}" target="_blank" rel="noopener"><code>{html.escape(declaration["fqn"])}</code></a></td>'
                f'<td><a href="{source_link}" target="_blank" rel="noopener">L{declaration["line"]}</a></td>'
                f'<td>{html.escape(declaration.get("doc") or "—")} {badges}</td></tr>'
            )
        decl_html = (
            f'<table class="panel-decl-table"><thead><tr>{columns}</tr></thead><tbody>'
            + "".join(rows)
            + "</tbody></table>"
            if rows
            else f'<p class="panel-empty">{t["no_decl"]}</p>'
        )
        modules_html: list[str] = []
        for module in block.get("modules", []):
            module_highlights = " ".join(_badge(item, "partial") for item in module.get("highlights", []))
            module_imports = ", ".join(module.get("imports", [])[:8])
            modules_html.append(
                f'<div class="panel-module-card"><div class="panel-module-head"><strong>{html.escape(module["module"])}</strong>'
                f'<span class="panel-muted">{t["module_stats"].format(loc=module["loc"], declarations=len(module["declarations"]))}</span></div>'
                f'<div class="panel-muted">{html.escape(module.get("summary") or "")} {module_highlights}</div>'
                f'<div class="panel-muted">{t["imports"]}: {html.escape(module_imports or "—")}</div></div>'
            )
        summary = t["block_summary"].format(label=t["block_label"], id=block["id"], declarations=len(declarations))
        block_cards.append(
            f'<article class="panel-card" id="block-{html.escape(block["id"])}">'
            f'<div class="panel-meta"><h2>{html.escape(block.get("title", block["id"]))}</h2>{rank_badge}{highlight_badges}</div>'
            f'<p>{html.escape(block.get("content") or "")}</p>'
            f'<p class="panel-muted"><strong>{t["boundary"]}:</strong> {html.escape(block.get("boundary") or "—")}</p>'
            f'<details open><summary>{html.escape(summary)}</summary>'
            f'{"".join(modules_html)}{decl_html}</details></article>'
        )

    return f'''
  <main class="panel-detail-wrap">
    <div class="panel-detail-header">
      <div class="section-eyebrow">{t["catalog"]}</div>
      <h1>{html.escape(heading)}</h1>
      <p>{html.escape(unit.get("title", unit["id"]))} · {html.escape(t["level_label"])} {html.escape(unit.get("level", ""))} · {unit.get("loc", 0):,} {html.escape(t["loc_label"])} · {len(unit.get("modules", []))} {html.escape(t["module_label"])}</p>
      <p style="margin-top:10px;"><a href="{page_prefix}modules.html">← {html.escape(t["back_label"])}</a></p>
      {depends_html}{imports_section}
    </div>
    <div class="panel-grid">{"".join(block_cards) if block_cards else f'<article class="panel-card"><p class="panel-empty">{t["no_blocks"]}</p></article>'}</div>
  </main>
'''


def build_paper_coverage_body(paper: dict[str, Any], lang: str) -> str:
    """Render the optional paper-level coverage from the supplied metadata."""
    coverage = (paper.get("metadata") or {}).get("coverage_claims")
    if not isinstance(coverage, dict) or not coverage:
        return ""

    aspects = ("math", "asymptotic", "circuit", "resource")
    t = strings_for(lang)["coverage"]
    heading, dimensions, columns = t["heading"], t["dimensions"], t["columns"]
    unknown, unnamed = t["unknown"], t["unnamed"]

    def entries(value: Any) -> list:
        return value if isinstance(value, list) else []

    locators = {
        claim["id"]: claim.get("label") or unnamed
        for claim in entries(paper.get("claims"))
        if isinstance(claim, dict) and isinstance(claim.get("id"), str) and claim["id"]
    }
    rank_labels = {"unknown": unknown, "not_applicable": "N/A"}

    def reader_text(value: str) -> str:
        text = re.sub(r"(?<![A-Za-z0-9_])(?:[A-Za-z][A-Za-z0-9_]*\.)?(c[0-9]{3,5})(?![A-Za-z0-9_])",
                      lambda match: locators.get(match[1], unnamed), value)
        return html.escape(text)

    rows: list[str] = []
    for aspect, dimension in zip(aspects, dimensions, strict=True):
        claim = coverage.get(aspect)
        if not isinstance(claim, dict):
            claim = {}
        rank = claim.get("rank") or "unknown"
        sources = dict.fromkeys(
            reader_text(locators.get(key.rsplit(".", 1)[-1], unnamed))
            for key in entries(claim.get("source_claims")) if isinstance(key, str) and key
        )
        evidence_lines = []
        for item in entries(claim.get("covered_by")):
            if not isinstance(item, dict):
                continue
            fqn = item.get("fqn") or ""
            path = item.get("file") or ""
            method = item.get("coverage") or ""
            note = reader_text(item.get("note") or "")
            # Preserve declared overlay paths verbatim without inferring public links.
            location = html.escape(path)
            if fqn and not re.search(r"(?:^|[._])(?:c[0-9]{3,5}(?:_|$)|Pr[0-9]+|oq[0-9]+)", fqn):
                location = f"<code>{html.escape(fqn)}</code> ({location})" if path else f"<code>{html.escape(fqn)}</code>"
            evidence_lines.append(" · ".join(part for part in (location, html.escape(method.replace("_", " ")), note) if part))
        details = [reader_text(claim[key]) for key in ("reason", "boundary") if claim.get(key)]
        cells = (html.escape(rank_labels.get(rank, rank)), reader_text(claim.get("target") or ""),
                 ", ".join(sources), "<br>".join(evidence_lines), "<br>".join(details))
        rows.append(
            f'<tr><th scope="row">{dimension}</th>'
            + "".join(f"<td>{cell or '—'}</td>" for cell in cells)
            + "</tr>"
        )
    header = "".join(f'<th scope="col">{title}</th>' for title in columns)
    return f"""
    <article class="panel-card"><h2>{heading}</h2>
      <div class="panel-table-wrap"><table class="panel-decl-table panel-coverage-table">
        <thead><tr>{header}</tr></thead>
        <tbody>{"".join(rows)}</tbody>
      </table></div>
    </article>"""


def build_paper_detail_body(
    *, paper: dict[str, Any], lang: str, root_prefix: str, catalog: dict[str, Any]
) -> str:
    page_prefix = root_prefix + url_for(lang)
    identity = (paper.get("metadata") or {}).get("identity", {})
    title = paper.get("title") or identity.get("title") or paper.get("key", "")
    claims = paper.get("claims", [])
    source_unit = paper.get("source_unit")
    t = strings_for(lang)["paper"]

    links: list[str] = []
    if paper.get("doi"):
        links.append(f'<a class="bib-ext-badge" href="https://doi.org/{html.escape(paper["doi"])}" target="_blank" rel="noopener">DOI ↗</a>')
    if paper.get("eprint"):
        links.append(f'<a class="bib-ext-badge" href="https://arxiv.org/abs/{html.escape(paper["eprint"])}" target="_blank" rel="noopener">arXiv:{html.escape(paper["eprint"])} ↗</a>')
    if paper.get("url") and not links:
        links.append(f'<a class="bib-ext-badge" href="{html.escape(paper["url"])}" target="_blank" rel="noopener">URL ↗</a>')
    source_html = ""
    if source_unit:
        source_html = (
            f'<div class="panel-card"><h2>{html.escape(t["source_heading"])}</h2>'
            f'<p><a href="{_unit_href(source_unit["id"], lang, root_prefix)}">{html.escape(source_unit["path"])}</a> · {source_unit["loc"]:,} LOC</p>'
            f'<div class="panel-links">{" ".join(_badge(item, "partial") for item in source_unit.get("highlights", []))}</div></div>'
        )

    unit_ids = {unit["id"] for unit in catalog.get("units", [])}
    columns = "".join(f"<th>{html.escape(label)}</th>" for label in t["columns"])
    claim_cards: list[str] = []
    for claim in claims:
        binds: list[str] = []
        for binding in claim.get("binds", []):
            unit_id = str(binding).split(".", 1)[0]
            href = _unit_href(unit_id, lang, root_prefix) if unit_id in unit_ids else f"{page_prefix}modules.html"
            binds.append(f'<a class="dir-chip" href="{href}">{html.escape(binding)}</a>')
        coverage_rows: list[str] = []
        for item in claim.get("covered_by", []):
            raw_file = str(item.get("file", ""))
            norm_file = re.sub(
                r"^[^/]+/(?=(?:Foundations|Concepts|Papers|OpenQuestions)/)",
                "Qatlib/",
                raw_file,
            )
            file_href = f"{GITHUB_REPO_URL}/blob/main/{norm_file}" if norm_file else ""
            fqn = html.escape(str(item.get("fqn") or ""))
            fqn_html = f'<a href="{file_href}" target="_blank" rel="noopener"><code>{fqn}</code></a>' if file_href else f"<code>{fqn}</code>"
            coverage_rows.append(
                f'<tr><td>{fqn_html}</td><td>{_badge(str(item.get("coverage") or "unrecorded"), "full" if item.get("coverage") in {"full", "equivalent"} else "partial")}</td><td>{html.escape(str(item.get("note") or ""))}</td></tr>'
            )
        coverage_html = (
            f'<table class="panel-decl-table"><thead><tr>{columns}</tr></thead><tbody>'
            + "".join(coverage_rows)
            + "</tbody></table>"
            if coverage_rows
            else f'<p class="panel-empty">{t["no_evidence"]}</p>'
        )
        bind_links = "".join(binds) or f'<span class="panel-empty">{t["no_binds"]}</span>'
        claim_cards.append(
            f'<article class="panel-claim"><h3>{html.escape(claim.get("label") or claim.get("id", "Claim"))} {_coverage_badges(claim)}</h3>'
            f'<p><strong>{html.escape(claim.get("id", ""))}</strong> · {html.escape(claim.get("content") or claim.get("statement") or "")}</p>'
            f'<div class="panel-links">{bind_links}</div>{coverage_html}</article>'
        )
    claims_html = "".join(claim_cards) if claim_cards else f'<p class="panel-empty">{t["no_claims"]}</p>'

    metadata_ids = {
        item.get("id")
        for item in catalog.get("metadata", {}).get("papers", [])
        if item.get("id")
    }

    def paper_chips(ids: list[Any]) -> str:
        chips: list[str] = []
        for item in ids:
            if isinstance(item, dict):
                key = item.get("ref_id") or item.get("id") or item.get("key") or ""
                label = item.get("title") or key
            else:
                key = str(item)
                label = key
            if key in metadata_ids:
                chips.append(
                    f'<a class="dir-chip" href="{_paper_href(key, lang, root_prefix)}">{html.escape(str(label))}</a>'
                )
            else:
                chips.append(f'<span class="dir-chip">{html.escape(str(label))}</span>')
        return "".join(chips)

    return f'''
  <main class="panel-detail-wrap">
    <div class="panel-detail-header">
      <div class="section-eyebrow">{t["explorer"]}</div>
      <h1>{html.escape(paper.get("key", ""))}</h1>
      <p>{html.escape(title)}</p>
      <p class="panel-muted">{html.escape(paper.get("authors", ""))} · {html.escape(paper.get("venue", ""))} · {html.escape(paper.get("year", ""))}</p>
      <div class="panel-links">{"".join(links)}</div>
      <p style="margin-top:10px;"><a href="{page_prefix}papers.html">← {html.escape(t["back_label"])}</a></p>
    </div>
    {source_html}{build_paper_coverage_body(paper, lang)}
    <article class="panel-card"><h2>{html.escape(t["claim_heading"])}</h2>{claims_html}</article>
    <article class="panel-card"><h2>{t["references_heading"]}</h2>
      <div class="panel-links"><span class="panel-muted">{t["references"]}:</span>{paper_chips(paper.get("references", [])) or '<span class="panel-empty">—</span>'}</div>
      <div class="panel-links"><span class="panel-muted">{t["cited_by"]}:</span>{paper_chips(paper.get("cited_by", [])) or '<span class="panel-empty">—</span>'}</div>
    </article>
  </main>
'''


# ---------------------------------------------------------------------------
# Markdown rendering & README table extraction
# ---------------------------------------------------------------------------

def render_markdown_raw(md_text: str) -> str:
    """Render Markdown to HTML using markdown-it-py (with a clean stdlib fallback)."""
    try:
        from markdown_it import MarkdownIt

        md = MarkdownIt("commonmark", {"html": True}).enable("table")
        return md.render(md_text)
    except ImportError:
        return _stdlib_markdown_fallback(md_text)


def _stdlib_markdown_fallback(md_text: str) -> str:
    """Minimal CommonMark + pipe-table fallback if markdown-it-py is absent."""
    lines = md_text.splitlines()
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("```"):
            lang = html.escape(line[3:].strip())
            code_lines = []
            i += 1
            while i < len(lines) and not lines[i].startswith("```"):
                code_lines.append(html.escape(lines[i]))
                i += 1
            cls = f' class="language-{lang}"' if lang else ""
            out.append(f"<pre><code{cls}>" + "\n".join(code_lines) + "</code></pre>")
            i += 1
            continue
        m_h = re.match(r"^(#{1,4})\s+(.*)$", line)
        if m_h:
            lvl = len(m_h.group(1))
            out.append(f"<h{lvl}>{_inline_md(m_h.group(2))}</h{lvl}>")
            i += 1
            continue
        if not line.strip():
            i += 1
            continue
        out.append(f"<p>{_inline_md(line)}</p>")
        i += 1
    return "\n".join(out)


def _inline_md(text: str) -> str:
    text = re.sub(r"`([^`]+)`", lambda m: f"<code>{html.escape(m.group(1))}</code>", text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"\*([^*]+)\*", r"<em>\1</em>", text)
    text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r'<a href="\2">\1</a>', text)
    return text


def slugify(text: str) -> str:
    plain = re.sub(r"<[^>]+>", "", text)
    plain = html.unescape(plain).strip().lower()
    slug = re.sub(r"[^\w\u4e00-\u9fff-]+", "-", plain).strip("-")
    return slug or "section"


def rewrite_repo_href(href: str, source_rel: str, lang: str, root_prefix: str) -> str:
    """Rewrite repository-relative Markdown links so every link works on GitHub Pages."""
    if not href or href.startswith(("#", "http://", "https://", "mailto:")):
        return href

    # Split anchor
    path_part, sep, frag = href.partition("#")
    anchor = f"#{frag}" if sep else ""

    src_dir = Path(source_rel).parent
    resolved = os.path.normpath((src_dir / path_part).as_posix()).lstrip("./")

    guides = {
        f"{stem}{locale['md_suffix']}.md": url_for(key, page)
        for stem, page in GUIDE_PAGES.items()
        for key, locale in LOCALES.items()
    }
    guides["CHANGELOG.md"] = url_for(lang, "changelog.html")
    if resolved in guides:
        target = guides[resolved]
        return root_prefix + target + (anchor if "#" not in target else "")

    # Map Qatlib directory links to Module Explorer / API Reference
    mod_page = root_prefix + url_for(lang, "modules.html")
    if resolved == "Qatlib":
        return mod_page
    if resolved in ("Qatlib/Foundations", "Qatlib/Concepts", "Qatlib/Papers"):
        layer = resolved.split("/", 1)[1]
        return f"{mod_page}#layer={layer}"
    if resolved.startswith("Qatlib/") and not resolved.endswith(".lean"):
        return f"{mod_page}#{resolved}"
    if resolved.startswith("Qatlib/") and resolved.endswith(".lean"):
        html_rel = resolved[:-5] + ".html"
        return f"{root_prefix}docs/{html_rel}{anchor}"

    # Fallback: link repository files (LICENSE, lakefile.toml, scripts/*.lean, etc.) to GitHub
    return f"{GITHUB_REPO_URL}/blob/main/{resolved}{anchor}"


def process_markdown_guide(
    md_path: Path,
    repo_root: Path,
    lang: str,
    root_prefix: str,
    strip_h1: bool = True,
    *,
    section_id: str | None = None,
) -> tuple[str, str, list[dict[str, Any]]]:
    """Render a Markdown guide or one explicitly anchored H2 section."""
    raw = md_path.read_text(encoding="utf-8")
    if section_id is not None:
        section = re.search(
            rf'^## <a id="{re.escape(section_id)}"></a>[^\n]*\n.*?(?=^## |\Z)',
            raw,
            re.MULTILINE | re.DOTALL,
        )
        raw = section.group() if section else ""
    lines = raw.splitlines()
    # The root README uses the vector wordmark as its visual title. Keep a
    # stable page title if this renderer is ever pointed at either README
    # after the decorative ``# Qatlib`` heading has been removed.
    is_root_readme = md_path.parent.resolve() == repo_root.resolve() and md_path.name in {
        "README.md",
        "README.en.md",
    }
    title = "Qatlib" if is_root_readme else md_path.stem
    cleaned_lines: list[str] = []
    h1_stripped = False
    fence_char: str | None = None

    for line in lines:
        # Remove repo language-switch blockquote banner (> 🌐 [English version](...))
        if re.match(r"^>\s*🌐\s*\[", line.strip()):
            continue
        fence_m = re.match(r"^\s*(`{3,}|~{3,})", line)
        if fence_m:
            marker_char = fence_m.group(1)[0]
            if fence_char is None:
                fence_char = marker_char
            elif fence_char == marker_char:
                fence_char = None
            cleaned_lines.append(line)
            continue
        if strip_h1 and not h1_stripped and fence_char is None and line.startswith("# "):
            title = line[2:].strip()
            h1_stripped = True
            continue
        cleaned_lines.append(line)

    html_body = render_markdown_raw("\n".join(cleaned_lines))
    source_rel = md_path.relative_to(repo_root).as_posix()

    # Add heading IDs and collect h2/h3 TOC
    toc: list[dict[str, Any]] = []
    used_ids: set[str] = set()

    def _heading_repl(m: re.Match[str]) -> str:
        lvl = int(m.group(1))
        inner = m.group(2)
        explicit_id_m = re.search(r'<a\s+id="([^"]+)"\s*>\s*</a>', inner)
        if explicit_id_m:
            hid = explicit_id_m.group(1)
            inner_clean = re.sub(r'<a\s+id="[^"]+"\s*>\s*</a>', "", inner).strip()
        else:
            hid = slugify(inner)
            inner_clean = inner
        base = hid
        idx = 2
        while hid in used_ids:
            hid = f"{base}-{idx}"
            idx += 1
        used_ids.add(hid)
        plain_label = html.unescape(re.sub(r"<[^>]+>", "", inner_clean)).strip()
        if lvl in (2, 3) and plain_label:
            toc.append({"level": lvl, "id": hid, "text": plain_label})
        return (
            f'<h{lvl} id="{hid}">{inner_clean}'
            f'<a class="heading-anchor" href="#{hid}" aria-hidden="true" tabindex="-1">#</a></h{lvl}>'
        )

    html_body = re.sub(r"<h([234])>([\s\S]*?)</h\1>", _heading_repl, html_body)

    # Rewrite hrefs
    def _href_repl(m: re.Match[str]) -> str:
        orig = m.group(1)
        new_href = rewrite_repo_href(orig, source_rel, lang, root_prefix)
        ext_attrs = ' target="_blank" rel="noopener"' if new_href.startswith("http") else ""
        return f'href="{new_href}"{ext_attrs}'

    html_body = re.sub(r'href="([^"]+)"', _href_repl, html_body)

    # Wrap <pre><code> blocks with header bar + copy button
    copy_label = strings_for(lang)["ui"]["copy"]

    def _code_repl(m: re.Match[str]) -> str:
        cls_attr = m.group(1) or ""
        code_inner = m.group(2)
        lang_m = re.search(r"language-([A-Za-z0-9_-]+)", cls_attr)
        code_lang = lang_m.group(1) if lang_m else "text"
        lang_badge = code_lang.upper() if code_lang != "text" else "CODE"
        return (
            f'<div class="code-card">'
            f'<div class="code-card-header"><span class="code-lang">{lang_badge}</span>'
            f'<button type="button" class="copy-btn" data-copy-label="{copy_label}">{copy_label}</button></div>'
            f"<pre><code{cls_attr}>{code_inner}</code></pre></div>"
        )

    html_body = re.sub(r"<pre><code([^>]*)>([\s\S]*?)</code></pre>", _code_repl, html_body)
    return title, html_body, toc


def parse_readme_areas_and_bibtex(readme_path: Path) -> tuple[list[dict[str, Any]], str]:
    """Extract the thematic research areas table and BibTeX snippet directly from README."""
    raw = readme_path.read_text(encoding="utf-8")
    areas: list[dict[str, Any]] = []

    for line in raw.splitlines():
        s = line.strip()
        if not s.startswith("| **"):
            continue
        cells = [c.strip() for c in s.strip("|").split("|")]
        if len(cells) < 3:
            continue
        raw_area = re.sub(r"^\*\*|\*\*$", "", cells[0]).strip()
        num_m = re.match(r"^(\d+)\.\s*(.+)$", raw_area)
        num = num_m.group(1).zfill(2) if num_m else ""
        area_title = num_m.group(2).strip() if num_m else raw_area
        topics = clean_inline_markdown_plain(cells[1])
        dirs = re.findall(r"\(\./(Qatlib/[^)]+)\)", cells[2])
        areas.append(
            {
                "num": num,
                "title": area_title,
                "topics": topics,
                "dirs": [d.rstrip("/") for d in dirs],
            }
        )

    bib_m = re.search(r"```bibtex\s*([\s\S]*?)```", raw)
    bibtex_str = bib_m.group(1).strip() if bib_m else ""
    return areas, bibtex_str


def clean_inline_markdown_plain(s: str) -> str:
    s = re.sub(r"`([^`]+)`", r"\1", s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"\1", s)
    return s.strip()


# ---------------------------------------------------------------------------
# Stylesheet & Client-side Script
# ---------------------------------------------------------------------------

SITE_CSS = """/* Qatlib Documentation Portal — Clean Academic Design
 * Brand Palette: Ink Blue (#263F5F), Teal Ink (#245858), Plum Slate (#5B4D68)
 */
:root {
  --bg: #f8fafd;
  --bg-elevated: #ffffff;
  --bg-subtle: #f0f4fa;
  --bg-code: #0f1724;
  --fg: #182232;
  --fg-muted: #526178;
  --fg-faint: #7b8ba3;
  --border: #dfe6f0;
  --border-strong: #c7d3e3;
  --brand: #263f5f;
  --brand-hover: #1b2e47;
  --brand-soft: rgba(38, 63, 95, 0.08);
  --teal: #245858;
  --teal-soft: rgba(36, 88, 88, 0.10);
  --plum: #5b4d68;
  --plum-soft: rgba(91, 77, 104, 0.10);
  --shadow-sm: 0 1px 2px rgba(15, 23, 36, 0.04), 0 4px 12px rgba(15, 23, 36, 0.03);
  --shadow-md: 0 4px 16px rgba(15, 23, 36, 0.06), 0 1px 3px rgba(15, 23, 36, 0.04);
  --radius: 12px;
  --radius-sm: 8px;
  --font-sans: Inter, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto,
    "PingFang SC", "HarmonyOS Sans SC", "Source Han Sans SC",
    "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", sans-serif;
  --font-mono: "JetBrains Mono", "JuliaMono", ui-monospace, SFMono-Regular,
    Menlo, Monaco, Consolas, "Sarasa Mono SC", "Noto Sans Mono CJK SC",
    "Source Han Mono SC", "PingFang SC", "Source Han Sans SC",
    "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", monospace;
  --prose-leading: 1.72;
  --nav-h: 64px;
}

[data-theme="dark"] {
  --bg: #0c121d;
  --bg-elevated: #131c2b;
  --bg-subtle: #192538;
  --bg-code: #090e17;
  --fg: #e6edf7;
  --fg-muted: #9cb0c9;
  --fg-faint: #6c819c;
  --border: #223147;
  --border-strong: #314663;
  --brand: #dbedff;
  --brand-hover: #b2d0f5;
  --brand-soft: rgba(140, 182, 235, 0.13);
  --teal: #66c2bd;
  --teal-soft: rgba(102, 194, 189, 0.13);
  --plum: #c3aed6;
  --plum-soft: rgba(195, 174, 214, 0.14);
  --shadow-sm: 0 1px 3px rgba(0, 0, 0, 0.3);
  --shadow-md: 0 8px 24px rgba(0, 0, 0, 0.35);
}

*, *::before, *::after { box-sizing: border-box; }
button, input, select, textarea { font-family: inherit; }
html { scroll-behavior: smooth; scroll-padding-top: calc(var(--nav-h) + 24px); }
body {
  margin: 0;
  background: var(--bg);
  color: var(--fg);
  font-family: var(--font-sans);
  font-size: 16px;
  line-height: 1.68;
  -webkit-font-smoothing: antialiased;
}

a { color: var(--brand); text-decoration: none; transition: color 0.15s ease; }
a:hover { color: var(--brand-hover); }
:is(a, button, input, select, textarea, summary):focus-visible {
  outline: 2px solid var(--brand);
  outline-offset: 3px;
}
.skip-link {
  position: fixed;
  inset: 8px auto auto 8px;
  z-index: 101;
  padding: 8px 12px;
  background: var(--bg-elevated);
  border-radius: var(--radius-sm);
  transform: translateY(-150%);
}
.skip-link:focus { transform: none; }

/* Sticky Top Navigation */
.site-header {
  position: sticky;
  top: 0;
  z-index: 100;
  min-height: var(--nav-h);
  background: color-mix(in srgb, var(--bg-elevated) 88%, transparent);
  backdrop-filter: blur(12px);
  -webkit-backdrop-filter: blur(12px);
  border-bottom: 1px solid var(--border);
}
.nav-inner {
  max-width: 1600px;
  min-height: var(--nav-h);
  margin: 0 auto;
  padding: 8px 24px;
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 16px;
}
.nav-brand {
  display: flex;
  align-items: center;
  gap: 10px;
  flex-shrink: 0;
}
.brand-link {
  display: inline-flex;
  align-items: center;
  gap: 10px;
  color: var(--brand);
  font-weight: 700;
}
.brand-link:hover { opacity: 0.88; }
.brand-wordmark { display: block; }
.brand-wordmark img { display: block; width: 100%; height: auto; }
.brand-wordmark .wordmark-dark, [data-theme="dark"] .brand-wordmark .wordmark-light { display: none; }
[data-theme="dark"] .brand-wordmark .wordmark-dark { display: block; }
.nav-wordmark { width: 104px; }
.toolchain-pill {
  font-family: var(--font-mono);
  font-size: 11.5px;
  font-weight: 600;
  padding: 2px 8px;
  border-radius: 999px;
  background: var(--brand-soft);
  color: var(--brand);
  border: 1px solid color-mix(in srgb, var(--brand) 22%, transparent);
  white-space: nowrap;
}

.nav-links {
  display: flex;
  align-items: center;
  gap: 4px;
}
.nav-links a {
  padding: 6px 9px;
  border-radius: var(--radius-sm);
  color: var(--fg-muted);
  font-size: 13.8px;
  font-weight: 500;
  white-space: nowrap;
}
.nav-links a:hover, .nav-links a.active {
  color: var(--fg);
  background: var(--bg-subtle);
}
.nav-links a.nav-api-btn {
  color: var(--brand);
  background: var(--brand-soft);
  font-weight: 600;
  margin-left: 4px;
}
.nav-links a.nav-api-btn:hover {
  background: color-mix(in srgb, var(--brand) 18%, transparent);
}

.nav-actions {
  display: flex;
  align-items: center;
  gap: 8px;
  flex-shrink: 0;
}
.nav-search-form {
  position: relative;
  display: flex;
  align-items: center;
}
.nav-search-input {
  width: 165px;
  padding: 6px 30px 6px 11px;
  border-radius: var(--radius-sm);
  border: 1px solid var(--border);
  background: var(--bg);
  color: var(--fg);
  font-size: 13px;
  font-family: var(--font-sans);
  transition: border-color 0.15s, width 0.2s;
}
.nav-search-input:focus {
  outline: none;
  border-color: var(--brand);
  width: 195px;
}
.nav-search-kbd {
  position: absolute;
  right: 8px;
  font-family: var(--font-mono);
  font-size: 11px;
  color: var(--fg-faint);
  border: 1px solid var(--border);
  border-radius: 4px;
  padding: 0 5px;
  pointer-events: none;
}

.icon-btn {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  height: 34px;
  padding: 0 10px;
  border-radius: var(--radius-sm);
  border: 1px solid var(--border);
  background: var(--bg-elevated);
  color: var(--fg-muted);
  font-size: 13px;
  font-weight: 600;
  white-space: nowrap;
  flex-shrink: 0;
  cursor: pointer;
}
.icon-btn:hover {
  color: var(--fg);
  border-color: var(--border-strong);
  background: var(--bg-subtle);
}
.lang-switcher { position: relative; flex-shrink: 0; }
.lang-switcher[open] { z-index: 2; }
.lang-switcher summary { gap: 6px; list-style: none; }
.lang-switcher summary::-webkit-details-marker { display: none; }
.lang-switcher :is(summary, a):focus-visible {
  outline: 2px solid var(--brand);
  outline-offset: 2px;
}
.lang-options {
  position: absolute;
  inset-inline-end: 0;
  top: calc(100% + 6px);
  min-width: 140px;
  padding: 4px;
  border: 1px solid var(--border);
  border-radius: var(--radius-sm);
  background: var(--bg-elevated);
  box-shadow: var(--shadow-md);
}
.lang-options a {
  display: flex;
  justify-content: space-between;
  align-items: center;
  gap: 10px;
  padding: 7px 9px;
  border-radius: 4px;
  color: var(--fg);
  font-size: 13px;
  white-space: nowrap;
}
.lang-options a:hover, .lang-options a[aria-current="page"] {
  background: var(--brand-soft);
  color: var(--brand);
}
.mobile-menu-btn { display: none; }

/* Hero Section */
.hero {
  position: relative;
  padding: 60px 24px 48px;
  border-bottom: 1px solid var(--border);
  background:
    radial-gradient(900px 340px at 50% -60px, var(--brand-soft), transparent 70%),
    var(--bg-elevated);
}
.hero-inner {
  max-width: 1180px;
  margin: 0 auto;
  display: grid;
  grid-template-columns: 1.06fr 0.94fr;
  gap: 36px;
  align-items: center;
}
.qs-panel .code-card pre {
  font-size: 12.2px;
  padding: 12px 14px;
}
.hero-wordmark {
  width: 240px;
  max-width: 100%;
  margin-bottom: 16px;
}
.hero-eyebrow {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  font-size: 12.5px;
  font-weight: 600;
  letter-spacing: 0.02em;
  padding: 4px 12px;
  border-radius: 999px;
  background: var(--teal-soft);
  color: var(--teal);
  margin-bottom: 16px;
}
.hero h1 {
  margin: 0 0 14px;
  font-size: clamp(26px, 3.3vw, 38px);
  line-height: 1.22;
  letter-spacing: -0.02em;
  color: var(--fg);
}
.hero-lead {
  margin: 0 0 24px;
  font-size: 16.5px;
  color: var(--fg-muted);
  max-width: 620px;
}
.hero-ctas {
  display: flex;
  flex-wrap: wrap;
  gap: 10px;
}
.btn {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 10px;
  min-height: 46px;
  padding: 8px 14px;
  border-radius: var(--radius-sm);
  font-size: 14px;
  font-weight: 600;
  line-height: 1.35;
  text-align: center;
  border: 1px solid transparent;
  transition: background-color 0.15s, border-color 0.15s, color 0.15s;
}
.btn-primary {
  background: var(--brand);
  color: #ffffff;
}
.btn-primary:hover { background: var(--brand-hover); color: #ffffff; }
[data-theme="dark"] .btn-primary {
  color: #0b1320;
}
.btn-secondary {
  background: var(--bg);
  color: var(--brand);
  border-color: var(--border-strong);
}
.btn-secondary:hover {
  background: var(--bg-subtle);
  border-color: var(--brand);
}
.hero-resources {
  display: flex;
  flex-wrap: wrap;
  column-gap: 18px;
  margin-top: 12px;
  border-top: 1px solid var(--border);
}
.hero-resources a {
  display: inline-flex;
  align-items: center;
  min-height: 44px;
  color: var(--fg-muted);
  font-size: 13.5px;
  font-weight: 500;
}
.hero-resources a:hover,
.footer-nav a:hover {
  color: var(--brand);
  text-decoration: underline;
  text-underline-offset: 3px;
}

/* Quickstart Card in Hero */
.quickstart-card {
  background: var(--bg);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  box-shadow: var(--shadow-md);
  overflow: hidden;
}
.qs-tabs {
  display: flex;
  border-bottom: 1px solid var(--border);
  background: var(--bg-subtle);
}
.qs-tab {
  flex: 1;
  padding: 10px 14px;
  border: none;
  background: transparent;
  color: var(--fg-muted);
  font-size: 13px;
  font-weight: 600;
  cursor: pointer;
  border-bottom: 2px solid transparent;
}
.qs-tab.active {
  color: var(--brand);
  background: var(--bg-elevated);
  border-bottom-color: var(--brand);
}
.qs-panel { display: none; padding: 16px; }
.qs-panel.active { display: block; }
.qs-caption {
  font-size: 12.5px;
  color: var(--fg-muted);
  margin: 0 0 8px;
}

/* Metrics Strip */
.metrics-strip {
  max-width: 1160px;
  margin: 28px auto 0;
  padding-top: 24px;
  border-top: 1px solid var(--border);
  display: grid;
  grid-template-columns: repeat(5, 1fr);
  gap: 16px;
}
.metric-item {
  display: flex;
  flex-direction: column;
  gap: 2px;
}
.metric-val {
  font-family: var(--font-mono);
  font-variant-numeric: tabular-nums;
  font-size: 22px;
  font-weight: 700;
  color: var(--brand);
}
.metric-label {
  font-size: 13px;
  color: var(--fg-muted);
}

/* Main Sections */
.section {
  max-width: 1160px;
  margin: 0 auto;
  padding: 52px 24px;
}
.section + .section {
  border-top: 1px solid var(--border);
}
.section-header {
  margin-bottom: 28px;
}
.section-eyebrow {
  font-family: var(--font-mono);
  font-size: 12px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: var(--teal);
  margin-bottom: 6px;
}
.section-header h2 {
  margin: 0 0 8px;
  font-size: 26px;
  letter-spacing: -0.015em;
}
.section-header p {
  margin: 0;
  color: var(--fg-muted);
  max-width: 720px;
}

/* 3-Layer Architecture Grid */
.layers-grid {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 20px;
}
.layer-card {
  min-width: 0;
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 24px;
  box-shadow: var(--shadow-sm);
  display: flex;
  flex-direction: column;
  transition: border-color 0.15s, transform 0.15s;
}
.layer-card:hover {
  border-color: var(--brand);
  transform: translateY(-2px);
}
.layer-badge {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 8px;
  font-family: var(--font-mono);
  font-size: 11.5px;
  font-weight: 600;
  white-space: nowrap;
  padding: 5px 10px;
  border-radius: 6px;
  margin-bottom: 14px;
}
.layer-foundations .layer-badge { background: var(--brand-soft); color: var(--brand); }
.layer-concepts .layer-badge { background: var(--teal-soft); color: var(--teal); }
.layer-papers .layer-badge { background: var(--plum-soft); color: var(--plum); }
.layer-card h3 { margin: 0 0 8px; font-size: 19px; }
.layer-card p { margin: 0 0 16px; font-size: 14.5px; color: var(--fg-muted); flex: 1; }
.layer-card-footer {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding-top: 12px;
  border-top: 1px solid var(--border);
  font-size: 13.5px;
  font-weight: 600;
}

/* 8 Thematic Areas Grid */
.areas-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 20px;
}
.area-card {
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 22px 24px;
  box-shadow: var(--shadow-sm);
  display: flex;
  flex-direction: column;
  gap: 10px;
}
.area-head {
  display: flex;
  align-items: baseline;
  gap: 10px;
}
.area-num {
  font-family: var(--font-mono);
  font-size: 12.5px;
  font-weight: 700;
  color: var(--teal);
  background: var(--teal-soft);
  padding: 2px 8px;
  border-radius: 6px;
}
.area-card h3 {
  margin: 0;
  font-size: 17px;
  line-height: 1.35;
}
.area-topics {
  margin: 0;
  font-size: 14px;
  color: var(--fg-muted);
  line-height: 1.58;
}
.chip-list {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  margin-top: 4px;
}
.dir-chip {
  font-family: var(--font-mono);
  font-size: 12px;
  padding: 3px 9px;
  border-radius: 6px;
  background: var(--bg-subtle);
  border: 1px solid var(--border);
  color: var(--fg);
}
.dir-chip:hover {
  border-color: var(--brand);
  color: var(--brand);
  background: var(--brand-soft);
}

/* 3-Column Documentation Layout (CSLib-inspired) */
.docs-shell {
  max-width: 1280px;
  margin: 0 auto;
  padding: 36px 24px 72px;
  display: grid;
  grid-template-columns: 230px minmax(0, 1fr) 220px;
  gap: 40px;
  align-items: start;
}
.docs-sidebar, .docs-toc {
  position: sticky;
  top: calc(var(--nav-h) + 28px);
}
.sidebar-group-title {
  font-size: 11.5px;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.07em;
  color: var(--fg-faint);
  margin: 0 0 10px;
}
.sidebar-nav {
  list-style: none;
  padding: 0;
  margin: 0 0 24px;
  display: flex;
  flex-direction: column;
  gap: 3px;
}
.sidebar-nav a {
  display: block;
  padding: 7px 12px;
  border-radius: var(--radius-sm);
  font-size: 14px;
  color: var(--fg-muted);
  font-weight: 500;
}
.sidebar-nav a:hover {
  color: var(--fg);
  background: var(--bg-subtle);
}
.sidebar-nav a.active {
  color: var(--brand);
  background: var(--brand-soft);
  font-weight: 600;
}

.toc-list {
  list-style: none;
  padding: 0;
  margin: 0;
  border-left: 1px solid var(--border);
}
.toc-list li a {
  display: block;
  padding: 5px 0 5px 14px;
  font-size: 13px;
  color: var(--fg-muted);
  line-height: 1.4;
  border-left: 2px solid transparent;
  margin-left: -1px;
}
.toc-list li.toc-h3 a { padding-left: 26px; font-size: 12.5px; }
.toc-list li a:hover, .toc-list li a.active {
  color: var(--brand);
  border-left-color: var(--brand);
}

/* Prose Typography */
.prose {
  line-height: var(--prose-leading);
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 36px 42px;
  box-shadow: var(--shadow-sm);
  min-width: 0;
}
.prose-header {
  padding-bottom: 20px;
  margin-bottom: 26px;
  border-bottom: 1px solid var(--border);
}
.prose-header h1 {
  margin: 0 0 8px;
  font-size: 30px;
  letter-spacing: -0.02em;
}
.prose-source-link {
  font-size: 13px;
  color: var(--fg-faint);
}
.prose h2 {
  margin: 34px 0 14px;
  padding-bottom: 8px;
  border-bottom: 1px solid var(--border);
  font-size: 21px;
}
.prose > h2:first-child { margin-top: 0; }
.prose h3 { margin: 24px 0 10px; font-size: 17px; }
.prose p, .prose ul, .prose ol { margin: 0 0 16px; }
.prose ul, .prose ol { padding-left: 22px; }
.prose li { margin-bottom: 6px; }
.prose code {
  font-family: var(--font-mono);
  font-size: 0.875em;
  padding: 2px 6px;
  border-radius: 5px;
  background: var(--bg-subtle);
  border: 1px solid var(--border);
}
.prose blockquote {
  margin: 18px 0;
  padding: 14px 18px;
  border-left: 4px solid var(--brand);
  background: var(--brand-soft);
  border-radius: 0 var(--radius-sm) var(--radius-sm) 0;
}
.prose blockquote p:last-child, .prose blockquote ul:last-child { margin-bottom: 0; }
.prose table {
  width: 100%;
  border-collapse: collapse;
  margin: 20px 0;
  font-size: 14.5px;
}
.prose th, .prose td {
  padding: 10px 12px;
  border: 1px solid var(--border);
  text-align: left;
  vertical-align: top;
}
.prose th { background: var(--bg-subtle); font-weight: 600; }
.heading-anchor {
  opacity: 0;
  margin-left: 8px;
  font-weight: 400;
  color: var(--fg-faint);
  user-select: none;
  -webkit-user-select: none;
}
.prose h2:hover .heading-anchor, .prose h3:hover .heading-anchor { opacity: 1; }

/* Code Cards */
.code-card {
  margin: 14px 0 20px;
  border-radius: var(--radius-sm);
  overflow: hidden;
  background: var(--bg-code);
  border: 1px solid #223046;
}
.code-card-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 6px 12px;
  background: rgba(255, 255, 255, 0.04);
  border-bottom: 1px solid rgba(255, 255, 255, 0.08);
}
.code-lang {
  font-family: var(--font-mono);
  font-size: 11px;
  font-weight: 600;
  color: #8fa6c4;
  letter-spacing: 0.05em;
}
.copy-btn {
  font-family: var(--font-sans);
  font-size: 12px;
  padding: 2px 9px;
  border-radius: 5px;
  border: 1px solid rgba(255, 255, 255, 0.16);
  background: rgba(255, 255, 255, 0.05);
  color: #d4e0f0;
  cursor: pointer;
}
.copy-btn:hover { background: rgba(255, 255, 255, 0.14); }
.code-card pre {
  margin: 0;
  padding: 14px 16px;
  overflow-x: auto;
  color: #e6edf7;
  font-family: var(--font-mono);
  font-size: 13px;
  line-height: 1.58;
}
.code-card pre code {
  background: none;
  border: none;
  padding: 0;
  color: inherit;
  font-size: inherit;
}

/* Explorer Pages (modules.html & papers.html) */
.explorer-wrap {
  max-width: 1200px;
  margin: 0 auto;
  padding: 36px 24px 72px;
}
.explorer-toolbar {
  display: flex;
  flex-wrap: wrap;
  gap: 12px;
  align-items: center;
  justify-content: space-between;
  margin: 22px 0 24px;
  padding: 16px;
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  box-shadow: var(--shadow-sm);
}
.filter-input {
  flex: 1;
  min-width: 240px;
  padding: 9px 14px;
  border-radius: var(--radius-sm);
  border: 1px solid var(--border-strong);
  background: var(--bg);
  color: var(--fg);
  font-size: 14.5px;
}
.filter-input:focus { outline: none; border-color: var(--brand); }
.filter-pills {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
}
.filter-pill {
  padding: 7px 13px;
  border-radius: 999px;
  border: 1px solid var(--border);
  background: var(--bg);
  color: var(--fg-muted);
  font-size: 13px;
  font-weight: 600;
  cursor: pointer;
}
.filter-pill.active, .filter-pill:hover {
  background: var(--brand-soft);
  color: var(--brand);
  border-color: var(--brand);
}
.chapter-select {
  padding: 8px 12px;
  border-radius: var(--radius-sm);
  border: 1px solid var(--border-strong);
  background: var(--bg);
  color: var(--fg);
  font-size: 13.5px;
  max-width: 360px;
}
.results-status {
  font-size: 13.5px;
  color: var(--fg-muted);
  margin-bottom: 14px;
}

.mod-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 16px;
}
.mod-card {
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 18px 20px;
  display: flex;
  flex-direction: column;
  gap: 8px;
}
.mod-card.highlight-target {
  border-color: var(--brand);
  box-shadow: 0 0 0 3px var(--brand-soft);
}
.mod-card-top {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 8px;
}
.mod-layer-tag {
  font-family: var(--font-mono);
  font-size: 11.5px;
  font-weight: 600;
  padding: 2px 8px;
  border-radius: 5px;
}
.mod-layer-Foundations { background: var(--brand-soft); color: var(--brand); }
.mod-layer-Concepts { background: var(--teal-soft); color: var(--teal); }
.mod-layer-Papers { background: var(--plum-soft); color: var(--plum); }
.mod-count { font-family: var(--font-mono); font-size: 12px; color: var(--fg-faint); }
.mod-name {
  margin: 0;
  font-family: var(--font-mono);
  font-size: 16px;
  font-weight: 700;
}
.mod-subtitle { font-size: 14px; font-weight: 600; color: var(--fg); margin: 0; }
.mod-desc { font-size: 13.5px; color: var(--fg-muted); margin: 0; line-height: 1.52; }
.mod-actions {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 10px;
  margin-top: auto;
  padding-top: 8px;
  border-top: 1px solid var(--border);
  font-size: 13px;
  font-weight: 600;
}
.mod-details summary {
  cursor: pointer;
  font-size: 12.5px;
  color: var(--fg-muted);
}
.mod-leaf-list {
  margin: 8px 0 0;
  padding-left: 18px;
  font-family: var(--font-mono);
  font-size: 12px;
}

/* Bibliography List */
.bib-list {
  display: flex;
  flex-direction: column;
  gap: 12px;
}
.bib-card {
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 18px 22px;
}
.bib-card:target, .bib-card.highlight-target {
  border-color: var(--brand);
  box-shadow: 0 0 0 3px var(--brand-soft);
}
.bib-meta-top {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 8px;
  margin-bottom: 6px;
}
.bib-key {
  font-family: var(--font-mono);
  font-size: 12.5px;
  font-weight: 700;
  color: var(--plum);
  background: var(--plum-soft);
  padding: 2px 8px;
  border-radius: 5px;
}
.bib-chapter { font-size: 12px; color: var(--fg-faint); }
.bib-title { margin: 0 0 4px; font-size: 16.5px; font-weight: 600; color: var(--fg); }
.bib-authors { margin: 0 0 4px; font-size: 14px; color: var(--fg-muted); }
.bib-venue { margin: 0 0 10px; font-size: 13.5px; color: var(--fg-faint); font-style: italic; }
.bib-links {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 8px;
  font-size: 12.5px;
}
.bib-ext-badge {
  padding: 2px 9px;
  border-radius: 5px;
  border: 1px solid var(--border-strong);
  background: var(--bg-subtle);
  font-weight: 600;
}
.bib-raw-details summary {
  cursor: pointer;
  color: var(--fg-muted);
  font-weight: 600;
}

/* Footer */
.site-footer {
  border-top: 1px solid var(--border);
  background: var(--bg-elevated);
  padding: 40px 24px;
  font-size: 13.5px;
  color: var(--fg-muted);
}
.footer-inner {
  max-width: 1160px;
  margin: 0 auto;
  display: grid;
  grid-template-columns: minmax(200px, 1fr) minmax(0, 2.6fr);
  gap: 32px 52px;
}
.footer-about h2, .footer-group h2 {
  margin: 0 0 10px;
  color: var(--fg);
  font-size: 14px;
  line-height: 1.45;
}
.footer-about h2 { font-size: 18px; }
.footer-about a { color: var(--brand); }
.footer-about p { margin: 0; }
.footer-about p + p { margin-top: 4px; }
.footer-nav {
  display: grid;
  grid-template-columns: minmax(0, 1fr) minmax(0, 1.15fr) minmax(0, 1.45fr);
  gap: 24px 20px;
}
.footer-group ul {
  display: grid;
  gap: 6px;
  margin: 0;
  padding: 0;
  list-style: none;
}
.footer-nav a {
  color: var(--fg-muted);
  overflow-wrap: anywhere;
}

.back-to-top {
  position: fixed;
  right: 24px;
  bottom: 24px;
  z-index: 90;
  width: 38px;
  height: 38px;
  border-radius: 999px;
  border: 1px solid var(--border-strong);
  background: var(--bg-elevated);
  color: var(--brand);
  box-shadow: var(--shadow-md);
  display: inline-flex;
  align-items: center;
  justify-content: center;
  font-size: 16px;
  font-weight: 700;
  cursor: pointer;
  opacity: 0;
  pointer-events: none;
  transform: translateY(8px);
  transition: opacity 0.18s ease, transform 0.18s ease, border-color 0.15s ease;
}
.back-to-top.visible {
  opacity: 1;
  pointer-events: auto;
  transform: translateY(0);
}
.back-to-top:hover {
  border-color: var(--brand);
  background: var(--bg-subtle);
}

/* Unified Catalog / Paper / Declaration panel */
.panel-kpi-section { padding-top: 28px; }
.panel-table-wrap { overflow-x: auto; }
.panel-table {
  width: 100%;
  border-collapse: collapse;
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  overflow: hidden;
  font-size: 13px;
}
.panel-table th, .panel-table td {
  padding: 9px 11px;
  border-bottom: 1px solid var(--border);
  text-align: right;
  white-space: nowrap;
}
.panel-table th:first-child, .panel-table td:first-child { text-align: left; }
.panel-table thead th { background: var(--bg-subtle); color: var(--fg-muted); }
.panel-table tbody tr:last-child th, .panel-table tbody tr:last-child td { border-bottom: none; }
.panel-card {
  background: var(--bg-elevated);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 18px 20px;
  box-shadow: var(--shadow-sm);
}
.panel-card + .panel-card { margin-top: 14px; }
.panel-card h2, .panel-card h3 { margin: 0 0 8px; }
.panel-card h2 { font-size: 19px; }
.panel-card h3 { font-size: 16px; }
.panel-meta, .panel-muted { color: var(--fg-muted); font-size: 13px; }
.panel-meta { display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; }
.panel-badge {
  display: inline-flex;
  align-items: center;
  padding: 2px 7px;
  border-radius: 999px;
  border: 1px solid var(--border);
  background: var(--bg-subtle);
  color: var(--fg-muted);
  font-size: 11px;
  line-height: 1.35;
  white-space: nowrap;
}
.panel-badge-rank { color: var(--brand); border-color: var(--brand); background: var(--brand-soft); }
.panel-badge-status { color: var(--teal); border-color: var(--teal); background: var(--teal-soft); }
.panel-badge-full { color: #2f7a56; border-color: #65b48b; background: #e3f5eb; }
.panel-badge-partial { color: var(--plum); border-color: #c49bcf; background: var(--plum-soft); }
[data-theme="dark"] .panel-badge-full { color: #91ddb1; background: rgba(71, 170, 111, .18); }
.panel-links { display: flex; flex-wrap: wrap; gap: 7px; margin-top: 9px; }
.panel-links a {
  font-family: var(--font-mono);
  font-size: 11.5px;
  padding: 3px 8px;
  border-radius: 5px;
  border: 1px solid var(--border);
  background: var(--bg-subtle);
}
.panel-detail-wrap { max-width: 1280px; margin: 0 auto; padding: 36px 24px 72px; }
.panel-detail-header { margin-bottom: 22px; }
.panel-detail-header h1 { margin: 0 0 8px; font-size: 30px; }
.panel-detail-header p { margin: 0; color: var(--fg-muted); max-width: 900px; }
.panel-grid { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 14px; }
.panel-decl-table { width: 100%; border-collapse: collapse; font-size: 12.5px; margin-top: 12px; }
.panel-decl-table th, .panel-decl-table td { border: 1px solid var(--border); padding: 7px 8px; vertical-align: top; text-align: left; }
.panel-decl-table th { background: var(--bg-subtle); color: var(--fg-muted); white-space: nowrap; }
.panel-decl-table code { font-size: 11.5px; word-break: break-word; }
.panel-coverage-table { overflow-wrap: anywhere; }
.panel-coverage-table th { white-space: normal; }
.panel-coverage-table th:first-child, .panel-coverage-table :is(th, td):nth-child(2) {
  width: 1%; white-space: nowrap;
}
.panel-coverage-table :is(th, td):nth-child(2) { text-align: center; font-weight: 600; }
.panel-module-card { border-top: 1px solid var(--border); padding-top: 12px; margin-top: 12px; }
.panel-module-card:first-child { border-top: none; padding-top: 0; margin-top: 0; }
.panel-module-head { display:flex; justify-content:space-between; gap:10px; align-items:baseline; flex-wrap:wrap; }
.panel-module-head strong { font-family: var(--font-mono); font-size: 13px; }
.panel-claim { border-left: 3px solid var(--brand); padding-left: 12px; }
.panel-claim + .panel-claim { margin-top: 16px; }
.panel-claim p { margin: 6px 0; color: var(--fg-muted); white-space: pre-line; }
.panel-empty { color: var(--fg-faint); font-style: italic; }

/* UI labels use the text family; keep numeric columns aligned. */
.section-eyebrow, .layer-badge, .mod-layer-tag, .mod-count {
  font-family: var(--font-sans);
  font-variant-numeric: tabular-nums;
}

/* :lang() also matches inherited zh-Hans and locally marked bilingual text. */
body:lang(zh) {
  --prose-leading: 1.75;
  line-height: 1.75;
  text-spacing-trim: space-first;
  font-kerning: normal;
}
.hero h1:lang(zh), .prose-header h1:lang(zh),
.panel-detail-header h1:lang(zh), .explorer-wrap h1:lang(zh) {
  letter-spacing: 0;
  line-height: 1.36;
  font-weight: 600;
}
.section-header h2:lang(zh), .prose h2:lang(zh) {
  letter-spacing: 0;
  line-height: 1.42;
  font-weight: 600;
}
.area-card h3:lang(zh), .layer-card h3:lang(zh), .prose h3:lang(zh) {
  line-height: 1.45;
  font-weight: 600;
}
.section-eyebrow:lang(zh), .sidebar-group-title:lang(zh) {
  font-family: var(--font-sans);
  letter-spacing: 0.04em;
  text-transform: none;
  font-weight: 600;
}
.panel-empty:lang(zh), em:lang(zh), cite:lang(zh) { font-style: normal; }
.filter-pill:lang(zh), .bib-ext-badge:lang(zh), .mod-actions:lang(zh) {
  font-weight: 500;
}
.prose :not(pre) > code:lang(zh) { margin-inline: 0.14em; }

@media (max-width: 760px) {
  .panel-grid { grid-template-columns: 1fr; }
  .panel-detail-wrap { padding: 22px 16px 48px; }
  .panel-table { font-size: 12px; }
}

@media (max-width: 1024px) {
  .hero-inner { grid-template-columns: 1fr; }
  .footer-inner { grid-template-columns: 1fr; }
  .metrics-strip { grid-template-columns: repeat(3, 1fr); }
  .layers-grid { grid-template-columns: 1fr; }
  .docs-shell { grid-template-columns: 200px minmax(0, 1fr); }
  .docs-toc { display: none; }
}

@media (max-width: 1570px) {
  .mobile-menu-btn { display: inline-flex; }
  .nav-links {
    display: none;
    position: absolute;
    top: 100%;
    left: 0;
    right: 0;
    flex-direction: column;
    align-items: stretch;
    padding: 12px 20px 16px;
    background: var(--bg-elevated);
    border-bottom: 1px solid var(--border);
    box-shadow: var(--shadow-md);
  }
  .nav-links.open { display: flex; }
}

@media (max-width: 1024px) {
  .nav-links { padding-top: 60px; }
  .nav-search-form {
    display: none;
    position: absolute;
    top: calc(100% + 12px);
    left: 20px;
    right: 20px;
    z-index: 1;
  }
  .nav-links.open + .nav-actions .nav-search-form { display: flex; }
  .nav-search-input, .nav-search-input:focus { width: 100%; }
}

@media (max-width: 480px) {
  .nav-inner { padding: 8px 12px; gap: 8px; }
  .nav-actions { gap: 5px; }
  .nav-actions .icon-btn { padding-inline: 7px; }
  .nav-brand { flex-direction: column; align-items: flex-start; gap: 2px; }
  .nav-wordmark { width: 96px; }
  .toolchain-pill { font-size: 10px; padding: 2px 6px; }
  .hero-ctas { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .hero-ctas .btn-primary { grid-column: 1 / -1; }
  .site-footer { padding-block: 32px; }
  .footer-nav { grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .footer-group:last-child { grid-column: 1 / -1; }
}

@media (max-width: 760px) {
  .areas-grid, .mod-grid { grid-template-columns: 1fr; }
  .metrics-strip { grid-template-columns: repeat(2, 1fr); }
  .docs-shell { grid-template-columns: 1fr; padding: 20px 16px 48px; }
  .docs-sidebar { position: static; }
  .prose { padding: 24px 20px; }
}
"""

SITE_JS = """(() => {
  // Theme initialization & toggle
  const root = document.documentElement;
  const savedTheme = localStorage.getItem("qatlib-theme");
  if (savedTheme === "dark" || savedTheme === "light") {
    root.setAttribute("data-theme", savedTheme);
  } else if (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches) {
    root.setAttribute("data-theme", "dark");
  }

  const themeBtn = document.getElementById("theme-toggle");
  const syncThemeIcon = () => {
    if (!themeBtn) return;
    const isDark = root.getAttribute("data-theme") === "dark";
    themeBtn.textContent = isDark ? "☀" : "☾";
    themeBtn.title = isDark ? themeBtn.dataset.lightTitle : themeBtn.dataset.darkTitle;
    themeBtn.setAttribute("aria-pressed", String(isDark));
  };
  syncThemeIcon();
  if (themeBtn) {
    themeBtn.addEventListener("click", () => {
      const next = root.getAttribute("data-theme") === "dark" ? "light" : "dark";
      root.setAttribute("data-theme", next);
      localStorage.setItem("qatlib-theme", next);
      syncThemeIcon();
    });
  }

  // Mobile navigation drawer
  const menuBtn = document.getElementById("mobile-menu-btn");
  const navLinks = document.getElementById("nav-links");
  const setMenuOpen = (open) => {
    if (!menuBtn || !navLinks) return;
    navLinks.classList.toggle("open", open);
    menuBtn.setAttribute("aria-expanded", String(open));
  };
  if (menuBtn && navLinks) {
    menuBtn.addEventListener("click", () => setMenuOpen(!navLinks.classList.contains("open")));
    navLinks.addEventListener("click", (e) => {
      if (e.target.closest("a")) setMenuOpen(false);
    });
  }

  // '/' shortcut focuses search box
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && navLinks?.classList.contains("open")) {
      setMenuOpen(false);
      menuBtn.focus();
    }
    if (e.key === "/" && !["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement?.tagName || "")) {
      const target = document.getElementById("explorer-search") || document.querySelector(".nav-search-input");
      if (target) {
        e.preventDefault();
        if (target.matches(".nav-search-input") && !target.getClientRects().length) setMenuOpen(true);
        target.focus();
      }
    }
  });

  // Quickstart tabs
  document.querySelectorAll(".qs-tabs").forEach((group) => {
    const tabs = [...group.querySelectorAll(".qs-tab")];
    const selectTab = (active) => {
      tabs.forEach((tab, index) => {
        const selected = index === active;
        tab.classList.toggle("active", selected);
        tab.setAttribute("aria-selected", String(selected));
        tab.tabIndex = selected ? 0 : -1;
        const panel = document.getElementById(tab.getAttribute("aria-controls"));
        panel.hidden = !selected;
        panel.classList.toggle("active", selected);
      });
      tabs[active].focus();
    };
    tabs.forEach((tab, index) => {
      tab.addEventListener("click", () => selectTab(index));
      tab.addEventListener("keydown", (event) => {
        const last = tabs.length - 1;
        const keys = { ArrowLeft: (index + last) % tabs.length, ArrowRight: (index + 1) % tabs.length,
          Home: 0, End: last };
        if (!Object.hasOwn(keys, event.key)) return;
        event.preventDefault();
        selectTab(keys[event.key]);
      });
    });
  });

  // Copy buttons on code cards
  document.querySelectorAll(".copy-btn").forEach((btn) => {
    btn.addEventListener("click", async () => {
      const card = btn.closest(".code-card");
      const code = card ? card.querySelector("pre code") : null;
      if (!code) return;
      try {
        await navigator.clipboard.writeText(code.innerText);
        const orig = btn.getAttribute("data-copy-label") || "Copy";
        btn.textContent = "✓";
        setTimeout(() => { btn.textContent = orig; }, 1400);
      } catch (_) {}
    });
  });

  // Module Explorer filtering & deep-link highlighting
  const modGrid = document.getElementById("module-explorer-grid");
  if (modGrid) {
    const searchInput = document.getElementById("explorer-search");
    const statusEl = document.getElementById("explorer-status");
    const pills = Array.from(document.querySelectorAll("[data-layer-filter]"));
    const cards = Array.from(modGrid.querySelectorAll(".mod-card"));
    let activeLayer = "all";

    const params = new URLSearchParams(window.location.hash.slice(1) || window.location.search);
    const qLayer = params.get("layer");
    if (qLayer && ["Foundations", "Concepts", "Papers"].includes(qLayer)) {
      activeLayer = qLayer;
    }

    const applyModFilter = () => {
      const q = (searchInput?.value || "").trim().toLowerCase();
      let shown = 0;
      cards.forEach((c) => {
        const layerOk = activeLayer === "all" || c.dataset.layer === activeLayer;
        const textOk = !q || (c.dataset.search || "").includes(q);
        const vis = layerOk && textOk;
        c.style.display = vis ? "" : "none";
        if (vis) shown++;
      });
      pills.forEach((p) => p.classList.toggle("active", p.dataset.layerFilter === activeLayer));
      if (statusEl) {
        const tpl = statusEl.dataset.template || "{shown} / {total}";
        statusEl.textContent = tpl.replace("{shown}", String(shown)).replace("{total}", String(cards.length));
      }
    };

    pills.forEach((p) => {
      p.addEventListener("click", () => {
        activeLayer = p.dataset.layerFilter || "all";
        applyModFilter();
      });
    });
    if (searchInput) {
      searchInput.addEventListener("input", applyModFilter);
    }

    const focusHashCard = () => {
      const rawHash = decodeURIComponent(window.location.hash.replace(/^#/, ""));
      const layer = /^layer=(Foundations|Concepts|Papers)$/.exec(rawHash)?.[1];
      if (layer) {
        activeLayer = layer;
        applyModFilter();
        return;
      }
      if (!rawHash) return;
      const target = document.getElementById(rawHash);
      if (target && target.classList.contains("mod-card")) {
        activeLayer = "all";
        if (searchInput) searchInput.value = "";
        applyModFilter();
        cards.forEach((c) => c.classList.remove("highlight-target"));
        target.classList.add("highlight-target");
        const det = target.querySelector("details");
        if (det) det.open = true;
        target.scrollIntoView({ behavior: "smooth", block: "center" });
      }
    };
    applyModFilter();
    focusHashCard();
    window.addEventListener("hashchange", focusHashCard);
  }

  // Bibliography Explorer filtering
  const bibList = document.getElementById("bib-explorer-list");
  if (bibList) {
    const searchInput = document.getElementById("explorer-search");
    const chapterSelect = document.getElementById("chapter-filter");
    const onlyFormalized = document.getElementById("formalized-only");
    const statusEl = document.getElementById("explorer-status");
    const cards = Array.from(bibList.querySelectorAll(".bib-card"));

    const applyBibFilter = () => {
      const q = (searchInput?.value || "").trim().toLowerCase();
      const sec = chapterSelect?.value || "all";
      const reqForm = Boolean(onlyFormalized?.checked);
      let shown = 0;
      cards.forEach((c) => {
        const secOk = sec === "all" || c.dataset.section === sec;
        const formOk = !reqForm || c.dataset.formalized === "1";
        const textOk = !q || (c.dataset.search || "").includes(q);
        const vis = secOk && formOk && textOk;
        c.style.display = vis ? "" : "none";
        if (vis) shown++;
      });
      if (statusEl) {
        const tpl = statusEl.dataset.template || "{shown} / {total}";
        statusEl.textContent = tpl.replace("{shown}", String(shown)).replace("{total}", String(cards.length));
      }
    };
    if (searchInput) searchInput.addEventListener("input", applyBibFilter);
    if (chapterSelect) chapterSelect.addEventListener("change", applyBibFilter);
    if (onlyFormalized) onlyFormalized.addEventListener("change", applyBibFilter);
    applyBibFilter();
  }

  // Nav search form submission via JS navigation (compatible with strict CSP form-action 'none')
  document.querySelectorAll(".nav-search-form").forEach((form) => {
    form.addEventListener("submit", (e) => {
      e.preventDefault();
      const input = form.querySelector("input[name='q']");
      const q = (input?.value || "").trim();
      const target = form.getAttribute("action") || "./docs/search.html";
      window.location.href = q ? `${target}#q=${encodeURIComponent(q)}` : target;
    });
  });

  // Back-to-top floating button
  const topBtn = document.getElementById("back-to-top");
  if (topBtn) {
    const syncTopBtn = () => {
      topBtn.classList.toggle("visible", window.scrollY > 480);
    };
    window.addEventListener("scroll", syncTopBtn, { passive: true });
    syncTopBtn();
    topBtn.addEventListener("click", () => {
      window.scrollTo({ top: 0, behavior: "smooth" });
    });
  }

  // 404 legacy root doc-gen4 URL auto-redirector
  if (document.getElementById("redirect-msg")) {
    const p = window.location.pathname;
    const legacy = /\\/(qatlib\\/)?(Qatlib|Mathlib|Physlib|Init|Std|Lean|Batteries|Aesop|Qq)(\\/|\\.html)|\\/(qatlib\\/)?(search|references|tactics|foundational_types)\\.html/;
    if (legacy.test(p) && !p.includes("/docs/")) {
      const idx = p.indexOf("/qatlib/");
      const next = idx >= 0
        ? p.slice(0, idx + 8) + "docs/" + p.slice(idx + 8)
        : "/docs" + p;
      window.location.replace(next + window.location.search + window.location.hash);
    }
  }
})();
"""

THEME_INIT_JS = """\
(() => {
  try {
    const s = localStorage.getItem("qatlib-theme");
    if (s === "dark" || (!s && window.matchMedia("(prefers-color-scheme: dark)").matches)) {
      document.documentElement.setAttribute("data-theme", "dark");
    }
  } catch (_) {}
})();
"""


# ---------------------------------------------------------------------------
# HTML Shell & Page Builders
# ---------------------------------------------------------------------------

def language_link(locale: str, href: str, *, current: bool = False, label: str | None = None) -> str:
    info = LOCALES[locale]
    selected = ' aria-current="page"' if current else ""
    check = '<span aria-hidden="true">✓</span>' if current else ""
    return (
        f'<a href="{href}" lang="{info["tag"]}" hreflang="{info["tag"]}"{selected}>'
        f'{label or info["name"]}{check}</a>'
    )


def language_switcher(lang: str, page_slug: str) -> str:
    current_page = LOCALES[lang]["prefix"] + page_slug
    options = "".join(
        language_link(locale, relative_url(current_page, url_for(locale, page_slug)),
                      current=locale == lang, label="简体中文" if locale == "zh" else None)
        for locale in LOCALES
    )
    current = LOCALES[lang]
    label = html.escape(strings_for(lang)["ui"]["language_label"].format(name=current["name"]))
    preserve = ' data-preserve-hash' if page_slug == DEPENDENCY_GRAPH_PAGE else ""
    return f'''<details class="lang-switcher"{preserve}>
  <summary class="icon-btn" aria-label="{label}">
    <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" aria-hidden="true">
      <circle cx="12" cy="12" r="9"/><ellipse cx="12" cy="12" rx="4" ry="9"/><path d="M3 12h18"/>
    </svg>
    <span lang="{current["tag"]}">{current["name"]}</span><span aria-hidden="true">▾</span>
  </summary>
  <div class="lang-options">{options}</div>
</details>'''


def locale_metadata(lang: str, page: str, site_url: str, title: str, description: str) -> str:
    canonical = site_url + url_for(lang, page)
    alternate = [
        f'<link rel="alternate" hreflang="{info["tag"]}" href="{html.escape(site_url + url_for(key, page))}">'
        for key, info in LOCALES.items()
    ]
    other = next(info["og"] for key, info in LOCALES.items() if key != lang)
    image = site_url + "assets/" + SOCIAL_IMAGE
    sharing = {
        "og:type": "website", "og:site_name": "Qatlib", "og:title": title,
        "og:description": description, "og:url": canonical, "og:image": image,
        "og:image:width": "1280", "og:image:height": "640",
        "og:locale": LOCALES[lang]["og"], "og:locale:alternate": other,
    }
    twitter = {"twitter:card": "summary_large_image", "twitter:title": title,
               "twitter:description": description, "twitter:image": image}
    return "\n  ".join([
        f'<link rel="canonical" href="{html.escape(canonical)}">',
        *alternate,
        f'<link rel="alternate" hreflang="x-default" href="{html.escape(site_url)}">',
        f'<meta name="description" content="{html.escape(description)}">',
        *(f'<meta property="{key}" content="{html.escape(value)}">' for key, value in sharing.items()),
        *(f'<meta name="{key}" content="{html.escape(value)}">' for key, value in twitter.items()),
    ])


def build_dependency_graph_body(lang: str, root_prefix: str, wordmark: str) -> tuple[str, str]:
    """Render the full-viewport graph and its bilingual controls."""
    t = strings_for(lang)["graph"]
    title, labels, toolbar = t["title"], t["labels"], t["toolbar"]
    tabs = "".join(
        f'<button type="button" class="dg-tab" role="tab" data-layer="{i}" data-key="{key}" '
        f'id="dg-tab-{i}" aria-controls="dg-controls" aria-selected="false" tabindex="-1">{label}</button>'
        for i, (key, label) in enumerate(zip(PANEL_LAYERS, labels, strict=True))
    )
    legend = "".join(f'<span data-layer="{i}">{label}</span>' for i, label in enumerate(labels))
    buttons = "".join(
        f'<button type="button" class="dg-icon" id="dg-{key}" aria-label="{label}" title="{label}">{symbol}</button>'
        for (key, symbol), label in zip(
            (("zoom-in", "+"), ("zoom-out", "−"), ("fit", "◎"), ("home", "↺"), ("fullscreen", "⛶")),
            toolbar, strict=True,
        )
    )
    runtime = html.escape(json.dumps(t["strings"], ensure_ascii=False))
    return title, f'''<main class="dg" data-strings="{runtime}" data-src="{root_prefix}docs/{DEPENDENCY_GRAPH_ASSET}" data-api="{root_prefix}docs/">
  <header class="dg-mast">
    <a href="./" class="dg-brand" aria-label="{strings_for(lang)["ui"]["brand_home_label"]}">{wordmark}</a>
    <h1>{title}</h1>
    {language_switcher(lang, DEPENDENCY_GRAPH_PAGE)}
  </header>
  <canvas class="dg-sky" id="dg-sky" tabindex="0" aria-label="{html.escape(t["canvas_name"])}" aria-describedby="dg-hint"></canvas>
  <p id="dg-status" class="dg-status" role="status">{html.escape(t["loading"])}</p>
  <div id="dg-layout" class="dg-layout" hidden>
    <div class="dg-tray">
      <div class="dg-view" role="group" aria-label="{html.escape(t["mode_label"])}">
        <button id="dg-2d" type="button" aria-label="{html.escape(t["view2d"])}" title="{html.escape(t["view2d"])}" aria-pressed="true">2D</button>
        <button id="dg-3d" type="button" aria-label="{html.escape(t["view3d"])}" title="{html.escape(t["view3d"])}" aria-pressed="false">3D</button>
      </div>
      <button class="dg-control" id="dg-browse" type="button" aria-controls="dg-sidebar" aria-expanded="false">{html.escape(t["browse"])}</button>
      <button class="dg-control" id="dg-inspect" type="button" aria-controls="dg-detail" aria-expanded="false" hidden>{html.escape(t["inspect"])}</button>
    </div>
    <aside class="dg-panel dg-sidebar" id="dg-sidebar" aria-label="{html.escape(t["browse"])}" hidden>
      <div class="dg-field">
        <label for="dg-search">{html.escape(t["search"])}</label>
        <input type="search" id="dg-search" autocomplete="off" aria-controls="dg-results">
        <div id="dg-results" class="dg-results" aria-live="polite" hidden></div>
      </div>
      <div class="dg-tabs" role="tablist" aria-label="{html.escape(t["layers"])}">{tabs}</div>
      <div id="dg-controls" role="tabpanel">
        <div class="dg-field">
          <label for="dg-filter">{html.escape(t["filter_label"])}</label>
          <input type="search" id="dg-filter" autocomplete="off" aria-controls="dg-list">
        </div>
        <div id="dg-list" class="dg-list"></div>
      </div>
    </aside>
    <aside id="dg-detail" class="dg-panel dg-detail" aria-labelledby="dg-selection-title" hidden></aside>
    <div class="dg-toolbar" role="group" aria-label="{html.escape(t["toolbar_label"])}">{buttons}</div>
    <footer class="dg-hud">
      <div class="dg-legend">{legend}</div>
      <p id="dg-totals"></p>
    </footer>
    <p class="dg-hint" id="dg-hint">{html.escape(t["strings"]["hint2d"])}</p>
    <div class="dg-tooltip" id="dg-tooltip" role="tooltip" hidden></div>
  </div>
  <script type="module" src="{root_prefix}assets/{DEPENDENCY_GRAPH_SCRIPT}"></script>
</main>'''


def render_page_shell(
    *,
    title: str,
    lang: str,
    page_slug: str,
    root_prefix: str,
    toolchain_tag: str,
    wordmark_nav: str,
    body_html: str,
    site_url: str = DEFAULT_SITE_URL,
) -> str:
    t = strings_for(lang)["ui"]
    tag = LOCALES[lang]["tag"]
    i18n_script = f'<script type="module" src="{root_prefix}assets/i18n.js"></script>'
    page_prefix = root_prefix + url_for(lang)
    docs_prefix = f"{root_prefix}docs/"

    def nav_cls(slug: str) -> str:
        return ' class="active" aria-current="page"' if slug == page_slug else ""

    full_title = f"{title} — Qatlib" if title != "Qatlib" else f"Qatlib · {t['site_tagline']}"
    descriptions = strings_for(lang)["descriptions"]
    if page_slug == DEPENDENCY_GRAPH_PAGE:
        description = strings_for(lang)["graph"]["description"]
    else:
        template = descriptions.get(page_slug) or descriptions.get(page_slug.split("/")[0])
        description = template.format(title=title) if template else title
    metadata = locale_metadata(lang, page_slug, site_url, full_title, description)
    if page_slug == DEPENDENCY_GRAPH_PAGE:
        return f"""<!doctype html>
<html lang="{tag}" data-theme="dark">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(full_title)}</title>
  {metadata}
  {i18n_script}
  <link rel="stylesheet" href="{root_prefix}assets/style.css">
  <link rel="stylesheet" href="{root_prefix}assets/{DEPENDENCY_GRAPH_STYLES}">
{render_favicon_links(root_prefix)}
</head>
<body class="dependency-page">{body_html}</body>
</html>
"""
    switcher = language_switcher(lang, page_slug)
    if page_slug == "index.html":
        body_html = f"<main>{body_html}</main>"
    body_html = body_html.replace("<main", '<main id="main-content" tabindex="-1"', 1)
    nav_items = "\n        ".join(
        f'<a href="{root_prefix}{url_for(lang, slug)}"{nav_cls(slug)}>{t[key]}</a>'
        for slug, key in NAV_PAGES.items()
    )
    return f"""<!DOCTYPE html>
<html lang="{tag}">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(full_title)}</title>
  {metadata}
  <link rel="stylesheet" href="{root_prefix}assets/style.css">
  <script src="{root_prefix}assets/theme-init.js"></script>
  {i18n_script}
{render_favicon_links(root_prefix)}
</head>
<body>
  <a class="skip-link" href="#main-content">{t["skip_to_content"]}</a>
  <header class="site-header">
    <div class="nav-inner">
      <div class="nav-brand">
        <a class="brand-link" href="{page_prefix}" aria-label="{t['brand_home_label']}">
          {wordmark_nav}
        </a>
        <span class="toolchain-pill">Lean {html.escape(toolchain_tag)}</span>
      </div>

      <nav id="nav-links" class="nav-links" aria-label="{t['primary_nav']}">
        {nav_items}
        <a href="{docs_prefix}index.html" class="nav-api-btn">{t["nav_api"]}</a>
      </nav>

      <div class="nav-actions">
        <form class="nav-search-form" action="{docs_prefix}search.html" method="get">
          <input class="nav-search-input" type="search" name="q" placeholder="{t['search_placeholder']}" aria-label="{t['search_placeholder']}" autocomplete="off">
          <span class="nav-search-kbd" aria-hidden="true">/</span>
        </form>
        {switcher}
        <button id="theme-toggle" class="icon-btn" type="button" aria-label="{t['theme_toggle_label']}" data-light-title="{t['theme_light']}" data-dark-title="{t['theme_dark']}">☾</button>
        <a class="icon-btn" href="{GITHUB_REPO_URL}" target="_blank" rel="noopener" title="{t['github_title']}" aria-label="GitHub">
          <svg width="17" height="17" viewBox="0 0 16 16" fill="currentColor" aria-hidden="true">
            <path d="M8 0C3.58 0 0 3.58 0 8a8 8 0 0 0 5.47 7.59c.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82a7.65 7.65 0 0 1 4 0c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0 0 16 8c0-4.42-3.58-8-8-8Z"/>
          </svg>
        </a>
        <button id="mobile-menu-btn" class="icon-btn mobile-menu-btn" type="button" aria-label="{t['menu_label']}" aria-controls="nav-links" aria-expanded="false">☰</button>
      </div>
    </div>
  </header>

  {body_html}

  <footer class="site-footer">
    <div class="footer-inner">
      <div class="footer-about">
        <h2><a href="{page_prefix}">Qatlib</a></h2>
        <p>{t["footer_note"]}</p>
        <p>{t["footer_license"]}</p>
      </div>
      <nav class="footer-nav" aria-label="{t['footer_nav']}">
        <div class="footer-group">
          <h2>{t["footer_guides"]}</h2>
          <ul>
            <li><a href="{page_prefix}getting-started.html">{t["nav_getting_started"]}</a></li>
            <li><a href="{page_prefix}architecture.html">{t["nav_architecture"]}</a></li>
            <li><a href="{page_prefix}modules.html">{t["nav_modules"]}</a></li>
          </ul>
        </div>
        <div class="footer-group">
          <h2>{t["footer_research"]}</h2>
          <ul>
            <li><a href="{page_prefix}papers.html">{t["nav_papers"]}</a></li>
            <li><a href="{page_prefix}{DEPENDENCY_GRAPH_PAGE}">{t["nav_graph"]}</a></li>
            <li><a href="{docs_prefix}index.html">{t["footer_api"]}</a></li>
            <li><a href="{docs_prefix}references.html">{t["footer_refs"]}</a></li>
          </ul>
        </div>
        <div class="footer-group">
          <h2>{t["footer_project"]}</h2>
          <ul>
            <li><a href="{GITHUB_REPO_URL}" target="_blank" rel="noopener noreferrer">GitHub · {GITHUB_REPO_URL.removeprefix('https://github.com/')}</a></li>
            <li><a href="{page_prefix}changelog.html">{t["nav_changelog"]}</a></li>
            <li><a href="{page_prefix}contributing.html">{t["nav_contributing"]}</a></li>
          </ul>
        </div>
      </nav>
    </div>
  </footer>
  <button id="back-to-top" class="back-to-top" type="button" title="{t['back_to_top_label']}" aria-label="{t['back_to_top_label']}">↑</button>
  <script src="{root_prefix}assets/site.js" defer></script>
</body>
</html>
"""


def build_docs_layout(
    *,
    page_title: str,
    source_rel: str,
    lang: str,
    page_slug: str,
    root_prefix: str,
    prose_html: str,
    toc: list[dict[str, Any]],
) -> str:
    t = strings_for(lang)["ui"]
    docs_prefix = f"{root_prefix}docs/"
    sidebar = []
    for slug, key in NAV_PAGES.items():
        active = ' class="active"' if slug == page_slug else ""
        sidebar.append(f'<li><a href="{root_prefix}{url_for(lang, slug)}"{active}>{t[key]}</a></li>')
    sidebar_lis = "\n".join(sidebar)
    api_links = zip(
        ("index.html", "Qatlib.html", "references.html", "tactics.html"),
        t["api_links"], strict=True,
    )
    api_lis = "\n".join(f'<li><a href="{docs_prefix}{href}">{label}</a></li>' for href, label in api_links)

    toc_lis = "\n".join(
        f'<li class="toc-h{item["level"]}"><a href="#{item["id"]}">{html.escape(item["text"])}</a></li>'
        for item in toc
    )
    toc_aside = (
        f'<aside class="docs-toc" aria-label="{t["toc_heading"]}">'
        f'<p class="sidebar-group-title">{t["toc_heading"]}</p>'
        f'<ul class="toc-list">{toc_lis}</ul></aside>'
        if toc_lis
        else '<aside class="docs-toc"></aside>'
    )

    return f"""
  <div class="docs-shell">
    <aside class="docs-sidebar" aria-label="{t['guides_heading']}">
      <p class="sidebar-group-title">{t["guides_heading"]}</p>
      <ul class="sidebar-nav">{sidebar_lis}</ul>
      <p class="sidebar-group-title">{t["api_group_heading"]}</p>
      <ul class="sidebar-nav">{api_lis}</ul>
    </aside>

    <main class="prose">
      <div class="prose-header">
        <h1>{html.escape(page_title)}</h1>
        <a class="prose-source-link" href="{GITHUB_REPO_URL}/blob/main/{source_rel}" target="_blank" rel="noopener">{t["edit_on_github"]} ({source_rel})</a>
      </div>
      {prose_html}
    </main>

    {toc_aside}
  </div>
"""


def build_home_body(
    *,
    lang: str,
    root_prefix: str,
    toolchain_tag: str,
    wordmark_hero: str,
    tree_stats: dict[str, Any],
    bib_count: int,
    areas: list[dict[str, Any]],
    bibtex_str: str,
    qec_html: str,
) -> str:
    page_prefix = root_prefix + url_for(lang)
    docs_prefix = f"{root_prefix}docs/"
    layers = tree_stats["layers"]
    total_mods = f"{tree_stats['total_modules']:,}"
    p_dirs = f"{layers['Papers']['dir_count']:,}"
    copy_lbl = strings_for(lang)["ui"]["copy"]

    dep_toml = html.escape(
        '[[require]]\nname = "Qatlib"\n'
        'git = "https://github.com/quantum-atlas-ai/qatlib.git"\nrev = "main"'
    )
    dep_sh = "lake update\nlake exe get_cache"
    clone_sh = (
        "git clone https://github.com/quantum-atlas-ai/qatlib.git\n"
        "cd qatlib\n"
        "lake exe get_cache\n"
        "lake build Qatlib.Papers.GroverSearch96.MainResults.GainConvergence"
    )

    t = strings_for(lang)["home"]
    cta_papers = t["cta_papers"].format(count=bib_count)
    cap1 = t["cap1"].format(toolchain=toolchain_tag)
    metrics = zip((total_mods, p_dirs, f"{bib_count:,}", "0", toolchain_tag), t["metrics"], strict=True)
    layer_cards = []
    for layer in PANEL_LAYERS:
        card = t["layer_cards"][layer.lower()]
        counts = layers[layer]
        layer_cards.append((
            layer.lower(), f"Qatlib/{layer}",
            card["count"].format(dirs=counts["dir_count"], modules=f"{counts['module_count']:,}"),
            card["title"], card["description"], f"{page_prefix}modules.html#layer={layer}", card["link"],
        ))

    metrics_html = "\n".join(
        f'<div class="metric-item"><span class="metric-val">{val}</span>'
        f'<span class="metric-label">{lbl}</span></div>'
        for val, lbl in metrics
    )

    layers_html = "\n".join(
        f'<div class="layer-card layer-{cls}">'
        f'<div class="layer-badge"><span>{path_lbl}</span><span>{cnt_lbl}</span></div>'
        f"<h3>{html.escape(title_lbl)}</h3>"
        f"<p>{html.escape(desc_lbl)}</p>"
        f'<div class="layer-card-footer"><a href="{href}">{cta_lbl}</a>'
        f'<a href="{docs_prefix}{path_lbl}/index.html">API ↗</a></div></div>'
        for cls, path_lbl, cnt_lbl, title_lbl, desc_lbl, href, cta_lbl in layer_cards
    )

    area_cards_html = []
    for area in areas:
        chips = "\n".join(
            f'<a class="dir-chip" href="{page_prefix}modules.html#{d}">{html.escape(d.removeprefix("Qatlib/"))}</a>'
            for d in area["dirs"]
        )
        area_cards_html.append(
            f'<div class="area-card">'
            f'<div class="area-head"><span class="area-num">{html.escape(area["num"])}</span>'
            f'<h3>{html.escape(area["title"])}</h3></div>'
            f'<p class="area-topics">{html.escape(area["topics"])}</p>'
            f'<div class="chip-list">{chips}</div></div>'
        )
    qec_section = (
        '<section class="section" aria-labelledby="quantum-error-correction">'
        f'<div class="prose">{qec_html}</div></section>'
        if qec_html else ""
    )

    return f"""
  <section class="hero">
    <div class="hero-inner">
      <div>
        <div class="hero-eyebrow">✓ {html.escape(t["eyebrow"])}</div>
        {wordmark_hero}
        <h1>{html.escape(t["h1"])}</h1>
        <p class="hero-lead">{html.escape(t["lead"])}</p>
        <nav class="hero-ctas" aria-label="{html.escape(t['cta_nav'])}">
          <a class="btn btn-primary" href="{page_prefix}getting-started.html">{html.escape(t["cta_start"])} <span aria-hidden="true">→</span></a>
          <a class="btn btn-secondary" href="{page_prefix}{DEPENDENCY_GRAPH_PAGE}">{html.escape(t["cta_graph"])}</a>
          <a class="btn btn-secondary" href="{docs_prefix}index.html">{html.escape(t["cta_api"])}</a>
        </nav>
        <nav class="hero-resources" aria-label="{html.escape(t['resources_nav'])}">
          <a href="{page_prefix}modules.html">{html.escape(t["cta_mods"])}</a>
          <a href="{page_prefix}papers.html">{html.escape(cta_papers)}</a>
          <a href="{page_prefix}changelog.html">{html.escape(strings_for(lang)["ui"]["nav_changelog"])}</a>
        </nav>
      </div>

      <div class="quickstart-card">
        <div class="qs-tabs" role="tablist" aria-label="{html.escape(strings_for(lang)["ui"]["nav_getting_started"])}">
          <button type="button" class="qs-tab active" id="qs-dep-tab" role="tab" aria-selected="true" aria-controls="qs-dep">{html.escape(t["tab1"])}</button>
          <button type="button" class="qs-tab" id="qs-build-tab" role="tab" aria-selected="false" aria-controls="qs-build" tabindex="-1">{html.escape(t["tab2"])}</button>
        </div>
        <div id="qs-dep" class="qs-panel active" role="tabpanel" aria-labelledby="qs-dep-tab">
          <p class="qs-caption">{html.escape(cap1)}</p>
          <div class="code-card">
            <div class="code-card-header"><span class="code-lang">TOML · lakefile.toml</span>
              <button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>
            <pre><code>{dep_toml}</code></pre>
          </div>
          <div class="code-card" style="margin-bottom:0;">
            <div class="code-card-header"><span class="code-lang">BASH</span>
              <button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>
            <pre><code>{dep_sh}</code></pre>
          </div>
        </div>
        <div id="qs-build" class="qs-panel" role="tabpanel" aria-labelledby="qs-build-tab" hidden>
          <p class="qs-caption">{html.escape(t["cap2"])}</p>
          <div class="code-card" style="margin-bottom:0;">
            <div class="code-card-header"><span class="code-lang">BASH</span>
              <button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>
            <pre><code>{clone_sh}</code></pre>
          </div>
        </div>
      </div>
    </div>

    <div class="metrics-strip">
      {metrics_html}
    </div>
  </section>

  <section class="section">
    <div class="section-header">
      <div class="section-eyebrow">{html.escape(t["sec_arch_eye"])}</div>
      <h2>{html.escape(t["sec_arch_h2"])}</h2>
      <p>{html.escape(t["sec_arch_p"])}</p>
    </div>
    <div class="layers-grid">
      {layers_html}
    </div>
  </section>

  {build_catalog_kpi_panel(lang=lang, tree_stats=tree_stats)}

  {qec_section}

  <section class="section">
    <div class="section-header">
      <div class="section-eyebrow">{html.escape(t["sec_area_eye"])}</div>
      <h2>{html.escape(t["sec_area_h2"])}</h2>
      <p>{html.escape(t["sec_area_p"])}</p>
    </div>
    <div class="areas-grid">
      {"".join(area_cards_html)}
    </div>
  </section>

  <section class="section">
    <div class="section-header">
      <div class="section-eyebrow">{html.escape(t["sec_cite_eye"])}</div>
      <h2>{html.escape(t["sec_cite_h2"])}</h2>
      <p>{html.escape(t["sec_cite_p"])}</p>
    </div>
    <div class="code-card" style="max-width:780px;">
      <div class="code-card-header"><span class="code-lang">BIBTEX</span>
        <button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>
      <pre><code>{html.escape(bibtex_str)}</code></pre>
    </div>
  </section>
"""


def build_modules_explorer_body(
    *,
    lang: str,
    root_prefix: str,
    tree_stats: dict[str, Any],
) -> str:
    page_prefix = root_prefix + url_for(lang)
    docs_prefix = f"{root_prefix}docs/"
    layers = tree_stats["layers"]
    dirs = tree_stats["dirs"]
    catalog_units = {
        unit.get("path"): unit
        for unit in tree_stats.get("catalog", {}).get("units", [])
        if unit.get("path")
    }

    t = strings_for(lang)["modules"]
    lead = t["lead"].format(dirs=tree_stats["total_dirs"], modules=tree_stats["total_modules"])
    lbl_all = t["lbl_all"].format(count=tree_stats["total_dirs"])
    layer_display = t["layer_display"]
    layer_counts = {
        layer: t["layer_count"].format(layer=label, count=layers[layer]["dir_count"])
        for layer, label in layer_display.items()
    }
    status_tpl = t["status_tpl"]

    cards_html: list[str] = []
    for d in dirs:
        panel_unit = catalog_units.get(d["rel_dir"])
        panel_link = (
            f'<a href="{_unit_href(panel_unit["id"], lang, root_prefix)}">{t["unit_detail"]}</a>'
            if panel_unit
            else ""
        )
        layer_tag_lbl = layer_display.get(d["layer"], d["layer"])
        search_blob = " ".join(
            [d["rel_dir"], d["name"], layer_tag_lbl, d["title"], d["summary"], " ".join(d["citations"])]
        ).lower()
        cite_chips = "".join(
            f'<a class="dir-chip" href="{page_prefix}papers.html#{html.escape(ck)}">[{html.escape(ck)}]</a>'
            for ck in d["citations"][:4]
        )
        cite_row = f'<div class="chip-list">{cite_chips}</div>' if cite_chips else ""
        leaf_lis = "".join(
            f'<li><a href="{docs_prefix}{m["html_path"]}">{html.escape(m["label"])}</a></li>'
            for m in d["featured_mods"]
        )
        subtitle_el = f'<p class="mod-subtitle">{html.escape(d["title"])}</p>' if d["title"] else ""
        desc_el = f'<p class="mod-desc">{html.escape(d["summary"])}</p>' if d["summary"] else ""

        cards_html.append(
            f'<article id="{html.escape(d["rel_dir"])}" class="mod-card" '
            f'data-layer="{d["layer"]}" data-search="{html.escape(search_blob)}">'
            f'<div class="mod-card-top">'
            f'<span class="mod-layer-tag mod-layer-{d["layer"]}">{html.escape(layer_tag_lbl)}</span>'
            f'<span class="mod-count">{d["module_count"]} {t["mod_unit"]}</span>'
            f"</div>"
            f'<h2 class="mod-name">{html.escape(d["name"])}</h2>'
            f"{subtitle_el}{desc_el}{cite_row}"
            f'<details class="mod-details"><summary>{t["expand_lbl"]} ({len(d["featured_mods"])})</summary>'
            f'<ul class="mod-leaf-list">{leaf_lis}</ul></details>'
            f'<div class="mod-actions">'
            f"{panel_link}"
            f'<a href="{docs_prefix}{d["entry_html"]}">{t["api_lbl"]}</a>'
            f'<a href="{docs_prefix}{d["rel_dir"]}/index.html">{t["dir_api_lbl"]}</a>'
            f'<a href="{GITHUB_REPO_URL}/tree/main/{d["rel_dir"]}" target="_blank" rel="noopener">{t["gh_lbl"]}</a>'
            f"</div></article>"
        )

    return f"""
  <main class="explorer-wrap">
    <div class="section-header" style="margin-bottom:16px;">
      <div class="section-eyebrow">Qatlib/{'{'}Foundations, Concepts, Papers{'}'}</div>
      <h1 style="margin:0 0 8px;font-size:30px;">{html.escape(t["h1"])}</h1>
      <p>{html.escape(lead)}</p>
    </div>

    <div class="explorer-toolbar">
      <input id="explorer-search" class="filter-input" type="search" placeholder="{html.escape(t["placeholder"])}" autocomplete="off">
      <div class="filter-pills">
        <button type="button" class="filter-pill active" data-layer-filter="all">{html.escape(lbl_all)}</button>
        <button type="button" class="filter-pill" data-layer-filter="Foundations">{html.escape(layer_counts["Foundations"])}</button>
        <button type="button" class="filter-pill" data-layer-filter="Concepts">{html.escape(layer_counts["Concepts"])}</button>
        <button type="button" class="filter-pill" data-layer-filter="Papers">{html.escape(layer_counts["Papers"])}</button>
      </div>
    </div>

    <div id="explorer-status" class="results-status" data-template="{html.escape(status_tpl)}">
      {html.escape(status_tpl.format(shown=len(dirs), total=len(dirs)))}
    </div>

    <div id="module-explorer-grid" class="mod-grid">
      {"".join(cards_html)}
    </div>
  </main>
"""


def build_papers_explorer_body(
    *,
    lang: str,
    root_prefix: str,
    bib_sections: list[dict[str, Any]],
    bib_entries: list[dict[str, Any]],
    panel_papers: list[dict[str, Any]] | None = None,
) -> str:
    page_prefix = root_prefix + url_for(lang)
    docs_prefix = f"{root_prefix}docs/"
    copy_lbl = strings_for(lang)["ui"]["copy"]
    paper_rows = panel_papers or bib_entries

    t = strings_for(lang)["bibliography"]
    counts = {"chapters": len(bib_sections), "references": len(paper_rows)}
    lead = t["lead"].format(**counts)
    all_chap = t["all_chap"].format(**counts)
    status_tpl = t["status_tpl"]

    def sec_label(sec_id: str, en_title: str) -> str:
        if lang == "zh":
            return BIB_SECTION_TITLES_ZH.get(sec_id, en_title)
        return en_title


    options_html = [f'<option value="all">{html.escape(all_chap)}</option>']
    for sec in bib_sections:
        options_html.append(
            f'<option value="{html.escape(sec["id"])}">'
            f'{html.escape(sec["id"])}. {html.escape(sec_label(sec["id"], sec["title"]))} ({sec["count"]})</option>'
        )

    cards_html: list[str] = []
    for ent in paper_rows:
        linked_dirs = ent.get("cited_by_dirs", []) or ent.get("section_related", [])
        has_direct = "1" if ent.get("cited_by_dirs") else "0"
        venue_parts = [p for p in [ent.get("venue", ""), f'vol. {ent.get("volume", "")}' if ent.get("volume") else "", ent.get("year", "")] if p]
        venue_line = ", ".join(venue_parts)
        section_id = ent.get("section_id", "00")
        section_title = ent.get("section_title", "General")
        chap_zh = BIB_SECTION_TITLES_ZH.get(section_id, "")
        chap_disp = sec_label(section_id, section_title)
        search_blob = " ".join(
            [
                ent.get("key", ""),
                ent.get("title", ""),
                ent.get("authors", ""),
                venue_line,
                section_title,
                chap_zh,
                ent.get("eprint", ""),
                ent.get("doi", ""),
                " ".join(linked_dirs),
            ]
        ).lower()

        ext_links: list[str] = []
        if ent.get("doi"):
            ext_links.append(
                f'<a class="bib-ext-badge" href="https://doi.org/{html.escape(ent.get("doi", ""))}" '
                f'target="_blank" rel="noopener">DOI ↗</a>'
            )
        if ent.get("eprint"):
            ext_links.append(
                f'<a class="bib-ext-badge" href="https://arxiv.org/abs/{html.escape(ent.get("eprint", ""))}" '
                f'target="_blank" rel="noopener">arXiv:{html.escape(ent.get("eprint", ""))} ↗</a>'
            )
        elif ent.get("url") and not ent.get("doi"):
            ext_links.append(
                f'<a class="bib-ext-badge" href="{html.escape(ent.get("url", ""))}" '
                f'target="_blank" rel="noopener">URL ↗</a>'
            )
        ext_links.append(
            f'<a class="bib-ext-badge" href="{docs_prefix}references.html#ref_{html.escape(ent.get("key", ""))}">{t["docgen_badge_lbl"]}</a>'
        )

        dir_chips = ""
        if ent.get("cited_by_dirs"):
            chips = "".join(
                f'<a class="dir-chip" href="{page_prefix}modules.html#{html.escape(d)}">'
                f'{html.escape(d.removeprefix("Qatlib/"))}</a>'
                for d in ent.get("cited_by_dirs", [])[:6]
            )
            dir_chips = (
                f'<div class="chip-list" style="margin-top:8px;align-items:center;">'
                f'<span style="font-size:12px;color:var(--fg-faint);">{t["form_prefix"]}</span>{chips}</div>'
            )
        detail_link = f'<a class="bib-ext-badge" href="{_paper_href(ent.get("key", ""), lang, root_prefix)}">{t["detail"]}</a>'
        claim_badges = " ".join(
            _badge(f"{len(ent.get('claims', []))} claims", "rank")
            for _ in [0]
            if ent.get("claims")
        )

        cards_html.append(
            f'<article id="{html.escape(ent.get("key", ""))}" class="bib-card" '
            f'data-section="{html.escape(section_id)}" data-formalized="{has_direct}" '
            f'data-search="{html.escape(search_blob)}">'
            f'<div class="bib-meta-top">'
            f'<a class="bib-key" href="#{html.escape(ent.get("key", ""))}">[{html.escape(ent.get("key", ""))}]</a>'
            f'<span class="bib-chapter">{html.escape(section_id)}. {html.escape(chap_disp)}</span>'
            f"</div>"
            f'<h2 class="bib-title">{html.escape(ent.get("title", ""))}</h2>'
            f'<p class="bib-authors">{html.escape(ent.get("authors", ""))}</p>'
            f'<p class="bib-venue">{html.escape(venue_line)}</p>'
            f'<div class="bib-links">{"".join(ext_links)}{detail_link}{claim_badges}'
            f'<details class="bib-raw-details"><summary>{t["raw_lbl"]}</summary>'
            f'<div class="code-card" style="margin-top:8px;">'
            f'<div class="code-card-header"><span class="code-lang">BIBTEX</span>'
            f'<button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>'
            f'<pre><code>{html.escape(ent.get("raw_bibtex", ""))}</code></pre></div></details></div>'
            f"{dir_chips}</article>"
        )

    return f"""
  <main class="explorer-wrap">
    <div class="section-header" style="margin-bottom:16px;">
      <div class="section-eyebrow">docs/references.bib</div>
      <h1 style="margin:0 0 8px;font-size:30px;">{html.escape(t["h1"])}</h1>
      <p>{html.escape(lead)}</p>
    </div>

    <div class="explorer-toolbar">
      <input id="explorer-search" class="filter-input" type="search" placeholder="{html.escape(t["placeholder"])}" autocomplete="off">
      <select id="chapter-filter" class="chapter-select" aria-label="{html.escape(t["select_aria"])}">
        {"".join(options_html)}
      </select>
      <label style="display:inline-flex;align-items:center;gap:6px;font-size:13px;color:var(--fg-muted);cursor:pointer;">
        <input id="formalized-only" type="checkbox"> {html.escape(t["only_form_lbl"])}
      </label>
    </div>

    <div id="explorer-status" class="results-status" data-template="{html.escape(status_tpl)}">
      {html.escape(status_tpl.format(shown=len(paper_rows), total=len(paper_rows)))}
    </div>

    <div id="bib-explorer-list" class="bib-list">
      {"".join(cards_html)}
    </div>
  </main>
"""


def build_legacy_redirect(page: str, site_url: str) -> str:
    route = url_for(DEFAULT_LOCALE, page)
    legacy_path = f"zh/{page}"
    target = relative_url(legacy_path, route)
    return f'''<!doctype html>
<html lang="zh-Hans" data-redirect-target="{target}">
<head><meta charset="utf-8"><title>Qatlib</title>
<link rel="canonical" href="{html.escape(site_url + route)}">
<noscript><meta http-equiv="refresh" content="0; url={target}"></noscript>
<link rel="icon" href="{root_relative(legacy_path)}favicon.ico">
<script type="module" src="{root_relative(legacy_path)}assets/i18n.js"></script></head>
<body><a href="{target}">Qatlib →</a></body></html>
'''


def write_site_indexes(out_dir: Path, site_url: str) -> None:
    homes = (site_url, site_url + url_for("en"))
    entries = "\n".join(f"  <url><loc>{html.escape(url)}</loc></url>" for url in homes)
    (out_dir / "sitemap.xml").write_text(
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        f"{entries}\n</urlset>\n", encoding="utf-8",
    )
    lines = ["# Qatlib", "", f'> {strings_for("en")["ui"]["site_tagline"]}.', ""]
    for lang, info in LOCALES.items():
        labels = strings_for(lang)["ui"]
        lines.extend([f'## {info["name"]}', ""])
        for page, label in NAV_PAGES.items():
            lines.append(f"- [{labels[label]}]({site_url + url_for(lang, page)})")
        lines.append("")
    lines.extend(["## API reference", "", f"- [API documentation]({site_url}docs/)"])
    for layer in PANEL_LAYERS:
        lines.append(f"- [Qatlib.{layer}]({site_url}docs/Qatlib/{layer}/)")
    (out_dir / "llms.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_smart_404_page() -> str:
    headings = " / ".join(
        f'<span lang="{info["tag"]}">{strings_for(key)["ui"]["not_found"]}</span>'
        for key, info in LOCALES.items()
    )
    links = " · ".join(language_link(locale, "./" + url_for(locale)) for locale in LOCALES)
    return f'''<!doctype html>
<html lang="en">
<head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>404 · Qatlib</title>
<link rel="stylesheet" href="./assets/style.css">
{render_favicon_links("./")}
<script type="module" src="./assets/i18n.js"></script>
<script defer src="./assets/site.js"></script></head>
<body><main id="redirect-msg" class="section"><h1>404 · {headings}</h1>
<p>{links} · <a href="./docs/">{strings_for("en")["ui"]["footer_api"]}</a></p>
</main></body></html>
'''

# ---------------------------------------------------------------------------
# doc-gen4 post-processing (_site/docs/)
# ---------------------------------------------------------------------------

DOCGEN_TYPOGRAPHY_CSS = """/* Qatlib typography: modern sans and CJK fallbacks */
body, .inductive_ctor_doc, .structure_field_doc {
  font-family: 'Lato Medium', Lato, -apple-system, BlinkMacSystemFont, "Segoe UI",
    "PingFang SC", "HarmonyOS Sans SC", "Source Han Sans SC",
    "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", sans-serif;
  line-height: 1.62;
}
h1, h2, h3, h4, h5, h6, strong, b {
  font-family: Lato, 'Lato Medium', -apple-system, BlinkMacSystemFont, "Segoe UI",
    "PingFang SC", "HarmonyOS Sans SC", "Source Han Sans SC",
    "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", sans-serif;
}
.imports li, code, .decl_header, .attributes, .structure_field_info,
.constructor, .instances li, .instances-for-list li, .equation, .structure_ext_ctor {
  font-family: 'JuliaMono', ui-monospace, SFMono-Regular, Menlo, Consolas,
    "Sarasa Mono SC", "Noto Sans Mono CJK SC", "PingFang SC",
    "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", monospace;
}
"""


def upgrade_docgen_directory(
    docs_out: Path,
    toolchain_tag: str,
    tree_stats: dict[str, Any],
    bib_count: int,
    areas_en: list[dict[str, Any]],
) -> None:
    """Enhance doc-gen4 output under _site/docs/ without breaking any relative assets."""
    # Existing API pages already resolve their icon to this shared doc-gen4 asset.
    shutil.copy2(FAVICON_ASSETS / ADAPTIVE_FAVICON, docs_out / "favicon.svg")

    # Patch only the mounted output, after raw snapshot verification. Reuse the
    # existing Lato family for real bold outlines without adding a font source.
    style_file = docs_out / "style.css"
    if style_file.is_file():
        css = style_file.read_text(encoding="utf-8")
        if DOCGEN_TYPOGRAPHY_CSS not in css:
            style_file.write_text(css.rstrip() + "\n\n" + DOCGEN_TYPOGRAPHY_CSS, encoding="utf-8")

    en = "../" + url_for("en")
    zh = "../" + url_for("zh")

    # 1. Inject return-to-portal links at the top of navbar.html
    navbar_file = docs_out / "navbar.html"
    if navbar_file.is_file():
        nav_html = navbar_file.read_text(encoding="utf-8")
        portal_links = (
            '<h3>Qatlib Portal</h3>'
            f'<div class="nav_link"><a href="{en}">← Home &amp; Guides</a></div>'
            f'<div class="nav_link"><a href="{en}getting-started.html">getting started</a></div>'
            f'<div class="nav_link"><a href="{en}modules.html">module explorer</a></div>'
            f'<div class="nav_link"><a href="{en}papers.html">bibliography</a></div>'
            f'<div class="nav_link"><a href="{en}{DEPENDENCY_GRAPH_PAGE}">theorem dependencies</a></div>'
            f'<div class="nav_link">{language_link("zh", zh)}</div>'
        )
        if "Qatlib Portal" in nav_html:
            nav_html = re.sub(
                r"<h3>Qatlib Portal</h3>[\s\S]*?(?=<h3>General documentation</h3>)",
                lambda _: portal_links,
                nav_html,
                count=1,
            )
            navbar_file.write_text(nav_html, encoding="utf-8")
        elif "<h3>General documentation</h3>" in nav_html:
            nav_html = nav_html.replace("<h3>General documentation</h3>", portal_links + "<h3>General documentation</h3>", 1)
            navbar_file.write_text(nav_html, encoding="utf-8")

    # 2. Replace the generic 2-line stub inside _site/docs/index.html <main>...</main>
    index_file = docs_out / "index.html"
    if index_file.is_file():
        idx_html = index_file.read_text(encoding="utf-8")
        layers = tree_stats["layers"]
        dir_lookup = {d["rel_dir"]: d["entry_html"] for d in tree_stats["dirs"]}
        area_lis = []
        for a in areas_en:
            links = ", ".join(
                f'<a href="./{dir_lookup.get(d, d + "/index.html")}"><code>{html.escape(d.removeprefix("Qatlib/"))}</code></a>'
                for d in a["dirs"][:4]
            )
            area_lis.append(f'<li><strong>{html.escape(a["title"])}</strong>: {links}</li>')

        rich_main = f"""<main><a id="top"></a>
<div style="max-width:920px;line-height:1.65;">
  <p style="margin:0 0 12px;">
    <a href="{en}"><strong>← Back to Qatlib Home &amp; Guides</strong></a>
    &nbsp;·&nbsp; <a href="{en}getting-started.html">Getting Started &amp; Cache</a>
    &nbsp;·&nbsp; <a href="{en}architecture.html">Architecture</a>
    &nbsp;·&nbsp; <a href="{en}modules.html">Module Explorer</a>
    &nbsp;·&nbsp; <a href="{en}papers.html">Bibliography ({bib_count})</a>
    &nbsp;·&nbsp; <a href="{en}{DEPENDENCY_GRAPH_PAGE}">Theorem Dependencies</a>
    &nbsp;·&nbsp; {language_link("zh", zh)}
  </p>
  <h1>Qatlib API Reference (<code>doc-gen4</code>)</h1>
  <p>
    Formalized API documentation for <strong>Qatlib</strong> (Lean <code>{html.escape(toolchain_tag)}</code>),
    built on top of <code>Mathlib</code> and <code>Physlib</code>.
    Use the <strong>Search</strong> box in the top-right corner to jump to any theorem, definition, or structure,
    or expand the module tree on the left.
  </p>
  <ul>
    <li><strong><a href="./Qatlib/Foundations/index.html">Qatlib.Foundations</a></strong> — {layers['Foundations']['dir_count']} directories ({layers['Foundations']['module_count']:,} modules): matrix &amp; operator norms, quantum states, concentration bounds, graph Laplacians, finite-precision arithmetic.</li>
    <li><strong><a href="./Qatlib/Concepts/index.html">Qatlib.Concepts</a></strong> — {layers['Concepts']['dir_count']} directories ({layers['Concepts']['module_count']:,} modules): quantum channels, entropy, block-encoding, QSVT/QSP, amplitude amplification, quantum walks, adversary bounds, fermionic/bosonic algebras, QEC.</li>
    <li><strong><a href="./Qatlib/Papers/index.html">Qatlib.Papers</a></strong> — {layers['Papers']['dir_count']} directories ({layers['Papers']['module_count']:,} modules): formalized definitions, main theorems, and resource bounds from the quantum computing literature.</li>
    <li><strong>General Indices</strong>: <a href="./Qatlib.html"><code>Qatlib</code> umbrella</a> · <a href="./references.html">Bibliography (<code>references.html</code>)</a> · <a href="./tactics.html">Tactics</a> · <a href="./foundational_types.html">Foundational Types</a></li>
  </ul>
  <h2>Entry Points by Research Area</h2>
  <ul>{"".join(area_lis)}</ul>
</div>
</main>"""
        idx_html = re.sub(r"<main>[\s\S]*?</main>", lambda _: rich_main, idx_html, count=1)
        idx_html = idx_html.replace("<title>Index</title>", "<title>Qatlib API Reference</title>", 1)
        favicon_links = render_favicon_links("../")
        if favicon_links not in idx_html:
            idx_html = re.sub(
                r'<link rel="icon" href="(?:\./)?favicon\.svg">|</head>',
                lambda match: favicon_links + ("\n</head>" if match.group() == "</head>" else ""),
                idx_html,
                count=1,
            )
        index_file.write_text(idx_html, encoding="utf-8")

    # 3. Generate lightweight directory index pages under _site/docs/Qatlib/... so directory URLs never 404
    _generate_docgen_dir_indexes(docs_out, tree_stats)


def _generate_docgen_dir_indexes(docs_out: Path, tree_stats: dict[str, Any]) -> None:
    """Create index.html for Qatlib/, Qatlib/<Layer>/, and Qatlib/<Layer>/<Dir>/ inside _site/docs/."""

    def write_dir_index(rel_dir: str, heading: str, items_html: str, depth: int) -> None:
        target = docs_out / rel_dir / "index.html"
        if target.exists():
            return
        target.parent.mkdir(parents=True, exist_ok=True)
        root_rel = "../" * depth
        portal_rel = "../" * (depth + 1)
        has_docgen_shell = (docs_out / "style.css").is_file() and (docs_out / "navbar.html").is_file()
        if has_docgen_shell:
            page = (
                f'<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">'
                f'<meta name="viewport" content="width=device-width, initial-scale=1">'
                f'<link rel="stylesheet" href="{root_rel}style.css">'
                f'{render_favicon_links(portal_rel)}'
                f"<title>{html.escape(heading)} — Qatlib API</title>"
                f'<script>const SITE_ROOT="{root_rel}";</script>'
                f'<script type="module" src="{root_rel}search.js"></script>'
                f"</head><body>"
                f'<input id="nav_toggle" type="checkbox">'
                f"<header><h1><label for=\"nav_toggle\"></label><span>Documentation</span></h1>"
                f'<h2 class="header_filename break_within"><span class="name">{html.escape(heading)}</span></h2>'
                f'<form id="search_form" action="{root_rel}search.html" method="get">'
                f'<input type="text" name="q" autocomplete="off"> <button id="search_button" type="submit">Search</button></form></header>'
                f'<main><a id="top"></a>'
                f'<p><a href="{portal_rel}{url_for("en")}">← Qatlib Home</a> · '
                f'<a href="{portal_rel}{url_for("en", "modules.html")}#{html.escape(rel_dir)}">Module Explorer</a> · '
                f'<a href="{root_rel}index.html">API Index</a> · '
                f'<a href="{GITHUB_REPO_URL}/tree/main/{html.escape(rel_dir)}" target="_blank" rel="noopener">GitHub Source ↗</a></p>'
                f"<h1>{html.escape(heading)}</h1>{items_html}</main>"
                f'<nav class="nav"><iframe src="{root_rel}navbar.html" class="navframe" frameBorder="0"></iframe></nav>'
                f"</body></html>"
            )
        else:
            page = (
                f'<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">'
                f'<meta name="viewport" content="width=device-width, initial-scale=1">'
                f'<link rel="stylesheet" href="{portal_rel}assets/style.css">'
                f'<script src="{portal_rel}assets/theme-init.js"></script>'
                f'{render_favicon_links(portal_rel)}'
                f"<title>{html.escape(heading)} — Qatlib API</title></head>"
                f'<body style="padding:36px 24px;max-width:920px;margin:0 auto;">'
                f'<p><a href="{portal_rel}{url_for("en")}">← Qatlib Home</a> · '
                f'<a href="{portal_rel}{url_for("en", "modules.html")}#{html.escape(rel_dir)}">Module Explorer</a> · '
                f'<a href="{root_rel}index.html">API Index</a></p>'
                f"<h1>{html.escape(heading)}</h1>{items_html}</body></html>"
            )
        target.write_text(page, encoding="utf-8")

    # Root Qatlib/
    layer_links = "".join(
        f'<li><a href="./{layer}/index.html"><strong>Qatlib.{layer}</strong></a> '
        f'({tree_stats["layers"][layer]["dir_count"]} directories, '
        f'{tree_stats["layers"][layer]["module_count"]:,} modules)</li>'
        for layer in ("Foundations", "Concepts", "Papers")
    )
    write_dir_index("Qatlib", "Qatlib", f"<ul>{layer_links}</ul>", depth=1)

    for layer in ("Foundations", "Concepts", "Papers"):
        ldirs = [d for d in tree_stats["dirs"] if d["layer"] == layer]
        lis = "".join(
            f'<li><a href="./{d["name"]}/index.html"><code>{html.escape(d["name"])}</code></a> '
            f'({d["module_count"]} modules)'
            + (f' — {html.escape(d["title"])}' if d["title"] else "")
            + "</li>"
            for d in ldirs
        )
        write_dir_index(f"Qatlib/{layer}", f"Qatlib.{layer}", f"<ul>{lis}</ul>", depth=2)

    for d in tree_stats["dirs"]:
        prefix = d["rel_dir"] + "/"
        mod_lis = []
        for lean_no_ext in d["all_lean_rel"]:
            sub_rel = lean_no_ext.removeprefix(prefix)
            mod_dot = lean_no_ext.replace("/", ".")
            mod_lis.append(
                f'<li><a href="./{sub_rel}.html"><code>{html.escape(mod_dot)}</code></a></li>'
            )
        desc = f'<p>{html.escape(d["summary"])}</p>' if d["summary"] else ""
        write_dir_index(
            d["rel_dir"],
            d["rel_dir"].replace("/", "."),
            f"{desc}<ul>{''.join(mod_lis)}</ul>",
            depth=3,
        )


def create_stub_docgen_dir(docs_out: Path, toolchain_tag: str, tree_stats: dict[str, Any]) -> None:
    """Create a clean local preview stub for _site/docs/ when docbuild/.lake/build/doc is absent."""
    docs_out.mkdir(parents=True, exist_ok=True)

    def render_stub_note(rel_doc_path: str) -> str:
        live_url = f"{DEFAULT_SITE_URL}docs/{rel_doc_path}"
        return (
            "<div style='padding:16px 20px;border-radius:10px;background:var(--brand-soft);"
            "border:1px solid var(--border);margin:16px 0 24px;'>"
            "<p style='margin:0 0 12px;'><strong>Preview Mode Stub</strong>: In GitHub Pages CI "
            "(<code>.github/workflows/docs.yml</code>), full <code>doc-gen4</code> HTML output is mounted "
            "directly under <code>/docs/</code>.</p>"
            f"<p style='margin:0;'><a class='btn btn-primary' href='{html.escape(live_url)}' "
            "target='_blank' rel='noopener'>Open Live doc-gen4 Page on GitHub Pages ↗</a></p></div>"
        )

    for fname, heading in [
        ("index.html", "Qatlib API Reference (doc-gen4)"),
        ("Qatlib.html", "Qatlib Umbrella Module"),
        ("search.html", "API Declaration Search"),
        ("references.html", "doc-gen4 Bibliography"),
        ("tactics.html", "Tactics Reference"),
        ("foundational_types.html", "Foundational Types"),
    ]:
        (docs_out / fname).write_text(
            f'<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width, initial-scale=1">'
            f'<link rel="stylesheet" href="../assets/style.css">'
            f'<script src="../assets/theme-init.js"></script>'
            f'{render_favicon_links("../")}'
            f"<title>{heading}</title></head>"
            f'<body style="padding:40px 24px;max-width:880px;margin:0 auto;">'
            f'<p><a href="../{url_for("en")}">← Back to Qatlib Portal</a> · <a href="../{url_for("en", "modules.html")}">Module Explorer</a></p>'
            f"<h1>{heading} (Lean {html.escape(toolchain_tag)})</h1>{render_stub_note(fname)}"
            f"</body></html>",
            encoding="utf-8",
        )
    # Match directory indices and guide links, which can target any source module.
    for d in tree_stats["dirs"]:
        for lean_no_ext in d["all_lean_rel"]:
            html_path = f"{lean_no_ext}.html"
            label = html.escape(lean_no_ext.replace("/", "."))
            p = docs_out / html_path
            p.parent.mkdir(parents=True, exist_ok=True)
            rel_assets = os.path.relpath(docs_out.parent / "assets/style.css", p.parent).replace("\\", "/")
            rel_theme = os.path.relpath(docs_out.parent / "assets/theme-init.js", p.parent).replace("\\", "/")
            portal_rel = os.path.relpath(docs_out.parent, p.parent).replace("\\", "/") + "/"
            p.write_text(
                f'<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">'
                f'<link rel="stylesheet" href="{rel_assets}">'
                f'<script src="{rel_theme}"></script>'
                f'{render_favicon_links(portal_rel)}'
                f'<title>{label}</title></head>'
                f'<body style="padding:36px 24px;max-width:880px;margin:0 auto;">'
                f'<p><a href="{portal_rel}{url_for("en")}">← Back to Qatlib Portal</a></p>'
                f"<h1><code>{label}</code></h1>{render_stub_note(html_path)}</body></html>",
                encoding="utf-8",
            )
    _generate_docgen_dir_indexes(docs_out, tree_stats)


# ---------------------------------------------------------------------------
# Internal Link Checker (--check)
# ---------------------------------------------------------------------------

class _LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for k, v in attrs:
            if v and k in ("href", "src", "action"):
                self.links.append(v)


def verify_portal_links(out_dir: Path) -> list[str]:
    """Verify every internal relative link on generated portal pages resolves on disk."""
    errors: list[str] = []
    portal_pages = (p for p in out_dir.rglob("*.html")
                    if "docs" not in p.relative_to(out_dir).parts)
    for html_file in portal_pages:
        parser = _LinkCollector()
        parser.feed(html_file.read_text(encoding="utf-8"))
        for raw in parser.links:
            if raw.startswith(("http://", "https://", "mailto:", "javascript:", "data:", "#")):
                continue
            clean = raw.split("#", 1)[0].split("?", 1)[0]
            if not clean:
                continue
            resolved = (html_file.parent / unquote(clean)).resolve()
            if resolved.is_dir():
                resolved = resolved / "index.html"
            if not resolved.is_file():
                errors.append(f"{html_file.relative_to(out_dir)} -> broken link: {raw}")
    return errors


def verify_docgen(repo_root: Path, docgen_dir: Path) -> list[str]:
    """Require real API pages for every source module and usable search assets."""
    required = ["index.html", "navbar.html", "style.css", "search.html", "search.js",
                "declaration-data.js", "references.html", "Qatlib.html",
                "declarations/declaration-data.bmp"]
    required.extend(str(p.relative_to(repo_root).with_suffix(".html"))
                    for p in (repo_root / "Qatlib").rglob("*.lean"))
    errors = []
    for name in required:
        path = docgen_dir / name
        if not path.is_file() or path.stat().st_size == 0:
            errors.append(f"missing or empty API output: {name}")
    return errors


# ---------------------------------------------------------------------------
# Main Build Entrypoint
# ---------------------------------------------------------------------------

def write_panel_detail_pages(
    *,
    out_dir: Path,
    catalog: dict[str, Any],
    panel_papers: list[dict[str, Any]],
    toolchain_tag: str,
    site_url: str,
) -> None:
    """Write bilingual Unit and Paper detail views driven by one panel model."""
    all_unit_ids = {unit["id"] for unit in catalog.get("units", [])}
    for lang in LOCALES:
        locale_root = out_dir / LOCALES[lang]["prefix"]
        units_root = locale_root / "units"
        papers_root = locale_root / "papers"
        units_root.mkdir(parents=True, exist_ok=True)
        papers_root.mkdir(parents=True, exist_ok=True)
        for unit in catalog.get("units", []):
            page_slug = f"units/{unit['id']}.html"
            root_prefix = root_relative(LOCALES[lang]["prefix"] + page_slug)
            body = build_unit_detail_body(
                unit=unit,
                lang=lang,
                root_prefix=root_prefix,
                all_unit_ids=all_unit_ids,
            )
            (units_root / f"{unit['id']}.html").write_text(
                render_page_shell(
                    title=strings_for(lang)["unit"]["heading"].format(id=unit["id"]),
                    lang=lang,
                    page_slug=page_slug,
                    root_prefix=root_prefix,
                    toolchain_tag=toolchain_tag,
                    site_url=site_url,
                    wordmark_nav=render_wordmark(root_prefix, "nav-wordmark"),
                    body_html=body,
                ),
                encoding="utf-8",
            )
        for paper in panel_papers:
            paper_id = paper.get("key", "")
            if not paper_id:
                continue
            page_slug = f"papers/{paper_id}.html"
            root_prefix = root_relative(LOCALES[lang]["prefix"] + page_slug)
            body = build_paper_detail_body(
                paper=paper,
                lang=lang,
                root_prefix=root_prefix,
                catalog=catalog,
            )
            (papers_root / f"{paper_id}.html").write_text(
                render_page_shell(
                    title=strings_for(lang)["paper"]["title"].format(id=paper_id),
                    lang=lang,
                    page_slug=page_slug,
                    root_prefix=root_prefix,
                    toolchain_tag=toolchain_tag,
                    site_url=site_url,
                    wordmark_nav=render_wordmark(root_prefix, "nav-wordmark"),
                    body_html=body,
                ),
                encoding="utf-8",
            )


def _reset_output_dir(path: Path) -> None:
    """Move a prior generated site to the desktop trash before rebuilding."""
    if not path.exists():
        return
    trash = shutil.which("trash-put")
    if trash is None:
        raise RuntimeError(f"cannot safely replace generated output without trash-put: {path}")
    subprocess.run([trash, str(path)], check=True)

def read_lean_toolchain(repo_root: Path) -> str:
    return (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip()


def install_dependency_graph_api(docs_dir: Path) -> None:
    asset = docs_dir / DEPENDENCY_GRAPH_ASSET
    api_search = docs_dir / "search.js"
    if not asset.is_file() or not api_search.is_file():
        return
    with asset.open("rb") as stream:
        if stream.peek(2).startswith(b"\x1f\x8b"):
            with gzip.GzipFile(fileobj=stream) as decoded:
                graph = json.load(decoded)
        else:
            graph = json.load(stream)
    shutil.copy2(SITE_ASSETS / DEPENDENCY_GRAPH_API, docs_dir)
    graph_import = f'import {{addQatlibDependencyLinks}} from "./{DEPENDENCY_GRAPH_API}";'
    routes = {
        lang: [relative_url("docs/search.js", url_for(lang, DEPENDENCY_GRAPH_PAGE)),
               strings_for(lang)["graph"]["api_link"]]
        for lang in LOCALES
    }
    options = ", ".join(json.dumps(value, ensure_ascii=False) for value in
                        (routes, PANEL_LAYERS, graph.get("ambiguousNames", [])))
    bridge = f"{graph_import}\naddQatlibDependencyLinks({options});\n"
    search_script = api_search.read_text(encoding="utf-8")
    if bridge not in search_script:
        legacy_import = f'import "./{DEPENDENCY_GRAPH_API}";\n'
        search_script = search_script.replace(legacy_import, "")
        search_script = re.sub(
            rf"(?m)^{re.escape(graph_import)}\naddQatlibDependencyLinks\([^\n]*\);\n",
            "", search_script,
        )
        api_search.write_text(f"{search_script.rstrip()}\n\n{bridge}", encoding="utf-8")


def build_site(
    repo_root: Path,
    out_dir: Path,
    docgen_dir: Path | None,
    move_docgen: bool,
    stub_docgen: bool,
    check_links: bool,
    metadata_dir: Path | None = None,
    dependency_graph: Path | None = None,
    site_url: str = DEFAULT_SITE_URL,
    mathjax_dir: Path | None = None,
) -> None:
    base = urlsplit(site_url)
    if base.scheme not in ("http", "https") or not base.netloc or base.query or base.fragment:
        raise ValueError("site URL must be an absolute HTTP(S) URL without a query or fragment")
    site_url = base.geturl().rstrip("/") + "/"
    if docgen_dir is not None:
        errors = verify_docgen(repo_root, docgen_dir)
        if errors:
            raise RuntimeError("Incomplete doc-gen4 output: " + "; ".join(errors[:10]))
    tc_raw = read_lean_toolchain(repo_root)
    toolchain_tag = tc_raw.split(":")[-1] if ":" in tc_raw else tc_raw

    bib_sections, bib_entries = parse_references_bib(repo_root / "docs/references.bib")
    bib_key_map = {e["key"]: e for e in bib_entries}
    tree_stats = scan_qatlib_tree(repo_root, set(bib_key_map.keys()))
    for ck, dir_set in tree_stats["cite_to_dirs"].items():
        if ck in bib_key_map:
            bib_key_map[ck]["cited_by_dirs"] = sorted(dir_set)
    catalog = scan_catalog_sources(repo_root)
    metadata = load_panel_metadata(metadata_dir)
    if metadata_dir is not None:
        catalog = apply_panel_metadata(catalog, metadata)
    tree_stats["catalog"] = catalog
    panel_papers = build_panel_papers(bib_entries, catalog, metadata)
    tree_stats["total_modules"] = catalog["total_modules"]
    tree_stats["total_dirs"] = catalog["total_dirs"]
    for layer in PANEL_LAYERS:
        tree_stats["layers"][layer]["module_count"] = catalog["layers"][layer]["module_count"]
        tree_stats["layers"][layer]["dir_count"] = catalog["layers"][layer]["dir_count"]

    readmes = {
        lang: repo_root / f"README{info['md_suffix']}.md"
        for lang, info in LOCALES.items()
    }
    readme_data = {lang: parse_readme_areas_and_bibtex(path) for lang, path in readmes.items()}

    _reset_output_dir(out_dir)
    (out_dir / "assets").mkdir(parents=True, exist_ok=True)
    (out_dir / ".nojekyll").write_text("", encoding="utf-8")
    (out_dir / "assets/style.css").write_text(SITE_CSS, encoding="utf-8")
    (out_dir / "assets/theme-init.js").write_text(THEME_INIT_JS, encoding="utf-8")
    (out_dir / "assets/site.js").write_text(SITE_JS, encoding="utf-8")
    for asset in (*DEPENDENCY_GRAPH_PORTAL_ASSETS, "i18n.js"):
        shutil.copy2(SITE_ASSETS / asset, out_dir / "assets" / asset)
    for wm_asset in ("qatlib-wordmark.svg", "qatlib-wordmark.png", "qatlib-wordmark-dark.svg", SOCIAL_IMAGE):
        wm_src = repo_root / BRAND_ASSETS / wm_asset
        if not wm_src.is_file():
            wm_src = FAVICON_ASSETS.parent / wm_asset
        shutil.copy2(wm_src, out_dir / "assets" / wm_asset)
    for favicon in FAVICON_ASSETS.iterdir():
        if favicon.suffix in (".png", ".ico") or favicon.name == ADAPTIVE_FAVICON:
            shutil.copy2(favicon, out_dir / favicon.name)

    for lang, info in LOCALES.items():
        sub_dir = out_dir / info["prefix"]
        sub_dir.mkdir(exist_ok=True)
        root_prefix = root_relative(info["prefix"] + "index.html")
        wordmark_nav = render_wordmark(root_prefix, "nav-wordmark")
        wordmark_hero = render_wordmark(root_prefix, "hero-wordmark")
        suffix = info["md_suffix"]
        readme = readmes[lang]
        areas, bibtex_str = readme_data[lang]
        bibtex_str = bibtex_str or readme_data["en"][1]
        graph_title, graph_body = build_dependency_graph_body(lang, root_prefix, wordmark_nav)
        (sub_dir / DEPENDENCY_GRAPH_PAGE).write_text(
            render_page_shell(
                title=graph_title, lang=lang, page_slug=DEPENDENCY_GRAPH_PAGE,
                root_prefix=root_prefix, toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav, body_html=graph_body,
            ), encoding="utf-8",
        )

        # 1. Overview (index.html)
        _, qec_html, _ = process_markdown_guide(
            readme, repo_root, lang, root_prefix, section_id="quantum-error-correction",
        )
        home_body = build_home_body(
            lang=lang,
            root_prefix=root_prefix,
            toolchain_tag=toolchain_tag,
            wordmark_hero=wordmark_hero,
            tree_stats=tree_stats,
            bib_count=len(bib_entries),
            areas=areas,
            bibtex_str=bibtex_str,
            qec_html=qec_html,
        )
        (sub_dir / "index.html").write_text(
            render_page_shell(
                title="Qatlib",
                lang=lang,
                page_slug="index.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=home_body,
            ),
            encoding="utf-8",
        )

        # 2. Getting Started
        gs_src = repo_root / f"docs/getting-started{suffix}.md"
        gs_title, gs_html, gs_toc = process_markdown_guide(gs_src, repo_root, lang, root_prefix)
        (sub_dir / "getting-started.html").write_text(
            render_page_shell(
                title=gs_title,
                lang=lang,
                page_slug="getting-started.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=build_docs_layout(
                    page_title=gs_title,
                    source_rel=gs_src.relative_to(repo_root).as_posix(),
                    lang=lang,
                    page_slug="getting-started.html",
                    root_prefix=root_prefix,
                    prose_html=gs_html,
                    toc=gs_toc,
                ),
            ),
            encoding="utf-8",
        )

        # 3. Architecture (+ scripts/README{.en,}.md tooling reference)
        arch_src = repo_root / f"docs/architecture{suffix}.md"
        arch_title, arch_html, arch_toc = process_markdown_guide(arch_src, repo_root, lang, root_prefix)
        scripts_md = repo_root / f"scripts/README{suffix}.md"
        if not scripts_md.is_file():
            scripts_md = repo_root / "scripts/README.md"
        if scripts_md.is_file():
            _, scripts_html, _ = process_markdown_guide(scripts_md, repo_root, lang, root_prefix)
            sec_title = strings_for(lang)["ui"]["architecture_tooling"]
            arch_html += (
                f'\n<h2 id="tooling">{sec_title}'
                f'<a class="heading-anchor" href="#tooling" aria-hidden="true" tabindex="-1">#</a></h2>\n'
                f"{scripts_html}"
            )
            arch_toc.append({"level": 2, "id": "tooling", "text": sec_title})

        (sub_dir / "architecture.html").write_text(
            render_page_shell(
                title=arch_title,
                lang=lang,
                page_slug="architecture.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=build_docs_layout(
                    page_title=arch_title,
                    source_rel=arch_src.relative_to(repo_root).as_posix(),
                    lang=lang,
                    page_slug="architecture.html",
                    root_prefix=root_prefix,
                    prose_html=arch_html,
                    toc=arch_toc,
                ),
            ),
            encoding="utf-8",
        )

        # 4. Module Explorer
        mod_title = strings_for(lang)["modules"]["h1"]
        (sub_dir / "modules.html").write_text(
            render_page_shell(
                title=mod_title,
                lang=lang,
                page_slug="modules.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=build_modules_explorer_body(
                    lang=lang,
                    root_prefix=root_prefix,
                    tree_stats=tree_stats,
                ),
            ),
            encoding="utf-8",
        )

        # 5. Papers & Bibliography
        pap_title = strings_for(lang)["bibliography"]["h1"]
        (sub_dir / "papers.html").write_text(
            render_page_shell(
                title=pap_title,
                lang=lang,
                page_slug="papers.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=build_papers_explorer_body(
                    lang=lang,
                    root_prefix=root_prefix,
                    bib_sections=bib_sections,
                    bib_entries=bib_entries,
                    panel_papers=panel_papers,
                ),
            ),
            encoding="utf-8",
        )

        # 6. Contributing
        contrib_src = repo_root / f"CONTRIBUTING{suffix}.md"
        contrib_title, contrib_html, contrib_toc = process_markdown_guide(contrib_src, repo_root, lang, root_prefix)
        (sub_dir / "contributing.html").write_text(
            render_page_shell(
                title=contrib_title,
                lang=lang,
                page_slug="contributing.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=build_docs_layout(
                    page_title=contrib_title,
                    source_rel=contrib_src.relative_to(repo_root).as_posix(),
                    lang=lang,
                    page_slug="contributing.html",
                    root_prefix=root_prefix,
                    prose_html=contrib_html,
                    toc=contrib_toc,
                ),
            ),
            encoding="utf-8",
        )

        # One authoritative English release history, with localized portal navigation.
        changelog_src = repo_root / "CHANGELOG.md"
        _, changelog_html, changelog_toc = process_markdown_guide(
            changelog_src, repo_root, lang, root_prefix
        )
        changelog_title = strings_for(lang)["ui"]["nav_changelog"]
        (sub_dir / "changelog.html").write_text(
            render_page_shell(
                title=changelog_title,
                lang=lang,
                page_slug="changelog.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                site_url=site_url,
                wordmark_nav=wordmark_nav,
                body_html=build_docs_layout(
                    page_title=changelog_title,
                    source_rel="CHANGELOG.md",
                    lang=lang,
                    page_slug="changelog.html",
                    root_prefix=root_prefix,
                    prose_html=changelog_html,
                    toc=changelog_toc,
                ),
            ),
            encoding="utf-8",
        )

    write_panel_detail_pages(
        out_dir=out_dir,
        catalog=catalog,
        panel_papers=panel_papers,
        toolchain_tag=toolchain_tag,
        site_url=site_url,
    )

    # Each former Chinese route keeps a thin redirect to its canonical page.
    for localized in (out_dir / "en").rglob("*.html"):
        page = localized.relative_to(out_dir / "en").as_posix()
        legacy = out_dir / "zh" / page
        legacy.parent.mkdir(parents=True, exist_ok=True)
        legacy.write_text(build_legacy_redirect(page, site_url), encoding="utf-8")
    (out_dir / "404.html").write_text(build_smart_404_page(), encoding="utf-8")
    write_site_indexes(out_dir, site_url)

    # Mount doc-gen4 output under _site/docs/
    docs_target = out_dir / "docs"
    if docgen_dir and docgen_dir.is_dir():
        if move_docgen:
            shutil.move(str(docgen_dir), str(docs_target))
        else:
            shutil.copytree(docgen_dir, docs_target)
        upgrade_docgen_directory(
            docs_out=docs_target,
            toolchain_tag=toolchain_tag,
            tree_stats=tree_stats,
            bib_count=len(bib_entries),
            areas_en=readme_data["en"][0],
        )
        adapt_docgen(docs_target, mathjax_dir)
    elif stub_docgen:
        create_stub_docgen_dir(docs_target, toolchain_tag, tree_stats)

    if dependency_graph is not None:
        docs_target.mkdir(exist_ok=True)
        shutil.copy2(dependency_graph, docs_target / DEPENDENCY_GRAPH_ASSET)
    install_dependency_graph_api(docs_target)

    if check_links:
        errs = verify_portal_links(out_dir)
        if errs:
            for e in errs[:30]:
                print(f"ERROR: {e}", file=sys.stderr)
            raise SystemExit(f"Portal link check failed with {len(errs)} broken link(s).")

    print(
        f"Built Qatlib site at {out_dir} "
        f"({tree_stats['total_modules']:,} modules across {tree_stats['total_dirs']:,} dirs, "
        f"{len(bib_entries):,} bibliography entries)."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."), help="Path to Qatlib repository root")
    parser.add_argument("--docgen-dir", type=Path, default=None, help="Path to doc-gen4 output (docbuild/.lake/build/doc)")
    parser.add_argument("--move-docgen", action="store_true", help="Move --docgen-dir into _site/docs in O(1) instead of copying")
    parser.add_argument("--stub-docgen-if-missing", action="store_true", help="Generate stub /docs/ pages for local preview if --docgen-dir is absent")
    parser.add_argument("--out-dir", type=Path, default=Path("_site"), help="Output directory for GitHub Pages artifact")
    parser.add_argument("--dependency-graph", type=Path, help="Use a prebuilt graph asset for local preview")
    parser.add_argument("--metadata-dir", type=Path, default=None, help="Optional Unit/Paper metadata directory to overlay on the source inventory")
    parser.add_argument("--check", action="store_true", help="Verify all internal relative links in generated portal HTML")
    parser.add_argument("--site-url", default=DEFAULT_SITE_URL, help="Public base URL for canonical and alternate links")
    parser.add_argument("--mathjax-dir", type=Path, help="Local MathJax 3.2.2 es5 directory for doc-gen4")
    args = parser.parse_args()

    build_site(
        repo_root=args.repo_root.resolve(),
        out_dir=args.out_dir.resolve(),
        docgen_dir=args.docgen_dir.resolve() if args.docgen_dir else None,
        move_docgen=args.move_docgen,
        stub_docgen=args.stub_docgen_if_missing,
        check_links=args.check,
        metadata_dir=args.metadata_dir.resolve() if args.metadata_dir else None,
        dependency_graph=args.dependency_graph.resolve() if args.dependency_graph else None,
        site_url=args.site_url,
        mathjax_dir=args.mathjax_dir.resolve() if args.mathjax_dir else None,
    )


if __name__ == "__main__":
    main()
