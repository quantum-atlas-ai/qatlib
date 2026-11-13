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
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import shutil
import sys
from typing import Any

GITHUB_REPO_URL = "https://github.com/quantum-atlas-ai/qatlib"
CACHE_CDN_URL = "https://lake-cache.quantum-atlas.ai"

# Fallback Qatlib brand wordmark group (selected Z-QL03: Q∀† scaled to 80%, lib unchanged, #263F5F on #FFFFFF)
FALLBACK_WORDMARK_INNER = (
    '<g id="prefix-qat" data-prefix-scale="0.8" transform="translate(0,20) scale(0.8)">'
    '<g id="quantum-q"><g id="q-bowl" transform="translate(6,0)">'
    '<path d="M23 0 H41 C54 0 64 13 64 33 V70 C64 90 54 103 41 103 H23 C10 103 0 90 0 70 '
    'V33 C0 13 10 0 23 0 Z M23 4.2 H41 C51.2 4.2 58.6 15.2 58.6 33 V70 C58.6 87.8 51.2 98.8 '
    '41 98.8 H23 C12.8 98.8 5.4 87.8 5.4 70 V33 C5.4 15.2 12.8 4.2 23 4.2 Z" '
    'fill="currentColor" fill-rule="evenodd"/></g>'
    '<path d="M40.37 76 C50.44 80 62 99 71 105 C74 107 77 107 80 105 L78 110 C73 112 69 109 '
    '65 104 C56 94 46.89 83 40.37 76 Z" fill="currentColor" fill-rule="evenodd"/></g>'
    '<g id="operator-ligature"><path d="M78 0 H83.46 L111 85.96 L138.54 0 H144 L111 103 Z" '
    'fill="currentColor" fill-rule="evenodd"/>'
    '<path d="M173.9 4 L178.1 3 L177.68 37 H174.32 Z" fill="currentColor"/>'
    '<path d="M176 -3 L180.6 2 L176 7 L171.4 2 Z" fill="currentColor"/>'
    '<path d="M170.7 37 L181.3 37 L179.445 81 L176 108 L172.555 81 Z M175.35 46 V88 '
    'L176.65 83 V46 Z" fill="currentColor" fill-rule="evenodd"/>'
    '<path d="M89 33.9 C115 33.9 152 33.9 175 33.9 C184 33.9 192 33.7 197 32.6 L196 38.295 '
    'C190 37.7 182 38.1 175 38.1 C150 38.1 115 38.1 91 38.1 Z" fill="currentColor" '
    'fill-rule="evenodd"/></g>'
    '<g id="qv-link"><path d="M68.5 33.9 H93 V38.1 H68.5 Z" fill="currentColor" '
    'fill-rule="evenodd"/></g></g>'
    '<g id="suffix-lib" transform="translate(168.6,0) scale(.95,1)">'
    '<path d="M9.73 98.7C9.73 97.59 9.62 96.19 9.93 94.49C11.53 83.36 16.84 53.78 20.25 '
    '39.24C23.06 28.41 24.16 23 17.55 23C12.93 23 9.22 25.51 9.22 25.51L8.72 27.31C11.53 '
    '27.71 12.73 30.72 11.73 36.33C11.73 36.33 5.01 72.33 0.2 97.19L0 98.7ZM37.6 34.43C37.5 '
    '37.24 39.8 39.84 42.71 39.84C45.52 39.84 47.92 37.24 48.02 34.43C48.02 31.62 45.72 29.22 '
    '42.91 29.22C40 29.22 37.6 31.62 37.6 34.43ZM27.57 98.7H37.3C37.4 98.1 37.4 97.49 '
    '37.4 96.89C37.4 95.19 37.6 93.28 38 91.18C39.8 80.55 41.91 67.32 42.71 63.2C43.01 '
    '61.5 44.92 54.88 44.92 52.78C45.02 50.17 43.91 48.07 41.21 48.07C37.2 48.07 32.68 50.67 '
    '30.58 53.18L31.48 54.78C31.78 54.68 31.98 54.68 32.28 54.68C33.79 54.68 35.09 55.79 '
    '34.99 58.29C34.99 58.79 34.99 59.9 27.67 98.3ZM66.97 36.33C66.47 42.45 57.15 86.06 57.15 '
    '91.08C57.15 97.19 63.67 100 71.89 100C90.43 100 99.96 79.95 99.96 64.81C99.96 53.18 '
    '96.45 47.66 89.93 47.66C83.62 47.66 75.7 52.78 70.48 60.8C73.69 49.67 77.7 32.73 77.8 '
    '27.81C77.8 24.6 76.5 23 72.79 23C68.18 23 64.47 25.51 64.47 25.51L64.07 27.31C66.57 '
    '27.41 67.17 30.22 67.17 33.03C67.17 34.23 67.07 35.33 66.97 36.33ZM67.17 83.76C68.08 '
    '77.44 68.08 76.54 70.18 64.71C74.39 59.29 80.91 54.38 84.72 54.38C89.23 54.38 90.74 59.49 '
    '90.74 66.01C90.74 77.94 86.52 94.49 73.99 94.49C68.18 94.49 66.87 91.98 66.87 88.17C66.87 '
    '86.87 66.97 85.36 67.17 83.76Z" fill="currentColor" '
    'stroke="var(--wordmark-cutout, #ffffff)" stroke-width="1.5" stroke-linejoin="round"/></g>'
)


def load_wordmark_svg(repo_root: Path, css_class: str = "brand-wordmark") -> str:
    """Extract Z-QL03 wordmark SVG from .github/assets/qatlib-wordmark.svg with adaptive cutout."""
    for rel in [".github/assets/qatlib-wordmark.svg", "docs/qatlib-logo.svg"]:
        candidate = repo_root / rel
        if candidate.is_file():
            raw = candidate.read_text(encoding="utf-8")
            m = re.search(r'(<g id="wordmark"[\s\S]*)</svg>', raw)
            if m:
                inner = m.group(1).strip()
                inner = re.sub(
                    r'stroke="#[0-9A-Fa-f]{6}"',
                    'stroke="var(--wordmark-cutout, #ffffff)"',
                    inner,
                )
                inner = re.sub(r'fill="#[0-9A-Fa-f]{6}"', 'fill="currentColor"', inner)
                inner = re.sub(r'^<g id="wordmark"\s+transform="[^"]*"', '<g id="wordmark"', inner, count=1)
                return (
                    f'<svg class="{css_class}" xmlns="http://www.w3.org/2000/svg" '
                    f'viewBox="3 15 264 97" role="img" aria-label="Qatlib">{inner}</svg>'
                )
    return (
        f'<svg class="{css_class}" xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="3 15 264 97" role="img" aria-label="Qatlib">'
        f'<g id="wordmark">{FALLBACK_WORDMARK_INNER}</g></svg>'
    )


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

    # Map canonical repo Markdown guides to portal HTML pages
    guide_map_en = {
        "README.en.md": f"{root_prefix}index.html",
        "README.md": f"{root_prefix}zh/index.html",
        "docs/getting-started.en.md": f"{root_prefix}getting-started.html",
        "docs/getting-started.md": f"{root_prefix}zh/getting-started.html",
        "docs/architecture.en.md": f"{root_prefix}architecture.html",
        "docs/architecture.md": f"{root_prefix}zh/architecture.html",
        "CONTRIBUTING.en.md": f"{root_prefix}contributing.html",
        "CONTRIBUTING.md": f"{root_prefix}zh/contributing.html",
        "scripts/README.en.md": f"{root_prefix}architecture.html#tooling",
        "scripts/README.md": f"{root_prefix}architecture.html#tooling",
    }
    guide_map_zh = {
        "README.md": f"{root_prefix}zh/index.html",
        "README.en.md": f"{root_prefix}index.html",
        "docs/getting-started.md": f"{root_prefix}zh/getting-started.html",
        "docs/getting-started.en.md": f"{root_prefix}getting-started.html",
        "docs/architecture.md": f"{root_prefix}zh/architecture.html",
        "docs/architecture.en.md": f"{root_prefix}architecture.html",
        "CONTRIBUTING.md": f"{root_prefix}zh/contributing.html",
        "CONTRIBUTING.en.md": f"{root_prefix}contributing.html",
        "scripts/README.md": f"{root_prefix}zh/architecture.html#tooling",
        "scripts/README.en.md": f"{root_prefix}architecture.html#tooling",
    }
    gmap = guide_map_zh if lang == "zh" else guide_map_en
    if resolved in gmap:
        target = gmap[resolved]
        if "#" in target and anchor:
            return target
        return target + anchor

    # Map Qatlib directory links to Module Explorer / API Reference
    mod_page = f"{root_prefix}zh/modules.html" if lang == "zh" else f"{root_prefix}modules.html"
    if resolved == "Qatlib":
        return mod_page
    if resolved in ("Qatlib/Foundations", "Qatlib/Concepts", "Qatlib/Papers"):
        layer = resolved.split("/", 1)[1]
        return f"{mod_page}?layer={layer}"
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
) -> tuple[str, str, list[dict[str, Any]]]:
    """Render a repo Markdown file into enhanced HTML + extract (title, html, toc)."""
    raw = md_path.read_text(encoding="utf-8")
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
    copy_label = "复制" if lang == "zh" else "Copy"

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
    """Extract the 8 thematic research areas table and BibTeX snippet directly from README."""
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
  --wordmark-cutout: #ffffff;
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
  --font-sans: Inter, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "PingFang SC", "Hiragino Sans GB", "Noto Sans CJK SC", "Microsoft YaHei", sans-serif;
  --font-mono: "JetBrains Mono", "Fira Code", ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
  --nav-h: 64px;
}

[data-theme="dark"] {
  --bg: #0c121d;
  --bg-elevated: #131c2b;
  --bg-subtle: #192538;
  --bg-code: #090e17;
  --wordmark-cutout: #131c2b;
  --fg: #e6edf7;
  --fg-muted: #9cb0c9;
  --fg-faint: #6c819c;
  --border: #223147;
  --border-strong: #314663;
  --brand: #8cb6eb;
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

/* Sticky Top Navigation */
.site-header {
  position: sticky;
  top: 0;
  z-index: 100;
  height: var(--nav-h);
  background: color-mix(in srgb, var(--bg-elevated) 88%, transparent);
  backdrop-filter: blur(12px);
  -webkit-backdrop-filter: blur(12px);
  border-bottom: 1px solid var(--border);
}
.nav-inner {
  max-width: 1280px;
  height: 100%;
  margin: 0 auto;
  padding: 0 24px;
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 16px;
}
.brand-link {
  display: inline-flex;
  align-items: center;
  gap: 10px;
  color: var(--brand);
  font-weight: 700;
}
.brand-link:hover { opacity: 0.88; }
.nav-wordmark { height: 26px; width: auto; display: block; }
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
  padding: 6px 12px;
  border-radius: var(--radius-sm);
  color: var(--fg-muted);
  font-size: 14.5px;
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
}
.nav-search-form {
  position: relative;
  display: flex;
  align-items: center;
}
.nav-search-input {
  width: 200px;
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
  width: 240px;
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

.icon-btn, .lang-switch {
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
.icon-btn:hover, .lang-switch:hover {
  color: var(--fg);
  border-color: var(--border-strong);
  background: var(--bg-subtle);
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
  height: 60px;
  width: auto;
  color: var(--brand);
  margin-bottom: 16px;
  display: block;
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
  margin-bottom: 24px;
}
.btn {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  padding: 10px 18px;
  border-radius: var(--radius-sm);
  font-size: 14.5px;
  font-weight: 600;
  border: 1px solid transparent;
  cursor: pointer;
  transition: all 0.15s ease;
}
.btn-primary {
  background: #263f5f;
  color: #ffffff;
}
.btn-primary:hover { background: #1c304a; color: #ffffff; }
[data-theme="dark"] .btn-primary {
  background: #8cb6eb;
  color: #0b1320;
}
[data-theme="dark"] .btn-primary:hover { background: #a8caf4; color: #0b1320; }
.btn-secondary {
  background: var(--bg);
  color: var(--fg);
  border-color: var(--border-strong);
}
.btn-secondary:hover {
  background: var(--bg-subtle);
  border-color: var(--brand);
  color: var(--brand);
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
.bib-title { margin: 0 0 4px; font-size: 16.5px; font-weight: 650; color: var(--fg); }
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
  padding: 36px 24px;
  font-size: 13.5px;
  color: var(--fg-muted);
}
.footer-inner {
  max-width: 1160px;
  margin: 0 auto;
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: 16px;
}
.footer-links {
  display: flex;
  flex-wrap: wrap;
  gap: 18px;
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

@media (max-width: 1180px) {
  .nav-links a { padding: 6px 9px; font-size: 13.8px; }
  .nav-search-input { width: 165px; }
  .nav-search-input:focus { width: 195px; }
}

@media (max-width: 1024px) {
  .hero-inner { grid-template-columns: 1fr; }
  .metrics-strip { grid-template-columns: repeat(3, 1fr); }
  .layers-grid { grid-template-columns: 1fr; }
  .docs-shell { grid-template-columns: 200px minmax(0, 1fr); }
  .docs-toc { display: none; }
  .nav-search-form { display: none; }
}

@media (max-width: 760px) {
  .mobile-menu-btn { display: inline-flex; }
  .nav-links {
    display: none;
    position: absolute;
    top: var(--nav-h);
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
  const isZh = (root.getAttribute("lang") || "").startsWith("zh");
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
    themeBtn.setAttribute(
      "title",
      isZh
        ? (isDark ? "切换为浅色模式" : "切换为深色模式")
        : (isDark ? "Switch to light mode" : "Switch to dark mode")
    );
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
  if (menuBtn && navLinks) {
    menuBtn.addEventListener("click", () => navLinks.classList.toggle("open"));
  }

  // '/' shortcut focuses search box
  document.addEventListener("keydown", (e) => {
    if (e.key === "/" && !["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement?.tagName || "")) {
      const target = document.getElementById("explorer-search") || document.querySelector(".nav-search-input");
      if (target) {
        e.preventDefault();
        target.focus();
      }
    }
  });

  // Quickstart tabs
  document.querySelectorAll(".qs-tab").forEach((tab) => {
    tab.addEventListener("click", () => {
      const group = tab.closest(".quickstart-card");
      if (!group) return;
      const targetId = tab.getAttribute("data-tab");
      group.querySelectorAll(".qs-tab").forEach((t) => t.classList.toggle("active", t === tab));
      group.querySelectorAll(".qs-panel").forEach((p) => p.classList.toggle("active", p.id === targetId));
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

    const params = new URLSearchParams(window.location.search);
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
      window.location.href = q ? `${target}?q=${encodeURIComponent(q)}` : target;
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

UI_STRINGS = {
    "en": {
        "html_lang": "en",
        "site_tagline": "The Lean 4 Library for Formalized Quantum Computing & Quantum Information",
        "nav_overview": "Overview",
        "nav_getting_started": "Getting Started",
        "nav_architecture": "Architecture",
        "nav_modules": "Modules",
        "nav_papers": "Bibliography",
        "nav_contributing": "Contributing",
        "nav_api": "API Docs ↗",
        "search_placeholder": "Search API declarations…",
        "switch_lang_label": "中文",
        "switch_lang_title": "切换到中文页面",
        "brand_home_label": "Qatlib Home",
        "theme_toggle_label": "Toggle color theme",
        "github_title": "GitHub Repository",
        "menu_label": "Menu",
        "back_to_top_label": "Back to top",
        "guides_heading": "Documentation",
        "api_group_heading": "API Reference",
        "toc_heading": "On this page",
        "edit_on_github": "View source on GitHub ↗",
        "footer_api": "API Reference (doc-gen4)",
        "footer_refs": "API Bibliography",
        "footer_note": "Built on Lean 4, Mathlib, and Physlib · Released under the Apache-2.0 License.",
    },
    "zh": {
        "html_lang": "zh-CN",
        "site_tagline": "基于 Lean 4 的量子计算与量子信息形式化数学库",
        "nav_overview": "首页",
        "nav_getting_started": "快速开始",
        "nav_architecture": "库架构",
        "nav_modules": "模块导览",
        "nav_papers": "文献索引",
        "nav_contributing": "参与贡献",
        "nav_api": "API 文档 ↗",
        "search_placeholder": "搜索 API 声明…",
        "switch_lang_label": "EN",
        "switch_lang_title": "Switch to English",
        "brand_home_label": "Qatlib 首页",
        "theme_toggle_label": "切换浅色/深色主题",
        "github_title": "GitHub 代码仓库",
        "menu_label": "导航菜单",
        "back_to_top_label": "回到顶部",
        "guides_heading": "文档导航",
        "api_group_heading": "API 参考文档",
        "toc_heading": "本页目录",
        "edit_on_github": "在 GitHub 查看源码 ↗",
        "footer_api": "API 文档 (doc-gen4)",
        "footer_refs": "API 文献页",
        "footer_note": "构建于 Lean 4、Mathlib 与 Physlib 之上 · 采用 Apache-2.0 开源协议发布。",
    },
}


def render_page_shell(
    *,
    title: str,
    lang: str,
    page_slug: str,
    root_prefix: str,
    toolchain_tag: str,
    wordmark_nav: str,
    body_html: str,
) -> str:
    t = UI_STRINGS[lang]
    page_prefix = f"{root_prefix}zh/" if lang == "zh" else root_prefix
    alt_prefix = root_prefix if lang == "zh" else f"{root_prefix}zh/"
    alt_href = f"{alt_prefix}{page_slug}"
    docs_prefix = f"{root_prefix}docs/"

    def nav_cls(slug: str) -> str:
        return ' class="active"' if slug == page_slug else ""

    full_title = f"{title} — Qatlib" if title != "Qatlib" else f"Qatlib · {t['site_tagline']}"
    return f"""<!DOCTYPE html>
<html lang="{t['html_lang']}">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(full_title)}</title>
  <meta name="description" content="{html.escape(t['site_tagline'])}">
  <link rel="stylesheet" href="{root_prefix}assets/style.css">
  <script src="{root_prefix}assets/theme-init.js"></script>
</head>
<body>
  <header class="site-header">
    <div class="nav-inner">
      <div style="display:flex;align-items:center;gap:10px;">
        <a class="brand-link" href="{page_prefix}index.html" aria-label="{t['brand_home_label']}">
          {wordmark_nav}
        </a>
        <span class="toolchain-pill">Lean {html.escape(toolchain_tag)}</span>
      </div>

      <nav id="nav-links" class="nav-links" aria-label="Primary">
        <a href="{page_prefix}index.html"{nav_cls("index.html")}>{t["nav_overview"]}</a>
        <a href="{page_prefix}getting-started.html"{nav_cls("getting-started.html")}>{t["nav_getting_started"]}</a>
        <a href="{page_prefix}architecture.html"{nav_cls("architecture.html")}>{t["nav_architecture"]}</a>
        <a href="{page_prefix}modules.html"{nav_cls("modules.html")}>{t["nav_modules"]}</a>
        <a href="{page_prefix}papers.html"{nav_cls("papers.html")}>{t["nav_papers"]}</a>
        <a href="{page_prefix}contributing.html"{nav_cls("contributing.html")}>{t["nav_contributing"]}</a>
        <a href="{docs_prefix}index.html" class="nav-api-btn">{t["nav_api"]}</a>
      </nav>

      <div class="nav-actions">
        <form class="nav-search-form" action="{docs_prefix}search.html" method="get">
          <input class="nav-search-input" type="search" name="q" placeholder="{t['search_placeholder']}" autocomplete="off">
          <span class="nav-search-kbd">/</span>
        </form>
        <a class="lang-switch" href="{alt_href}" title="{t['switch_lang_title']}">{t["switch_lang_label"]}</a>
        <button id="theme-toggle" class="icon-btn" type="button" aria-label="{t['theme_toggle_label']}">☾</button>
        <a class="icon-btn" href="{GITHUB_REPO_URL}" target="_blank" rel="noopener" title="{t['github_title']}" aria-label="GitHub">
          <svg width="17" height="17" viewBox="0 0 16 16" fill="currentColor" aria-hidden="true">
            <path d="M8 0C3.58 0 0 3.58 0 8a8 8 0 0 0 5.47 7.59c.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82a7.65 7.65 0 0 1 4 0c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0 0 16 8c0-4.42-3.58-8-8-8Z"/>
          </svg>
        </a>
        <button id="mobile-menu-btn" class="icon-btn mobile-menu-btn" type="button" aria-label="{t['menu_label']}">☰</button>
      </div>
    </div>
  </header>

  {body_html}

  <footer class="site-footer">
    <div class="footer-inner">
      <div>{t["footer_note"]}</div>
      <div class="footer-links">
        <a href="{page_prefix}getting-started.html">{t["nav_getting_started"]}</a>
        <a href="{page_prefix}architecture.html">{t["nav_architecture"]}</a>
        <a href="{page_prefix}modules.html">{t["nav_modules"]}</a>
        <a href="{page_prefix}papers.html">{t["nav_papers"]}</a>
        <a href="{docs_prefix}index.html">{t["footer_api"]}</a>
        <a href="{docs_prefix}references.html">{t["footer_refs"]}</a>
        <a href="{GITHUB_REPO_URL}" target="_blank" rel="noopener">GitHub</a>
      </div>
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
    t = UI_STRINGS[lang]
    page_prefix = f"{root_prefix}zh/" if lang == "zh" else root_prefix
    docs_prefix = f"{root_prefix}docs/"

    nav_items = [
        ("index.html", t["nav_overview"]),
        ("getting-started.html", t["nav_getting_started"]),
        ("architecture.html", t["nav_architecture"]),
        ("modules.html", t["nav_modules"]),
        ("papers.html", t["nav_papers"]),
        ("contributing.html", t["nav_contributing"]),
    ]
    sidebar_lis = "\n".join(
        f'<li><a href="{page_prefix}{slug}"{" class=\"active\"" if slug == page_slug else ""}>{label}</a></li>'
        for slug, label in nav_items
    )

    api_links = (
        [
            (f"{docs_prefix}index.html", "API Reference Home ↗"),
            (f"{docs_prefix}Qatlib.html", "Qatlib Umbrella ↗"),
            (f"{docs_prefix}references.html", "API Bibliography ↗"),
            (f"{docs_prefix}tactics.html", "Tactics Index ↗"),
        ]
        if lang == "en"
        else [
            (f"{docs_prefix}index.html", "API 文档主页 ↗"),
            (f"{docs_prefix}Qatlib.html", "Qatlib 总入口模块 ↗"),
            (f"{docs_prefix}references.html", "API 文献引用页 ↗"),
            (f"{docs_prefix}tactics.html", "证明策略索引 ↗"),
        ]
    )
    api_lis = "\n".join(f'<li><a href="{href}">{label}</a></li>' for href, label in api_links)

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
) -> str:
    page_prefix = f"{root_prefix}zh/" if lang == "zh" else root_prefix
    docs_prefix = f"{root_prefix}docs/"
    layers = tree_stats["layers"]
    total_mods = f"{tree_stats['total_modules']:,}"
    f_mods = f"{layers['Foundations']['module_count']:,}"
    c_mods = f"{layers['Concepts']['module_count']:,}"
    p_mods = f"{layers['Papers']['module_count']:,}"
    p_dirs = f"{layers['Papers']['dir_count']:,}"
    copy_lbl = "复制" if lang == "zh" else "Copy"

    dep_toml = html.escape(
        '[[require]]\nname = "Qatlib"\n'
        'git = "https://github.com/quantum-atlas-ai/qatlib.git"\nrev = "main"'
    )
    dep_sh = "lake update\nlake exe get_cache"
    dev_sh = (
        "git clone https://github.com/quantum-atlas-ai/qatlib.git\n"
        "cd qatlib\n"
        "lake exe get_cache\n"
        "lake build Qatlib.Papers.GroverSearch96.MainResults.GainConvergence"
    )

    if lang == "en":
        eyebrow = "Kernel-Verified · 0 sorryAx · Standard Axioms Only"
        h1 = "The Lean 4 Library for Quantum Computing & Quantum Information"
        lead = (
            "Built on top of Mathlib and Physlib, Qatlib provides unified operator-algebraic "
            "foundations, reusable quantum algorithmic frameworks, and formalized theorems and "
            "resource complexity analyses from the quantum computing literature."
        )
        cta_start = "Get Started"
        cta_api = "API Reference (doc-gen4)"
        cta_mods = "Explore Modules"
        cta_papers = f"Bibliography ({bib_count})"
        tab1, tab2 = "Use as Dependency", "Clone & Develop"
        cap1 = f"Add to lakefile.toml (Lean {toolchain_tag}), then pull prebuilt Mathlib + Physlib + Qatlib caches:"
        cap2 = "Fetch all three cache tiers in one command and build incrementally:"
        metrics = [
            (total_mods, "Lean 4 Modules"),
            (p_dirs, "Paper Directories"),
            (f"{bib_count:,}", "Curated References"),
            ("0", "sorryAx / Custom Axioms"),
            (toolchain_tag, "Pinned Toolchain"),
        ]
        sec_arch_eye = "Three-Layer Architecture"
        sec_arch_h2 = "Strict One-Way Dependency: Foundations ← Concepts ← Papers"
        sec_arch_p = (
            "Enforced statically in ~1 second by lake lint and audited in the Lean 4 kernel by lake test."
        )
        layer_cards = [
            (
                "foundations",
                "Qatlib/Foundations",
                f"{layers['Foundations']['dir_count']} dirs · {f_mods} modules",
                "Foundations",
                "Shared operator analysis, trace & Schatten norms, positive semidefinite order, mixed-state fidelity, concentration bounds, graph Laplacians, and finite-precision arithmetic.",
                f"{page_prefix}modules.html?layer=Foundations",
                "Browse Foundations →",
            ),
            (
                "concepts",
                "Qatlib/Concepts",
                f"{layers['Concepts']['dir_count']} dirs · {c_mods} modules",
                "Concepts",
                "Reusable quantum channels & entropy, block-encoding algebra, QSVT/QSP, LCU, amplitude amplification, quantum walks, query/adversary bounds, fermionic/bosonic spaces, and QEC.",
                f"{page_prefix}modules.html?layer=Concepts",
                "Browse Concepts →",
            ),
            (
                "papers",
                "Qatlib/Papers",
                f"{p_dirs} dirs · {p_mods} modules",
                "Papers",
                "Selected model definitions, technical lemmas, main theorems (MainResults/), and end-to-end query/gate/qubit resource bounds organized by research paper.",
                f"{page_prefix}modules.html?layer=Papers",
                "Browse Papers →",
            ),
        ]
        sec_area_eye = "Thematic Coverage"
        sec_area_h2 = "Eight Interconnected Research Areas"
        sec_area_p = "Click any representative directory below to inspect its Lean modules and jump directly into doc-gen4 API documentation."
        sec_cite_eye = "Citation & Open Source"
        sec_cite_h2 = "Citing Qatlib"
        sec_cite_p = "Qatlib is released under the Apache License 2.0. If you use Qatlib in your research, please cite:"
    else:
        eyebrow = "Lean 4 内核级验证 · 零 sorryAx · 仅依赖标准公理"
        h1 = "基于 Lean 4 的量子计算与量子信息形式化数学库"
        lead = (
            "构建于 mathlib4 与 Physlib 之上，Qatlib 用统一的算子代数与执行语义接口，"
            "对量子计算基础数学结构、可复用算法原语以及学术文献中的核心定理与资源复杂度界进行形式化。"
        )
        cta_start = "快速开始"
        cta_api = "API 参考文档 (doc-gen4)"
        cta_mods = "模块导览"
        cta_papers = f"文献索引 ({bib_count})"
        tab1, tab2 = "作为下游依赖引入", "克隆与本地开发"
        cap1 = f"在 lakefile.toml（工具链 {toolchain_tag}）中添加依赖，一键拉取三层预编译缓存："
        cap2 = "无需从零编译全库，拉取 Mathlib + Physlib + Qatlib 缓存后按需增量构建："
        metrics = [
            (total_mods, "Lean 4 形式化模块"),
            (p_dirs, "形式化论文目录"),
            (f"{bib_count:,}", "权威文献条目"),
            ("0", "sorryAx / 自定义公理"),
            (toolchain_tag, "锁定工具链基线"),
        ]
        sec_arch_eye = "三层单向架构"
        sec_arch_h2 = "严格单向依赖：Foundations ← Concepts ← Papers"
        sec_arch_p = "由 lake lint 秒级静态校验分层与导入规范，并由 lake test 调用 Lean 4 内核验证全库公理闭包。"
        layer_cards = [
            (
                "foundations",
                "Qatlib/Foundations",
                f"{layers['Foundations']['dir_count']} 子目录 · {f_mods} 模块",
                "Foundations（基础层）",
                "共享矩阵分析、算子范数与 Schatten 范数、正半定序与混合态保真度、集中不等式、图拉普拉斯算子、有限精度算术与数值误差传播。",
                f"{page_prefix}modules.html?layer=Foundations",
                "浏览 Foundations →",
            ),
            (
                "concepts",
                "Qatlib/Concepts",
                f"{layers['Concepts']['dir_count']} 子目录 · {c_mods} 模块",
                "Concepts（概念与原语层）",
                "量子信道与量子熵、块编码代数、QSVT/QSP、LCU、振幅放大与估计、量子游走、多项式与对手下界、费米子/玻色子代数、量子纠错与资源记账。",
                f"{page_prefix}modules.html?layer=Concepts",
                "浏览 Concepts →",
            ),
            (
                "papers",
                "Qatlib/Papers",
                f"{p_dirs} 子目录 · {p_mods} 模块",
                "Papers（学术文献层）",
                "基于公共数学接口，按代表性论文目录组织模型定义、专题引理、核心结论定理（MainResults/）与端到端资源复杂度分析。",
                f"{page_prefix}modules.html?layer=Papers",
                "浏览 Papers →",
            ),
        ]
        sec_area_eye = "研究主题导航"
        sec_area_h2 = "八大交叉研究领域"
        sec_area_p = "点击下方任意代表性子目录标签，即可查看该目录包含的模块列表并直达 doc-gen4 API 文档。"
        sec_cite_eye = "引用与开源协议"
        sec_cite_h2 = "引用 Qatlib"
        sec_cite_p = "Qatlib 采用 Apache License 2.0 协议开源。如果你在研究中使用了本项目，欢迎引用："

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

    return f"""
  <section class="hero">
    <div class="hero-inner">
      <div>
        <div class="hero-eyebrow">✓ {html.escape(eyebrow)}</div>
        {wordmark_hero}
        <h1>{html.escape(h1)}</h1>
        <p class="hero-lead">{html.escape(lead)}</p>
        <div class="hero-ctas">
          <a class="btn btn-primary" href="{page_prefix}getting-started.html">{html.escape(cta_start)} →</a>
          <a class="btn btn-secondary" href="{docs_prefix}index.html">{html.escape(cta_api)}</a>
          <a class="btn btn-secondary" href="{page_prefix}modules.html">{html.escape(cta_mods)}</a>
          <a class="btn btn-secondary" href="{page_prefix}papers.html">{html.escape(cta_papers)}</a>
        </div>
      </div>

      <div class="quickstart-card">
        <div class="qs-tabs">
          <button type="button" class="qs-tab active" data-tab="qs-dep">{html.escape(tab1)}</button>
          <button type="button" class="qs-tab" data-tab="qs-dev">{html.escape(tab2)}</button>
        </div>
        <div id="qs-dep" class="qs-panel active">
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
        <div id="qs-dev" class="qs-panel">
          <p class="qs-caption">{html.escape(cap2)}</p>
          <div class="code-card" style="margin-bottom:0;">
            <div class="code-card-header"><span class="code-lang">BASH</span>
              <button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>
            <pre><code>{dev_sh}</code></pre>
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
      <div class="section-eyebrow">{html.escape(sec_arch_eye)}</div>
      <h2>{html.escape(sec_arch_h2)}</h2>
      <p>{html.escape(sec_arch_p)}</p>
    </div>
    <div class="layers-grid">
      {layers_html}
    </div>
  </section>

  <section class="section">
    <div class="section-header">
      <div class="section-eyebrow">{html.escape(sec_area_eye)}</div>
      <h2>{html.escape(sec_area_h2)}</h2>
      <p>{html.escape(sec_area_p)}</p>
    </div>
    <div class="areas-grid">
      {"".join(area_cards_html)}
    </div>
  </section>

  <section class="section">
    <div class="section-header">
      <div class="section-eyebrow">{html.escape(sec_cite_eye)}</div>
      <h2>{html.escape(sec_cite_h2)}</h2>
      <p>{html.escape(sec_cite_p)}</p>
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
    page_prefix = f"{root_prefix}zh/" if lang == "zh" else root_prefix
    docs_prefix = f"{root_prefix}docs/"
    layers = tree_stats["layers"]
    dirs = tree_stats["dirs"]

    if lang == "en":
        h1 = "Module Explorer"
        lead = (
            f"Browse all {tree_stats['total_dirs']:,} topic and paper directories "
            f"({tree_stats['total_modules']:,} Lean 4 modules) across Foundations, Concepts, and Papers. "
            "Every card links directly to doc-gen4 API documentation and GitHub source."
        )
        placeholder = "Filter by directory name, topic, theorem keyword, or [Citekey] (press / to focus)…"
        lbl_all = f"All ({tree_stats['total_dirs']})"
        lbl_f = f"Foundations ({layers['Foundations']['dir_count']})"
        lbl_c = f"Concepts ({layers['Concepts']['dir_count']})"
        lbl_p = f"Papers ({layers['Papers']['dir_count']})"
        layer_display = {
            "Foundations": "Foundations",
            "Concepts": "Concepts",
            "Papers": "Papers",
        }
        status_tpl = "Showing {shown} of {total} directories"
        api_lbl = "Entry API Docs →"
        dir_api_lbl = "Directory Index"
        gh_lbl = "GitHub ↗"
        expand_lbl = "Key modules"
        mod_unit = "modules"
    else:
        h1 = "模块导览"
        lead = (
            f"检索与浏览全库 {tree_stats['total_dirs']:,} 个主题与论文子目录（共 {tree_stats['total_modules']:,} 个 Lean 4 模块；"
            "目录标题与摘要实时提取自 .lean 源码模块文档），一键直达 doc-gen4 API 文档与 GitHub 源码目录。"
        )
        placeholder = "按目录名、数学主题、关键词或文献 [Citekey] 实时筛选（按 / 聚焦）…"
        lbl_all = f"全部 ({tree_stats['total_dirs']})"
        lbl_f = f"Foundations · 基础层 ({layers['Foundations']['dir_count']})"
        lbl_c = f"Concepts · 概念层 ({layers['Concepts']['dir_count']})"
        lbl_p = f"Papers · 论文层 ({layers['Papers']['dir_count']})"
        layer_display = {
            "Foundations": "Foundations · 基础层",
            "Concepts": "Concepts · 概念层",
            "Papers": "Papers · 论文层",
        }
        status_tpl = "当前显示 {shown} / {total} 个子目录"
        api_lbl = "入口 API 文档 →"
        dir_api_lbl = "目录索引"
        gh_lbl = "GitHub 源码 ↗"
        expand_lbl = "代表性模块"
        mod_unit = "个模块"

    cards_html: list[str] = []
    for d in dirs:
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
            f'<span class="mod-count">{d["module_count"]} {mod_unit}</span>'
            f"</div>"
            f'<h2 class="mod-name">{html.escape(d["name"])}</h2>'
            f"{subtitle_el}{desc_el}{cite_row}"
            f'<details class="mod-details"><summary>{expand_lbl} ({len(d["featured_mods"])})</summary>'
            f'<ul class="mod-leaf-list">{leaf_lis}</ul></details>'
            f'<div class="mod-actions">'
            f'<a href="{docs_prefix}{d["entry_html"]}">{api_lbl}</a>'
            f'<a href="{docs_prefix}{d["rel_dir"]}/index.html">{dir_api_lbl}</a>'
            f'<a href="{GITHUB_REPO_URL}/tree/main/{d["rel_dir"]}" target="_blank" rel="noopener">{gh_lbl}</a>'
            f"</div></article>"
        )

    return f"""
  <main class="explorer-wrap">
    <div class="section-header" style="margin-bottom:16px;">
      <div class="section-eyebrow">Qatlib/{'{'}Foundations, Concepts, Papers{'}'}</div>
      <h1 style="margin:0 0 8px;font-size:30px;">{html.escape(h1)}</h1>
      <p>{html.escape(lead)}</p>
    </div>

    <div class="explorer-toolbar">
      <input id="explorer-search" class="filter-input" type="search" placeholder="{html.escape(placeholder)}" autocomplete="off">
      <div class="filter-pills">
        <button type="button" class="filter-pill active" data-layer-filter="all">{html.escape(lbl_all)}</button>
        <button type="button" class="filter-pill" data-layer-filter="Foundations">{html.escape(lbl_f)}</button>
        <button type="button" class="filter-pill" data-layer-filter="Concepts">{html.escape(lbl_c)}</button>
        <button type="button" class="filter-pill" data-layer-filter="Papers">{html.escape(lbl_p)}</button>
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
) -> str:
    page_prefix = f"{root_prefix}zh/" if lang == "zh" else root_prefix
    docs_prefix = f"{root_prefix}docs/"
    copy_lbl = "复制" if lang == "zh" else "Copy"

    if lang == "en":
        h1 = "Papers & Bibliography"
        lead = (
            f"Search all {len(bib_entries):,} authoritative books, foundational papers, and preprints "
            f"in docs/references.bib across {len(bib_sections)} subject chapters, with direct cross-links "
            "to Qatlib formalization directories."
        )
        placeholder = "Search by author, title, year, citekey, arXiv ID, or Qatlib module…"
        all_chap = f"All {len(bib_sections)} Subject Chapters ({len(bib_entries)})"
        only_form_lbl = "Linked to Qatlib modules only"
        status_tpl = "Showing {shown} of {total} references"
        raw_lbl = "BibTeX"
        form_prefix = "Formalized / cited in:"
    else:
        h1 = "文献与参考书目索引"
        lead = (
            f"检索 docs/references.bib 收录的全部 {len(bib_entries):,} 篇权威专著与学术论文（按 {len(bib_sections)} 个学科章节分类），"
            "并直接跳转到对应的 Qatlib 形式化模块。"
        )
        placeholder = "按作者、论文标题、年份、Citekey、arXiv 编号或 Qatlib 模块名搜索…"
        all_chap = f"全部 {len(bib_sections)} 个学科章节 ({len(bib_entries)})"
        only_form_lbl = "仅显示已关联 Qatlib 模块的文献"
        status_tpl = "当前显示 {shown} / {total} 篇文献"
        raw_lbl = "BibTeX"
        form_prefix = "关联 Qatlib 模块："

    def sec_label(sec_id: str, en_title: str) -> str:
        if lang == "zh":
            return BIB_SECTION_TITLES_ZH.get(sec_id, en_title)
        return en_title

    select_aria = "Filter by subject chapter" if lang == "en" else "按学科章节筛选"
    docgen_badge_lbl = "doc-gen4 ↗" if lang == "en" else "API 引用 ↗"

    options_html = [f'<option value="all">{html.escape(all_chap)}</option>']
    for sec in bib_sections:
        options_html.append(
            f'<option value="{html.escape(sec["id"])}">'
            f'{html.escape(sec["id"])}. {html.escape(sec_label(sec["id"], sec["title"]))} ({sec["count"]})</option>'
        )

    cards_html: list[str] = []
    for ent in bib_entries:
        linked_dirs = ent["cited_by_dirs"] or ent["section_related"]
        has_direct = "1" if ent["cited_by_dirs"] else "0"
        venue_parts = [p for p in [ent["venue"], f'vol. {ent["volume"]}' if ent["volume"] else "", ent["year"]] if p]
        venue_line = ", ".join(venue_parts)
        chap_zh = BIB_SECTION_TITLES_ZH.get(ent["section_id"], "")
        chap_disp = sec_label(ent["section_id"], ent["section_title"])
        search_blob = " ".join(
            [
                ent["key"],
                ent["title"],
                ent["authors"],
                venue_line,
                ent["section_title"],
                chap_zh,
                ent["eprint"],
                ent["doi"],
                " ".join(linked_dirs),
            ]
        ).lower()

        ext_links: list[str] = []
        if ent["doi"]:
            ext_links.append(
                f'<a class="bib-ext-badge" href="https://doi.org/{html.escape(ent["doi"])}" '
                f'target="_blank" rel="noopener">DOI ↗</a>'
            )
        if ent["eprint"]:
            ext_links.append(
                f'<a class="bib-ext-badge" href="https://arxiv.org/abs/{html.escape(ent["eprint"])}" '
                f'target="_blank" rel="noopener">arXiv:{html.escape(ent["eprint"])} ↗</a>'
            )
        elif ent["url"] and not ent["doi"]:
            ext_links.append(
                f'<a class="bib-ext-badge" href="{html.escape(ent["url"])}" '
                f'target="_blank" rel="noopener">URL ↗</a>'
            )
        ext_links.append(
            f'<a class="bib-ext-badge" href="{docs_prefix}references.html#{html.escape(ent["key"])}">{docgen_badge_lbl}</a>'
        )

        dir_chips = ""
        if ent["cited_by_dirs"]:
            chips = "".join(
                f'<a class="dir-chip" href="{page_prefix}modules.html#{html.escape(d)}">'
                f'{html.escape(d.removeprefix("Qatlib/"))}</a>'
                for d in ent["cited_by_dirs"][:6]
            )
            dir_chips = (
                f'<div class="chip-list" style="margin-top:8px;align-items:center;">'
                f'<span style="font-size:12px;color:var(--fg-faint);">{form_prefix}</span>{chips}</div>'
            )

        cards_html.append(
            f'<article id="{html.escape(ent["key"])}" class="bib-card" '
            f'data-section="{html.escape(ent["section_id"])}" data-formalized="{has_direct}" '
            f'data-search="{html.escape(search_blob)}">'
            f'<div class="bib-meta-top">'
            f'<a class="bib-key" href="#{html.escape(ent["key"])}">[{html.escape(ent["key"])}]</a>'
            f'<span class="bib-chapter">{html.escape(ent["section_id"])}. {html.escape(chap_disp)}</span>'
            f"</div>"
            f'<h2 class="bib-title">{html.escape(ent["title"])}</h2>'
            f'<p class="bib-authors">{html.escape(ent["authors"])}</p>'
            f'<p class="bib-venue">{html.escape(venue_line)}</p>'
            f'<div class="bib-links">{"".join(ext_links)}'
            f'<details class="bib-raw-details"><summary>{raw_lbl}</summary>'
            f'<div class="code-card" style="margin-top:8px;">'
            f'<div class="code-card-header"><span class="code-lang">BIBTEX</span>'
            f'<button type="button" class="copy-btn" data-copy-label="{copy_lbl}">{copy_lbl}</button></div>'
            f'<pre><code>{html.escape(ent["raw_bibtex"])}</code></pre></div></details></div>'
            f"{dir_chips}</article>"
        )

    return f"""
  <main class="explorer-wrap">
    <div class="section-header" style="margin-bottom:16px;">
      <div class="section-eyebrow">docs/references.bib</div>
      <h1 style="margin:0 0 8px;font-size:30px;">{html.escape(h1)}</h1>
      <p>{html.escape(lead)}</p>
    </div>

    <div class="explorer-toolbar">
      <input id="explorer-search" class="filter-input" type="search" placeholder="{html.escape(placeholder)}" autocomplete="off">
      <select id="chapter-filter" class="chapter-select" aria-label="{html.escape(select_aria)}">
        {"".join(options_html)}
      </select>
      <label style="display:inline-flex;align-items:center;gap:6px;font-size:13px;color:var(--fg-muted);cursor:pointer;">
        <input id="formalized-only" type="checkbox"> {html.escape(only_form_lbl)}
      </label>
    </div>

    <div id="explorer-status" class="results-status" data-template="{html.escape(status_tpl)}">
      {html.escape(status_tpl.format(shown=len(bib_entries), total=len(bib_entries)))}
    </div>

    <div id="bib-explorer-list" class="bib-list">
      {"".join(cards_html)}
    </div>
  </main>
"""


def build_smart_404_page(wordmark_nav: str, toolchain_tag: str) -> str:
    """Build 404.html that auto-redirects legacy root doc-gen4 URLs to /docs/..."""
    body = """
  <main class="section" style="text-align:center;padding:88px 24px;">
    <div class="section-eyebrow">404</div>
    <h1 style="margin:0 0 12px;font-size:32px;">Page Not Found / 页面未找到</h1>
    <p id="redirect-msg" style="color:var(--fg-muted);max-width:560px;margin:0 auto 28px;">
      The requested path could not be found. API documentation generated by <code>doc-gen4</code> is hosted under <code>/docs/</code>.
    </p>
    <div class="hero-ctas" style="justify-content:center;">
      <a class="btn btn-primary" href="./index.html">Qatlib Home / 返回首页</a>
      <a class="btn btn-secondary" href="./docs/index.html">API Reference (/docs/)</a>
      <a class="btn btn-secondary" href="./modules.html">Module Explorer</a>
    </div>
  </main>
"""
    return render_page_shell(
        title="404 Not Found",
        lang="en",
        page_slug="",
        root_prefix="./",
        toolchain_tag=toolchain_tag,
        wordmark_nav=wordmark_nav,
        body_html=body,
    )


# ---------------------------------------------------------------------------
# doc-gen4 post-processing (_site/docs/)
# ---------------------------------------------------------------------------

def upgrade_docgen_directory(
    docs_out: Path,
    toolchain_tag: str,
    tree_stats: dict[str, Any],
    bib_count: int,
    areas_en: list[dict[str, Any]],
) -> None:
    """Enhance doc-gen4 output under _site/docs/ without breaking any relative assets."""
    # 1. Inject return-to-portal links at the top of navbar.html
    navbar_file = docs_out / "navbar.html"
    if navbar_file.is_file():
        nav_html = navbar_file.read_text(encoding="utf-8")
        portal_links = (
            '<h3>Qatlib Portal</h3>'
            '<div class="nav_link"><a href="../index.html">← Home &amp; Guides</a></div>'
            '<div class="nav_link"><a href="../getting-started.html">getting started</a></div>'
            '<div class="nav_link"><a href="../modules.html">module explorer</a></div>'
            '<div class="nav_link"><a href="../papers.html">bibliography</a></div>'
        )
        if "Qatlib Portal" not in nav_html:
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
    <a href="../index.html"><strong>← Back to Qatlib Home &amp; Guides</strong></a>
    &nbsp;·&nbsp; <a href="../getting-started.html">Getting Started &amp; Cache</a>
    &nbsp;·&nbsp; <a href="../architecture.html">Architecture</a>
    &nbsp;·&nbsp; <a href="../modules.html">Module Explorer</a>
    &nbsp;·&nbsp; <a href="../papers.html">Bibliography ({bib_count})</a>
    &nbsp;·&nbsp; <a href="../zh/index.html">简体中文</a>
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
                f'<link rel="icon" href="{root_rel}favicon.svg">'
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
                f'<p><a href="{portal_rel}index.html">← Qatlib Home</a> · '
                f'<a href="{portal_rel}modules.html#{html.escape(rel_dir)}">Module Explorer</a> · '
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
                f"<title>{html.escape(heading)} — Qatlib API</title></head>"
                f'<body style="padding:36px 24px;max-width:920px;margin:0 auto;">'
                f'<p><a href="{portal_rel}index.html">← Qatlib Home</a> · '
                f'<a href="{portal_rel}modules.html#{html.escape(rel_dir)}">Module Explorer</a> · '
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
    live_base = "https://quantum-atlas-ai.github.io/qatlib"

    def render_stub_note(rel_doc_path: str) -> str:
        live_url = f"{live_base}/{rel_doc_path}" if rel_doc_path != "index.html" else f"{live_base}/"
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
            f"<title>{heading}</title></head>"
            f'<body style="padding:40px 24px;max-width:880px;margin:0 auto;">'
            f'<p><a href="../index.html">← Back to Qatlib Portal</a> · <a href="../modules.html">Module Explorer</a></p>'
            f"<h1>{heading} (Lean {html.escape(toolchain_tag)})</h1>{render_stub_note(fname)}"
            f"</body></html>",
            encoding="utf-8",
        )
    # Also write stub entry pages for featured modules so --check validates 100% of links locally
    for d in tree_stats["dirs"]:
        for m in d["featured_mods"]:
            p = docs_out / m["html_path"]
            p.parent.mkdir(parents=True, exist_ok=True)
            rel_assets = os.path.relpath(docs_out.parent / "assets/style.css", p.parent).replace("\\", "/")
            rel_theme = os.path.relpath(docs_out.parent / "assets/theme-init.js", p.parent).replace("\\", "/")
            rel_home = os.path.relpath(docs_out.parent / "index.html", p.parent).replace("\\", "/")
            p.write_text(
                f'<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">'
                f'<link rel="stylesheet" href="{rel_assets}">'
                f'<script src="{rel_theme}"></script>'
                f'<title>{html.escape(m["label"])}</title></head>'
                f'<body style="padding:36px 24px;max-width:880px;margin:0 auto;">'
                f'<p><a href="{rel_home}">← Back to Qatlib Portal</a></p>'
                f"<h1><code>{html.escape(m['label'])}</code></h1>{render_stub_note(m['html_path'])}</body></html>",
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
    portal_pages = [
        *out_dir.glob("*.html"),
        *(out_dir / "zh").glob("*.html"),
    ]
    for html_file in portal_pages:
        parser = _LinkCollector()
        parser.feed(html_file.read_text(encoding="utf-8"))
        for raw in parser.links:
            if raw.startswith(("http://", "https://", "mailto:", "javascript:", "data:", "#")):
                continue
            clean = raw.split("#", 1)[0].split("?", 1)[0]
            if not clean:
                continue
            resolved = (html_file.parent / clean).resolve()
            if resolved.is_dir():
                resolved = resolved / "index.html"
            if not resolved.is_file():
                errors.append(f"{html_file.relative_to(out_dir)} -> broken link: {raw}")
    return errors


# ---------------------------------------------------------------------------
# Main Build Entrypoint
# ---------------------------------------------------------------------------

def build_site(
    repo_root: Path,
    out_dir: Path,
    docgen_dir: Path | None,
    move_docgen: bool,
    stub_docgen: bool,
    check_links: bool,
) -> None:
    tc_raw = (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    toolchain_tag = tc_raw.split(":")[-1] if ":" in tc_raw else tc_raw

    wordmark_nav = load_wordmark_svg(repo_root, css_class="nav-wordmark")
    wordmark_hero = load_wordmark_svg(repo_root, css_class="hero-wordmark")

    bib_sections, bib_entries = parse_references_bib(repo_root / "docs/references.bib")
    bib_key_map = {e["key"]: e for e in bib_entries}
    tree_stats = scan_qatlib_tree(repo_root, set(bib_key_map.keys()))
    for ck, dir_set in tree_stats["cite_to_dirs"].items():
        if ck in bib_key_map:
            bib_key_map[ck]["cited_by_dirs"] = sorted(dir_set)

    areas_en, bibtex_en = parse_readme_areas_and_bibtex(repo_root / "README.en.md")
    areas_zh, bibtex_zh = parse_readme_areas_and_bibtex(repo_root / "README.md")

    if out_dir.exists():
        shutil.rmtree(out_dir)
    (out_dir / "assets").mkdir(parents=True, exist_ok=True)
    (out_dir / "zh").mkdir(parents=True, exist_ok=True)
    (out_dir / ".nojekyll").write_text("", encoding="utf-8")
    (out_dir / "assets/style.css").write_text(SITE_CSS, encoding="utf-8")
    (out_dir / "assets/theme-init.js").write_text(THEME_INIT_JS, encoding="utf-8")
    (out_dir / "assets/site.js").write_text(SITE_JS, encoding="utf-8")
    for wm_asset in ("qatlib-wordmark.svg", "qatlib-wordmark.png"):
        wm_src = repo_root / ".github/assets" / wm_asset
        if wm_src.is_file():
            shutil.copy2(wm_src, out_dir / "assets" / wm_asset)

    # Assemble English (/) and Chinese (/zh/) pages
    for lang, root_prefix, sub_dir, areas, bibtex_str in [
        ("en", "./", out_dir, areas_en, bibtex_en),
        ("zh", "../", out_dir / "zh", areas_zh, bibtex_zh or bibtex_en),
    ]:
        # 1. Overview (index.html)
        home_body = build_home_body(
            lang=lang,
            root_prefix=root_prefix,
            toolchain_tag=toolchain_tag,
            wordmark_hero=wordmark_hero,
            tree_stats=tree_stats,
            bib_count=len(bib_entries),
            areas=areas,
            bibtex_str=bibtex_str,
        )
        (sub_dir / "index.html").write_text(
            render_page_shell(
                title="Qatlib",
                lang=lang,
                page_slug="index.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                wordmark_nav=wordmark_nav,
                body_html=home_body,
            ),
            encoding="utf-8",
        )

        # 2. Getting Started
        gs_src = repo_root / ("docs/getting-started.en.md" if lang == "en" else "docs/getting-started.md")
        gs_title, gs_html, gs_toc = process_markdown_guide(gs_src, repo_root, lang, root_prefix)
        (sub_dir / "getting-started.html").write_text(
            render_page_shell(
                title=gs_title,
                lang=lang,
                page_slug="getting-started.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
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
        arch_src = repo_root / ("docs/architecture.en.md" if lang == "en" else "docs/architecture.md")
        arch_title, arch_html, arch_toc = process_markdown_guide(arch_src, repo_root, lang, root_prefix)
        scripts_md = repo_root / ("scripts/README.en.md" if lang == "en" else "scripts/README.md")
        if not scripts_md.is_file():
            scripts_md = repo_root / "scripts/README.md"
        if scripts_md.is_file():
            _, scripts_html, _ = process_markdown_guide(scripts_md, repo_root, lang, root_prefix)
            sec_title = "3. Verification & Maintenance Executables (scripts/)" if lang == "en" else "3. 开发与内核审计可执行工具 (scripts/)"
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
        mod_title = "Module Explorer" if lang == "en" else "模块导览"
        (sub_dir / "modules.html").write_text(
            render_page_shell(
                title=mod_title,
                lang=lang,
                page_slug="modules.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
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
        pap_title = "Papers & Bibliography" if lang == "en" else "文献与参考书目"
        (sub_dir / "papers.html").write_text(
            render_page_shell(
                title=pap_title,
                lang=lang,
                page_slug="papers.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
                wordmark_nav=wordmark_nav,
                body_html=build_papers_explorer_body(
                    lang=lang,
                    root_prefix=root_prefix,
                    bib_sections=bib_sections,
                    bib_entries=bib_entries,
                ),
            ),
            encoding="utf-8",
        )

        # 6. Contributing
        contrib_src = repo_root / ("CONTRIBUTING.en.md" if lang == "en" else "CONTRIBUTING.md")
        contrib_title, contrib_html, contrib_toc = process_markdown_guide(contrib_src, repo_root, lang, root_prefix)
        (sub_dir / "contributing.html").write_text(
            render_page_shell(
                title=contrib_title,
                lang=lang,
                page_slug="contributing.html",
                root_prefix=root_prefix,
                toolchain_tag=toolchain_tag,
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

    # 404 page with legacy root doc-gen4 URL redirector
    (out_dir / "404.html").write_text(
        build_smart_404_page(wordmark_nav, toolchain_tag),
        encoding="utf-8",
    )

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
            areas_en=areas_en,
        )
    elif stub_docgen:
        create_stub_docgen_dir(docs_target, toolchain_tag, tree_stats)

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
    parser.add_argument("--check", action="store_true", help="Verify all internal relative links in generated portal HTML")
    args = parser.parse_args()

    build_site(
        repo_root=args.repo_root.resolve(),
        out_dir=args.out_dir.resolve(),
        docgen_dir=args.docgen_dir.resolve() if args.docgen_dir else None,
        move_docgen=args.move_docgen,
        stub_docgen=args.stub_docgen_if_missing,
        check_links=args.check,
    )


if __name__ == "__main__":
    main()
