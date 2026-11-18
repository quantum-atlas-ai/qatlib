#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Regression tests for bilingual portal and mounted API typography."""

from __future__ import annotations

from contextlib import contextmanager
from html.parser import HTMLParser
import html
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

import build_site

SOURCE = Path(__file__).resolve().parents[1]


def declarations(css, selector):
    """Collect successive declarations for an exact selector in these flat rules."""
    result = {}
    css = re.sub(r"/\*.*?\*/", "", css, flags=re.S)
    for selectors, body in re.findall(r"([^{}]+)\{([^{}]*)\}", css):
        if selector not in [item.strip() for item in selectors.split(",")]:
            continue
        for item in body.split(";"):
            if ":" in item:
                key, value = item.split(":", 1)
                result[key.strip()] = value.strip()
    return result


def families(value):
    return [item.strip().strip("\"'") for item in value.split(",")]


class Elements(HTMLParser):
    def __init__(self, source):
        super().__init__()
        self.elements = []
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        self.elements.append((tag, dict(attrs)))


@contextmanager
def workspace():
    root = Path(tempfile.mkdtemp())
    try:
        yield root
    finally:
        subprocess.run(["trash-put", "--", str(root)], check=True)


class SiteTypographyTests(unittest.TestCase):
    def test_modern_sans_order_and_monospace_cjk_fallbacks(self):
        variables = declarations(build_site.SITE_CSS, ":root")
        sans = families(variables["--font-sans"])
        modern = ["PingFang SC", "HarmonyOS Sans SC", "Source Han Sans SC",
                  "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", "sans-serif"]
        self.assertEqual(sans[-len(modern):], modern)
        self.assertNotIn("Hiragino Sans GB", sans)
        mono = families(variables["--font-mono"])
        self.assertEqual(mono[:2], ["JetBrains Mono", "JuliaMono"])
        self.assertEqual(mono[-9:], ["Sarasa Mono SC", "Noto Sans Mono CJK SC",
                                    "Source Han Mono SC", "PingFang SC", "Source Han Sans SC",
                                    "Noto Sans CJK SC", "Noto Sans SC", "Microsoft YaHei", "monospace"])

    def test_ui_labels_and_form_controls_use_text_family(self):
        for selector in (".section-eyebrow", ".layer-badge", ".mod-layer-tag", ".mod-count"):
            with self.subTest(selector=selector):
                rules = declarations(build_site.SITE_CSS, selector)
                self.assertEqual(rules["font-family"], "var(--font-sans)")
                self.assertEqual(rules["font-variant-numeric"], "tabular-nums")
        for tag in ("button", "input", "select", "textarea"):
            self.assertEqual(declarations(build_site.SITE_CSS, tag)["font-family"], "inherit")

    def test_chinese_spacing_leading_and_weights(self):
        body = declarations(build_site.SITE_CSS, "body:lang(zh)")
        self.assertEqual(body["line-height"], "1.75")
        self.assertEqual(body["text-spacing-trim"], "space-first")
        self.assertEqual(body["font-kerning"], "normal")
        for selector, leading in ((".hero h1", "1.36"), (".prose-header h1", "1.36"),
                                  (".panel-detail-header h1", "1.36"), (".explorer-wrap h1", "1.36"),
                                  (".section-header h2", "1.42"), (".prose h2", "1.42")):
            with self.subTest(selector=selector):
                rules = declarations(build_site.SITE_CSS, selector + ":lang(zh)")
                self.assertEqual(rules["letter-spacing"], "0")
                self.assertEqual(rules["line-height"], leading)
                self.assertEqual(rules["font-weight"], "600")
        for selector in (".area-card h3", ".layer-card h3", ".prose h3"):
            rules = declarations(build_site.SITE_CSS, selector + ":lang(zh)")
            self.assertEqual(rules["line-height"], "1.45")
            self.assertEqual(rules["font-weight"], "600")
        for selector in (".section-eyebrow", ".sidebar-group-title"):
            rules = declarations(build_site.SITE_CSS, selector + ":lang(zh)")
            self.assertEqual(rules["letter-spacing"], "0.04em")
            self.assertEqual(rules["text-transform"], "none")
        for selector in (".panel-empty", "em", "cite"):
            self.assertEqual(declarations(build_site.SITE_CSS, selector + ":lang(zh)")["font-style"], "normal")
        for selector in (".filter-pill", ".bib-ext-badge", ".mod-actions"):
            self.assertEqual(declarations(build_site.SITE_CSS, selector + ":lang(zh)")["font-weight"], "500")
        self.assertEqual(declarations(build_site.SITE_CSS, ".bib-title")["font-weight"], "600")
        self.assertEqual(declarations(build_site.SITE_CSS, ".prose :not(pre) > code:lang(zh)")["margin-inline"], "0.14em")

    def test_language_switch_and_bilingual_not_found_markup(self):
        for lang, alternate in (("en", "zh-CN"), ("zh", "en")):
            page = build_site.render_page_shell(title="Example", lang=lang, page_slug="index.html",
                                                root_prefix="./", toolchain_tag="test",
                                                wordmark_nav="", body_html="")
            switch = [attrs for tag, attrs in Elements(page).elements
                      if tag == "a" and attrs.get("class") == "lang-switch"]
            self.assertEqual(switch[0]["lang"], alternate)
        page = build_site.build_smart_404_page("", "test")
        self.assertIn('<html lang="en">', page)
        for text in ("页面未找到", "返回首页"):
            self.assertIn(f'<span lang="zh-CN">{text}</span>', page)

    def test_papers_bibliography_links_match_docgen_reference_anchors(self):
        # Pinned doc-gen4 renders bibliography entries with a "ref_" ID prefix.
        references = '<div id="ref_Aaronson2007Learnability"></div><div id="ref_Aaronson2018Shadow"></div>'
        anchors = {attrs["id"] for _, attrs in Elements(references).elements}
        entries = [{"key": key, "title": key} for key in
                   ("Aaronson2007Learnability", "Aaronson2018Shadow")]
        for lang, prefix in (("en", "./"), ("zh", "../")):
            with self.subTest(lang=lang):
                page = build_site.build_papers_explorer_body(
                    lang=lang, root_prefix=prefix, bib_sections=[], bib_entries=entries)
                links = [attrs["href"] for tag, attrs in Elements(page).elements
                         if tag == "a" and "references.html#" in attrs.get("href", "")]
                self.assertEqual(len(links), len(entries))
                for link in links:
                    target, anchor = link.split("#", 1)
                    self.assertEqual(target, prefix + "docs/references.html")
                    self.assertTrue(anchor.startswith("ref_"))
                    self.assertIn(anchor, anchors)

    def test_api_css_uses_existing_bold_family_and_cjk_stacks(self):
        css = build_site.DOCGEN_TYPOGRAPHY_CSS
        for selector in ("body", ".inductive_ctor_doc", ".structure_field_doc"):
            rules = declarations(css, selector)
            stack = families(rules["font-family"])
            self.assertEqual(stack[:2], ["Lato Medium", "Lato"])
            self.assertEqual(stack[-1], "sans-serif")
            self.assertEqual(rules["line-height"], "1.62")
        for selector in ("h1", "h2", "h3", "h4", "h5", "h6", "strong", "b"):
            stack = families(declarations(css, selector)["font-family"])
            self.assertEqual(stack[:2], ["Lato", "Lato Medium"])
            self.assertEqual(stack[-1], "sans-serif")
            self.assertLess(stack.index("Source Han Sans SC"), stack.index("Microsoft YaHei"))
        for selector in (".imports li", "code", ".decl_header", ".attributes", ".structure_field_info",
                         ".constructor", ".instances li", ".instances-for-list li", ".equation", ".structure_ext_ctor"):
            stack = families(declarations(css, selector)["font-family"])
            self.assertEqual(stack[0], "JuliaMono")
            self.assertEqual(stack[-1], "monospace")
            self.assertLess(stack.index("Noto Sans Mono CJK SC"), stack.index("Microsoft YaHei"))

    def test_assembly_patches_only_mounted_copy_and_is_idempotent(self):
        with workspace() as root:
            repo, raw, output = (root / name for name in ("repo", "raw", "output"))
            repo.mkdir()
            for name in ("README.md", "README.en.md", "CONTRIBUTING.md", "CONTRIBUTING.en.md",
                         "CITATION.cff", "CHANGELOG.md", "lean-toolchain", "docs/references.bib",
                         "docs/getting-started.md", "docs/getting-started.en.md",
                         "docs/architecture.md", "docs/architecture.en.md", "scripts/README.md"):
                target = repo / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(SOURCE / name, target)
            module = repo / "Qatlib/Foundations/Example/Main.lean"
            module.parent.mkdir(parents=True)
            module.write_text("/-! 中文说明 -/\ndef example := 1\n", encoding="utf-8")
            for name in ("index.html", "navbar.html", "style.css", "search.html", "search.js",
                         "declaration-data.js", "references.html", "Qatlib.html",
                         "declarations/declaration-data.bmp", "Qatlib/Foundations/Example/Main.html"):
                target = raw / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text('<html lang="en"><title>Index</title><main>中文说明</main></html>', encoding="utf-8")
            (raw / "style.css").write_text("body { font-family: 'Lato Medium'; }\n", encoding="utf-8")
            before = {p.relative_to(raw): p.read_bytes() for p in raw.rglob("*") if p.is_file()}
            self.assertEqual(build_site.verify_docgen(repo, raw), [])
            build_site.build_site(repo, output, raw, move_docgen=False, stub_docgen=False, check_links=False)
            self.assertEqual({p.relative_to(raw): p.read_bytes() for p in raw.rglob("*") if p.is_file()}, before)
            self.assertIn(build_site.DOCGEN_TYPOGRAPHY_CSS, (output / "docs/style.css").read_text())
            self.assertIn('lang="zh-CN">简体中文</a>', (output / "docs/index.html").read_text())
            self.assertEqual((output / "docs/Qatlib/Foundations/Example/Main.html").read_bytes(),
                             before[Path("Qatlib/Foundations/Example/Main.html")])
            mounted = output / "docs"
            assembled = {p.relative_to(mounted): p.read_bytes() for p in mounted.rglob("*") if p.is_file()}
            stats = build_site.scan_qatlib_tree(repo, set())
            build_site.upgrade_docgen_directory(mounted, "test", stats, 0, [])
            once = {p.relative_to(mounted): p.read_bytes() for p in mounted.rglob("*") if p.is_file()}
            build_site.upgrade_docgen_directory(mounted, "test", stats, 0, [])
            self.assertEqual({p.relative_to(mounted): p.read_bytes() for p in mounted.rglob("*") if p.is_file()}, once)
            self.assertEqual(assembled[Path("style.css")], once[Path("style.css")])
            self.assertEqual(once[Path("style.css")].decode().count(build_site.DOCGEN_TYPOGRAPHY_CSS), 1)

    def test_changelog_page_retains_dated_history_and_bilingual_navigation(self):
        with workspace() as root:
            repo, raw, output = (root / name for name in ("repo", "raw", "output"))
            sources = {
                "README.md": "# Qatlib\n", "README.en.md": "# Qatlib\n",
                "CONTRIBUTING.md": "# Contributing\n", "CONTRIBUTING.en.md": "# Contributing\n",
                "lean-toolchain": "leanprover/lean4:v4.35.0\n", "docs/references.bib": "",
                "docs/architecture.md": "# Architecture\n",
                "docs/architecture.en.md": "# Architecture\n",
                "docs/getting-started.md": "# Getting Started\n[Release history](../CHANGELOG.md).\n",
                "docs/getting-started.en.md": "# Getting Started\n[Release history](../CHANGELOG.md).\n",
                "Qatlib/Foundations/Example/Main.lean":
                    "namespace Qatlib.Foundations.Example\ndef value := 1\nend Qatlib.Foundations.Example\n",
            }
            for name, content in sources.items():
                target = repo / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(content, encoding="utf-8")
            changelog = (SOURCE / "CHANGELOG.md").read_bytes()
            (repo / "CHANGELOG.md").write_bytes(changelog)
            for name in ("index.html", "navbar.html", "style.css", "search.html", "search.js",
                         "declaration-data.js", "references.html", "tactics.html", "Qatlib.html",
                         "declarations/declaration-data.bmp", "Qatlib/Foundations/Example/Main.html"):
                target = raw / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text('<html lang="en"><title>API</title><main>Example</main></html>')
            build_site.build_site(repo, output, raw, move_docgen=False,
                                  stub_docgen=False, check_links=True)
            dated = re.findall(r"^## (\[\d{4}-\d{2}-\d{2}(?:\.\d+)?\] — .+)$",
                               changelog.decode(), re.M)
            self.assertTrue(dated)
            for lang, directory, prefix, label in (("en", output, "./", "Changelog"),
                                                    ("zh", output / "zh", "../zh/", "更新日志")):
                with self.subTest(lang=lang):
                    home = (directory / "index.html").read_text()
                    page = (directory / "changelog.html").read_text()
                    href = prefix + "changelog.html"
                    self.assertIn(f'<a class="btn btn-secondary" href="{href}">{label}</a>', home)
                    for section in ("header", "footer"):
                        section_html = re.search(rf"<{section}\b[^>]*>(.*?)</{section}>", home, re.S)[1]
                        self.assertIn(f'href="{href}"', section_html)
                    self.assertIn(f'href="{prefix}index.html"', page)
                    self.assertIn(f'href="{href}"', (directory / "getting-started.html").read_text())
                    headings = [html.unescape(re.sub(r"<[^>]+>", "", h)).rstrip("#").strip()
                                for h in re.findall(r"<h2\b[^>]*>(.*?)</h2>", page, re.S)]
                    rendered_dates = [h for h in headings if re.match(r"\[\d{4}-\d{2}-\d{2}", h)]
                    self.assertEqual(rendered_dates[0], dated[0])
                    self.assertEqual(rendered_dates[-1], dated[-1])
                    self.assertIn("Versioning Policy", headings)
                    elements = Elements(page).elements
                    menu = next(attrs for tag, attrs in elements
                                if tag == "button" and attrs.get("id") == "mobile-menu-btn")
                    self.assertEqual(menu["aria-controls"], "nav-links")
                    self.assertEqual(menu["aria-expanded"], "false")
                    self.assertTrue(any(tag == "form" and attrs.get("class") == "nav-search-form"
                                        and attrs.get("action", "").endswith("docs/search.html")
                                        for tag, attrs in elements))
                    ids = {attrs["id"] for _, attrs in elements if "id" in attrs}
                    for tag, attrs in elements:
                        target = attrs.get("href", "")
                        if tag == "a" and target.startswith("#"):
                            self.assertIn(target[1:], ids)
            self.assertEqual((repo / "CHANGELOG.md").read_bytes(), changelog)
            self.assertEqual(build_site.verify_portal_links(output), [])

    def test_typography_adds_no_font_sources_and_runs_in_ci(self):
        for css in (build_site.SITE_CSS, build_site.DOCGEN_TYPOGRAPHY_CSS):
            self.assertNotRegex(css, r"(?i)@font-face|@import|url\s*\(|\.woff2?\b")
        workflow = (SOURCE / ".github/workflows/lint.yml").read_text()
        self.assertIn("python3 scripts/test_site_typography.py", workflow)


if __name__ == "__main__":
    unittest.main()
