#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Regression tests for bilingual portal and mounted API typography."""

from __future__ import annotations

from contextlib import contextmanager
import gzip
from html.parser import HTMLParser
import html
import json
from pathlib import Path
import re
import shutil
from string import Formatter
import subprocess
import tempfile
import unittest
from urllib.parse import urljoin

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

    def test_locale_catalogs_have_matching_messages_and_placeholders(self):
        def schema(value):
            if isinstance(value, dict):
                return {key: schema(child) for key, child in value.items()}
            if isinstance(value, list):
                return [schema(child) for child in value]
            self.assertIsInstance(value, str)
            self.assertTrue(value.strip())
            return {field for _, field, _, _ in Formatter().parse(value) if field is not None}

        zh, en = (build_site.strings_for(lang) for lang in ("zh", "en"))
        self.assertEqual(schema(zh), schema(en))

    def test_bilingual_not_found_markup(self):
        page = build_site.build_smart_404_page()
        self.assertIn('<span lang="zh-Hans">页面未找到</span>', page)
        self.assertIn('<span lang="en">Page not found</span>', page)
        elements = Elements(page).elements
        self.assertEqual({a["href"] for tag, a in elements if tag == "a" and "hreflang" in a},
                         {"./en/", "./"})

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

    def test_optional_paper_metadata_renders_registered_coverage_in_both_languages(self):
        paper = {
            "id": "Example",
            "claims": [{"id": "c001", "label": "Theorem 4", "claim-rank": "A"}],
            "coverage_claims": {
                "math": {"rank": "B+", "target": "Show c001 for x < 1.",
                         "source_claims": ["Example.c001", "c001", "c002", "c003", None],
                         "covered_by": [None, {"file": "ExternalOverlay/Papers/Example/Main.lean",
                                              "fqn": "ExternalOverlay.Papers.Example.Main.bound",
                                              "coverage": "partial_support", "note": "Finite support."}]},
                "asymptotic": None,
                "circuit": {"rank": "D", "target": "Construct the gate sequence.", "source_claims": None},
                "resource": {"rank": "not_applicable", "reason": "No resource target.", "covered_by": None},
            },
        }
        catalog = {"units": []}
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            path = root / "papers" / "Example.json"
            path.parent.mkdir()
            path.write_text(json.dumps(paper), encoding="utf-8")
            metadata = build_site.load_panel_metadata(root)
        [record] = build_site.build_panel_papers([], catalog, metadata)
        for lang, heading, dimensions, unknown in (
            ("en", "Paper coverage", ("Mathematics", "Asymptotics", "Circuit", "Resources"), "Unassessed"),
            ("zh", "论文四维覆盖", ("数学", "渐近", "线路", "资源"), "待评估"),
        ):
            with self.subTest(lang=lang):
                page = build_site.build_paper_detail_body(
                    paper=record, lang=lang, root_prefix="./", catalog=catalog)
                table = page.split(f"<h2>{heading}</h2>", 1)[1].split("</article>", 1)[0]
                self.assertIn('<table class="panel-decl-table panel-coverage-table">', table)
                for dimension, grade in zip(dimensions, ("B+", unknown, "D", "N/A"), strict=True):
                    self.assertIn(f'<th scope="row">{dimension}</th><td>{grade}</td>', table)
                self.assertIn("Show Theorem 4 for x &lt; 1.", table)
                self.assertIn("No resource target.", table)
                self.assertIn("ExternalOverlay/Papers/Example/Main.lean", table)
                self.assertIn("ExternalOverlay.Papers.Example.Main.bound", table)
                self.assertIn("partial support", table)
                self.assertEqual(table.count("Theorem 4"), 2)
                unnamed = "Unnumbered source statement" if lang == "en" else "原文未编号主张"
                self.assertEqual(table.count(unnamed), 1)
                self.assertNotIn("c001", table)
                self.assertNotIn("blob/main", table)
        source_only = build_site.load_panel_metadata(None)
        [record] = build_site.build_panel_papers([{"key": "Example"}], catalog, source_only)
        page = build_site.build_paper_detail_body(
            paper=record, lang="en", root_prefix="./", catalog=catalog)
        self.assertNotIn("Paper coverage", page)
        self.assertIn("No structured claims are available", page)

    def test_paper_coverage_tolerates_missing_claim_ids_and_invalid_payloads(self):
        for coverage in (None, {}, ["math"], "math"):
            self.assertEqual(build_site.build_paper_coverage_body(
                {"metadata": {"coverage_claims": coverage}}, "en"), "")
        for claims in (None, [None, "legacy", {"label": "Missing ID"}]):
            page = build_site.build_paper_coverage_body(
                {"metadata": {"coverage_claims": {"math": {"source_claims": ["Example.c001"]}}},
                 "claims": claims}, "en")
            self.assertEqual(page.count("Unnumbered source statement"), 1)

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
            (raw / "search.js").write_text("export {};\nDeclarationDataCenter.init()\n  .then(() => {\n  });\n")
            before = {p.relative_to(raw): p.read_bytes() for p in raw.rglob("*") if p.is_file()}
            self.assertEqual(build_site.verify_docgen(repo, raw), [])
            build_site.build_site(repo, output, raw, move_docgen=False, stub_docgen=False, check_links=False)
            self.assertEqual({p.relative_to(raw): p.read_bytes() for p in raw.rglob("*") if p.is_file()}, before)
            self.assertIn(build_site.DOCGEN_TYPOGRAPHY_CSS, (output / "docs/style.css").read_text())
            self.assertIn('lang="zh-Hans" hreflang="zh-Hans">中文</a>', (output / "docs/index.html").read_text())
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
                "lean-toolchain": "leanprover/lean4:v4.35.0\n",
                "docs/references.bib": "@book{Example,\n  title={Example},\n  year={2026}\n}\n",
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
            (raw / "navbar.html").write_text(
                '<h3>Qatlib Portal</h3><div class="nav_link"><a href="../dependencies.html">theorem dependencies</a></div>'
                '<h3>General documentation</h3>'
            )
            legacy_import = 'import "./dependency-graph-api.js";'
            legacy_call = 'addQatlibDependencyLinks("../dependencies.html", ["Papers"], []);'
            graph_import = 'import {addQatlibDependencyLinks} from "./dependency-graph-api.js";'
            (raw / "search.js").write_text(
                f"export {{}};\nDeclarationDataCenter.init()\n  .then(() => {{\n  }});\n"
                f"{legacy_import}\n{graph_import}\n{legacy_call}\n"
            )
            graph = b'{"version": 1, "ambiguousNames": ["Example.shared"]}'
            (raw / build_site.DEPENDENCY_GRAPH_ASSET).write_bytes(gzip.compress(graph))
            base = "https://example.invalid/project/"
            build_site.build_site(repo, output, raw, move_docgen=False,
                                  stub_docgen=False, check_links=True, site_url=base.rstrip("/"))
            self.assert_localized_output(output, base)
            mounted = output / "docs"
            for name in ("index.html", "navbar.html"):
                text = (mounted / name).read_text()
                self.assertIn('href="../en/dependencies.html"', text)
                self.assertIn('href="../" lang="zh-Hans" hreflang="zh-Hans">中文</a>', text)
            self.assertEqual((mounted / "navbar.html").read_text().count("<h3>Qatlib Portal</h3>"), 1)
            self.assertNotIn('href="../dependencies.html"', (mounted / "navbar.html").read_text())
            search_script = (mounted / "search.js").read_text()
            self.assertNotIn(legacy_import, search_script)
            self.assertNotIn(legacy_call, search_script)
            self.assertEqual(search_script.count(graph_import), 1)
            self.assertIn('"zh": ["../dependencies.html", "定理依赖"]', search_script)
            self.assertIn('"en": ["../en/dependencies.html", "dependencies"]', search_script)
            self.assertIn('["Foundations", "Concepts", "Papers"], ["Example.shared"]);', search_script)
            build_site.build_site(repo, root / "reassembled", mounted, move_docgen=False,
                                  stub_docgen=False, check_links=True)
            self.assertEqual((root / "reassembled/docs/search.js").read_text(), search_script)
            (mounted / build_site.DEPENDENCY_GRAPH_ASSET).write_text('{"version": 1}')
            build_site.install_dependency_graph_api(mounted)
            updated = (mounted / "search.js").read_text()
            self.assertEqual(updated.count(graph_import), 1)
            self.assertNotIn("Example.shared", updated)
            dated = re.findall(r"^## (\[\d{4}-\d{2}-\d{2}(?:\.\d+)?\] — .+)$",
                               changelog.decode(), re.M)
            self.assertTrue(dated)
            for lang, label in (("en", "Changelog"), ("zh", "更新日志")):
                directory = output / ("en" if lang == "en" else "")
                prefix = "../en/" if lang == "en" else "./"
                with self.subTest(lang=lang):
                    home = (directory / "index.html").read_text()
                    page = (directory / "changelog.html").read_text()
                    href = prefix + "changelog.html"
                    resources = re.search(r'<nav class="hero-resources"[^>]*>(.*?)</nav>', home, re.S)[1]
                    self.assertIn(f'<a href="{href}">{label}</a>', resources)
                    for section in ("header", "footer"):
                        section_html = re.search(rf"<{section}\b[^>]*>(.*?)</{section}>", home, re.S)[1]
                        self.assertIn(f'href="{href}"', section_html)
                    self.assertIn(f'href="{prefix}"', page)
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

    def test_dependency_shell_metadata_language_and_guide_navigation(self):
        prefix = "../"
        for lang, alternate in (("en", "zh-Hans"), ("zh", "en")):
            with self.subTest(lang=lang):
                title, body = build_site.build_dependency_graph_body(lang, prefix, "")
                graph = build_site.render_page_shell(
                    title=title, lang=lang, page_slug="dependencies.html", root_prefix=prefix,
                    toolchain_tag="test", wordmark_nav="", body_html=body)
                tags = Elements(graph).elements
                description = next(attrs["content"] for tag, attrs in tags
                                   if tag == "meta" and attrs.get("name") == "description")
                self.assertTrue(description)
                switch = next(attrs for tag, attrs in tags
                              if tag == "a" and attrs.get("hreflang") == alternate)
                self.assertEqual(switch["lang"], alternate)
                menu = next(attrs for tag, attrs in tags
                            if tag == "details" and attrs.get("class") == "lang-switcher")
                self.assertIn("data-preserve-hash", menu)
                layout = build_site.build_docs_layout(
                    page_title="Guide", source_rel="docs/getting-started.md", lang=lang,
                    page_slug="getting-started.html", root_prefix=prefix, prose_html="", toc=[])
                self.assertIn(f'href="../{build_site.url_for(lang, "dependencies.html")}"', layout)

    def assert_localized_output(self, output, base):
        home_taglines = {
            "zh": "面向量子计算与量子信息的 Lean 4 形式化库",
            "en": "The Lean 4 Library for Quantum Computing and Quantum Information",
        }
        pages = {
            "index.html", "getting-started.html", "architecture.html", "modules.html",
            "papers.html", "dependencies.html", "contributing.html", "changelog.html",
            "papers/Example.html", "units/Example.html",
        }
        for lang, tag, og, other in (("zh", "zh-Hans", "zh_CN", "en_US"),
                                     ("en", "en", "en_US", "zh_CN")):
            folder = output / ("en" if lang == "en" else "")
            for page in pages:
                with self.subTest(lang=lang, page=page):
                    suffix = "" if page == "index.html" else page
                    source = (folder / page).read_text()
                    elements = Elements(source).elements
                    self.assertEqual(elements[0][1]["lang"], tag)
                    links = [a for element, a in elements if element == "link"]
                    canonical = next(a["href"] for a in links if a["rel"] == "canonical")
                    self.assertEqual(canonical, base + ("en/" if lang == "en" else "") + suffix)
                    self.assertEqual({a["hreflang"]: a["href"] for a in links if a["rel"] == "alternate"}, {
                        "en": base + "en/" + suffix, "zh-Hans": base + suffix,
                        "x-default": base,
                    })
                    meta = {a.get("property"): a.get("content") for el, a in elements if el == "meta"}
                    self.assertEqual((meta["og:locale"], meta["og:locale:alternate"]), (og, other))
                    self.assertEqual(meta["og:image"], base + "assets/qatlib-social-preview.png")
                    self.assertEqual(meta["og:url"], canonical)
                    self.assertTrue(meta["og:description"])
                    if page == "index.html":
                        tagline = home_taglines[lang]
                        self.assertIn(f"<h1>{tagline}</h1>", source)
                        self.assertEqual(meta["og:description"], tagline)
                        for name in ("description", "twitter:description"):
                            content = next(a["content"] for el, a in elements
                                           if el == "meta" and a.get("name") == name)
                            self.assertEqual(content, tagline)
                    menu, = [a for el, a in elements if el == "details" and a.get("class") == "lang-switcher"]
                    self.assertNotIn("open", menu)
                    self.assertTrue(any(el == "summary" and a.get("aria-label") for el, a in elements))
                    switches = [a for el, a in elements if el == "a" and "hreflang" in a]
                    self.assertEqual([a["hreflang"] for a in switches], ["zh-Hans", "en"])
                    for switch in switches:
                        option = switch["hreflang"]
                        self.assertEqual(switch["lang"], option)
                        self.assertEqual(switch.get("aria-current"), "page" if option == tag else None)
                        self.assertEqual(urljoin(canonical, switch["href"]),
                                         base + ("en/" if option == "en" else "") + suffix)
                    prefix = "../" * ((lang == "en") + page.count("/")) or "./"
                    self.assertIn(f'src="{prefix}assets/i18n.js"', source)
                    if page == "dependencies.html":
                        self.assertIn(f'data-src="{prefix}docs/{build_site.DEPENDENCY_GRAPH_ASSET}"', source)
                    else:
                        self.assertIn(f'href="{prefix}docs/index.html"', source)

        root = (output / "index.html").read_text()
        self.assertIn('<html lang="zh-Hans">', root)
        self.assertIn('id="main-content"', root)
        self.assertNotIn('http-equiv="refresh"', root)
        self.assertIn('href="./en/"', root)
        for page in pages:
            stub = (output / "zh" / page).read_text()
            suffix = "" if page == "index.html" else page
            target = "../" * (1 + page.count("/")) + suffix
            self.assertIn(f'data-redirect-target="{target}"', stub)
            self.assertIn(f'<noscript><meta http-equiv="refresh" content="0; url={target}"></noscript>', stub)
            self.assertIn(f'<link rel="canonical" href="{base}{suffix}">', stub)
            self.assertIn(f'<a href="{target}">', stub)
            self.assertLess(len(stub.encode()), 700)
        sitemap = (output / "sitemap.xml").read_text()
        self.assertEqual(re.findall(r"<loc>([^<]+)</loc>", sitemap), [base, base + "en/"])
        self.assertIn(f"[Qatlib.Foundations]({base}docs/Qatlib/Foundations/)", (output / "llms.txt").read_text())
        for file in output.rglob("*.html"):
            if file.relative_to(output).parts[0] == "docs":
                continue
            for el, a in Elements(file.read_text()).elements:
                if el == "script":
                    self.assertIn("src", a)
                self.assertFalse(any(key.startswith("on") for key in a))
                for key in ("href", "src", "action", "data-src"):
                    value = a.get(key, "")
                    if value.startswith(("./", "../")):
                        self.assertNotIn("?", value.split("#")[0])


if __name__ == "__main__":
    unittest.main()
