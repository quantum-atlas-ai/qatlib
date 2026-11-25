#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Source-parser regressions for portal imports, declaration identities and output."""

from __future__ import annotations

from pathlib import Path
import re
import shutil
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import urljoin
from xml.etree import ElementTree

import build_site
import docs_cache

SOURCE = Path(__file__).resolve().parents[1]
SELECTIVE = Path("Qatlib/Concepts/AbelianDecoders/SelectiveQFT.lean")
STOPPING = Path("Qatlib/Concepts/AEMeanReadout/LocalAEBackend/FiniteStoppingTail.lean")
SELECTIVE_IMPORTS = sorted((
    "Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport",
    "Qatlib.Foundations.InstrumentCore.Measurement.Basic",
    "Qatlib.Foundations.BornMetrics.EventProbability",
))


def parse_text(text):
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        path = root / "Qatlib/Concepts/Example/Main.lean"
        path.parent.mkdir(parents=True)
        path.write_text(text, encoding="utf-8")
        return build_site._parse_source_file((path, root))


class SiteBrandTests(unittest.TestCase):
    def test_wordmark_includes_the_emblem_in_both_themes(self):
        svg = "{http://www.w3.org/2000/svg}"
        assets = SOURCE / ".github/assets"
        light = ElementTree.parse(assets / "qatlib-wordmark.svg").getroot()
        dark = ElementTree.parse(assets / "qatlib-wordmark-dark.svg").getroot()
        for root in (light, dark):
            self.assertEqual(root.get("viewBox"), "-140.2627944163 -9 499.2627944163 120")
            self.assertIsNone(root.find(f".//{svg}rect"))
            self.assertIsNotNone(root.find(f".//{svg}g[@id='quantumatlas-emblem']"))
            self.assertIsNotNone(root.find(f".//{svg}g[@id='qatlib-textmark']"))

        def monogram(root):
            group = root.find(f".//{svg}g[@id='qatlib-monogram']")
            self.assertIsNotNone(group)
            return [(node.get("id"), node.get("d")) for node in group.iter(f"{svg}path")]

        favicon = ElementTree.parse(assets / "favicon/favicon-adaptive.svg").getroot()
        self.assertEqual(monogram(light), monogram(dark))
        self.assertEqual(monogram(light), monogram(favicon))

        markup = build_site.render_wordmark("../../", "nav-wordmark")
        collector = build_site._LinkCollector()
        collector.feed(markup)
        self.assertEqual(collector.links, [
            "../../assets/qatlib-wordmark.svg", "../../assets/qatlib-wordmark-dark.svg",
        ])

    def test_favicon_links_match_assets_and_have_no_query(self):
        links = build_site.render_favicon_links("../../")
        collector = build_site._LinkCollector()
        collector.feed(links)
        self.assertEqual(collector.links, [
            "../../favicon.ico",
            "../../favicon-light-32x32.png",
            "../../favicon-light-16x16.png",
            "../../favicon-dark-32x32.png",
            "../../favicon-dark-16x16.png",
            "../../favicon-adaptive.svg",
            "../../apple-touch-icon.png",
        ])
        self.assertEqual(links.count("<link "), 7)
        self.assertNotIn("?", links)
        for theme in ("light", "dark"):
            self.assertEqual(links.count(f'media="(prefers-color-scheme: {theme})"'), 2)
        for href in collector.links:
            self.assertTrue((build_site.FAVICON_ASSETS / Path(href).name).is_file())

    def test_adaptive_icon_replaces_shared_docgen_asset_in_mounted_copy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            raw = root / "raw"
            docs = root / "_site/docs"
            nested = raw / "Qatlib/Foundations"
            nested.mkdir(parents=True)
            (raw / "favicon.svg").write_text("<svg/>", encoding="utf-8")
            (raw / "index.html").write_text(
                '<head><link rel="icon" href="./favicon.svg"></head><main></main>', encoding="utf-8",
            )
            api = '<head><link rel="icon" href="../../favicon.svg"></head>'
            (nested / "Example.html").write_text(api, encoding="utf-8")
            shutil.copytree(raw, docs)
            stats = {
                "layers": {layer: {"dir_count": 0, "module_count": 0} for layer in build_site.PANEL_LAYERS},
                "dirs": [],
            }
            build_site.upgrade_docgen_directory(docs, "test", stats, 0, [])
            expected = (build_site.FAVICON_ASSETS / "favicon-adaptive.svg").read_bytes()
            self.assertEqual((docs / "favicon.svg").read_bytes(), expected)
            self.assertEqual((raw / "favicon.svg").read_text(), "<svg/>")
            self.assertEqual((docs / "Qatlib/Foundations/Example.html").read_text(), api)
            self.assertIn(build_site.render_favicon_links("../../../"),
                          (docs / "Qatlib/Foundations/index.html").read_text())
            index = (docs / "index.html").read_text()
            self.assertEqual(index.count(build_site.render_favicon_links("../")), 1)
            self.assertNotIn('href="./favicon.svg"', index)
            build_site.upgrade_docgen_directory(docs, "test", stats, 0, [])
            self.assertEqual((docs / "index.html").read_text(), index)

    def test_branding_paths_are_outside_raw_html_cache_inputs(self):
        branding_paths = (Path("README.md"), Path("README.en.md"),
                          Path(".github/assets/qatlib-wordmark.svg"),
                          Path(".github/assets/favicon/favicon-adaptive.svg"),
                          Path("scripts/build_site.py"), Path("scripts/site_docgen.py"),
                          Path(".github/assets/qatlib-social-preview.png"))
        for source in branding_paths:
            for cache_input in docs_cache.INPUTS:
                self.assertFalse(source.is_relative_to(cache_input), (source, cache_input))

    def test_portal_paths_have_one_canonical_chinese_route(self):
        self.assertEqual(build_site.url_for("zh"), "")
        self.assertEqual(build_site.url_for("en"), "en/")
        self.assertEqual(build_site.url_for("zh", "units/Example.html"), "units/Example.html")
        legacy = build_site.build_legacy_redirect("units/Example.html", build_site.DEFAULT_SITE_URL)
        self.assertIn('data-redirect-target="../../units/Example.html"', legacy)
        self.assertIn(f'rel="canonical" href="{build_site.DEFAULT_SITE_URL}units/Example.html"', legacy)


class PortalNavigationTests(unittest.TestCase):
    @staticmethod
    def links(markup):
        collector = build_site._LinkCollector()
        collector.feed(markup)
        return collector.links

    def test_home_actions_prioritize_start_graph_and_api_in_both_languages(self):
        layers = {layer: {"dir_count": 0, "module_count": 0, "loc": 0, "kind_counts": {}}
                  for layer in build_site.PANEL_LAYERS}
        stats = {"total_modules": 0, "layers": layers, "catalog": {"layers": layers}}
        for lang, prefix, mount in (("zh", "./", ""), ("en", "../", "en/")):
            with self.subTest(lang=lang):
                home = build_site.build_home_body(
                    lang=lang, root_prefix=prefix, toolchain_tag="test", wordmark_hero="",
                    tree_stats=stats, bib_count=47, areas=[], bibtex_str="", qec_html="",
                )
                actions = home.split('<nav class="hero-ctas"', 1)[1].split('</nav>', 1)[0]
                resources = home.split('<nav class="hero-resources"', 1)[1].split('</nav>', 1)[0]
                base = f"https://example.test/qatlib/{mount}"
                self.assertEqual([urljoin(base, href) for href in self.links(actions)], [
                    base + "getting-started.html", base + "dependencies.html",
                    "https://example.test/qatlib/docs/index.html",
                ])
                self.assertEqual(actions.count('class="btn btn-primary"'), 1)
                self.assertEqual(actions.count('class="btn btn-secondary"'), 2)
                self.assertEqual([urljoin(base, href) for href in self.links(resources)], [
                    base + "modules.html", base + "papers.html", base + "changelog.html",
                ])
                self.assertIn("(47)", resources)

    def test_grouped_footer_keeps_nested_links_local_and_names_github_repository(self):
        for lang, base, prefix in (("zh", "", "../"), ("en", "en/", "../../")):
            with self.subTest(lang=lang):
                page = build_site.render_page_shell(
                    title="Example", lang=lang, page_slug="units/example.html", root_prefix=prefix,
                    toolchain_tag="test", wordmark_nav="", body_html="<main></main>",
                )
                footer = page.split('<footer class="site-footer">', 1)[1].split('</footer>', 1)[0]
                groups = re.findall(r'<div class="footer-group">(.*?)</div>', footer, re.S)
                ui = build_site.strings_for(lang)["ui"]
                self.assertEqual([re.search(r'<h2>(.*?)</h2>', group)[1] for group in groups],
                                 [ui[key] for key in ("footer_guides", "footer_research", "footer_project")])
                origin = "https://example.test/qatlib/"
                url = origin + base + "units/example.html"
                self.assertEqual([[urljoin(url, href) for href in self.links(group)] for group in groups], [
                    [origin + base + page for page in ("getting-started.html", "architecture.html", "modules.html")],
                    [origin + base + page for page in ("papers.html", "dependencies.html")]
                    + [origin + "docs/index.html", origin + "docs/references.html"],
                    [build_site.GITHUB_REPO_URL, origin + base + "changelog.html", origin + base + "contributing.html"],
                ])
                self.assertIn("GitHub · quantum-atlas-ai/qatlib", groups[2])
                self.assertIn(ui["footer_note"], footer)
                self.assertIn(ui["footer_license"], footer)
                self.assertIn('<details class="lang-switcher">', page)


class SourceParserTests(unittest.TestCase):
    def test_actual_selective_qft_public_imports(self):
        module = build_site._parse_source_file((SOURCE / SELECTIVE, SOURCE))
        self.assertEqual(module["imports"], SELECTIVE_IMPORTS)
        self.assertEqual(module["layer_imports"]["Foundations"], SELECTIVE_IMPORTS[1:])
        self.assertEqual(module["layer_imports"]["Concepts"], SELECTIVE_IMPORTS[:1])

    def test_actual_stopping_tail_namespace_and_line(self):
        module = build_site._parse_source_file((SOURCE / STOPPING, SOURCE))
        declaration = next(d for d in module["declarations"] if d["name"] == "finiteSurvival")
        self.assertEqual(declaration["fqn"],
                         "Qatlib.Concepts.AEMeanReadout.LocalAEBackend.finiteSurvival")
        line = (SOURCE / STOPPING).read_text().splitlines()[declaration["line"] - 1]
        self.assertIn("def finiteSurvival", line)

    def test_header_modifiers_comments_and_multiline_imports(self):
        module = parse_text("""/- Leading /- nested -/ comment.
import Qatlib.Papers.CommentOnly
-/
module
public /- between modifier and keyword -/ import
  Qatlib.Foundations.First
public meta import Qatlib.Foundations.Meta
import /- between keyword and name -/ Qatlib.Concepts.Second
import all Qatlib.Concepts.Private
/- import Qatlib.Papers.AlsoCommented -/
namespace Example
def text : String := "
import Qatlib.Papers.InString
"
end Example
""")
        self.assertEqual(module["imports"], sorted((
            "Qatlib.Foundations.First", "Qatlib.Foundations.Meta",
            "Qatlib.Concepts.Second", "Qatlib.Concepts.Private")))

    def test_named_anonymous_and_dotted_scopes_preserve_namespace(self):
        module = parse_text("""module
namespace Outer.Inner
section Params.Deep
def inside := 1
end Params.Deep
def afterNamed := 2
section
def inAnonymous := 3
end
@[expose] public section
def publicValue := 4
end
mutual
  def left := 5
  def right := 6
end
end Inner
def outerValue := 7
end Outer
def rootValue := 8
""")
        fqns = {d["name"]: d["fqn"] for d in module["declarations"]}
        for name in ("inside", "afterNamed", "inAnonymous", "publicValue", "left", "right"):
            self.assertEqual(fqns[name], f"Outer.Inner.{name}")
        self.assertEqual(fqns["outerValue"], "Outer.outerValue")
        self.assertEqual(fqns["rootValue"], "rootValue")

    def test_comments_and_literals_do_not_open_or_close_scopes(self):
        source = r'''module
namespace Example
/- A nested /- block -/ comment:
end Example
namespace Phantom
def fake := 0
-/
/-- A documented declaration, with /- nested comment -/ text. -/
def text : String := "escaped \" quote
end Example
def fakeString := 0
"
def raw : String := r##"
end Example
namespace Fake
"##
def quote : Char := '"'
def stillHere := 1
end Example
'''
        module = parse_text(source)
        names = {d["name"]: d for d in module["declarations"]}
        self.assertEqual(set(names), {"text", "raw", "quote", "stillHere"})
        self.assertTrue(all(d["fqn"] == f"Example.{name}" for name, d in names.items()))
        self.assertIn("documented declaration", names["text"]["doc"])
        self.assertEqual(source.splitlines()[names["stillHere"]["line"] - 1], "def stillHere := 1")

    def test_multiline_scopes_and_punctuation_in_declaration_names(self):
        module = parse_text("""module
@[expose] public section
namespace
  Outer.Inner
section
  /- before the scope name -/
  Helpers.More
def inside? := 1
end
  Helpers.More
def afterSection! := 2
end
  Outer.Inner
def atRoot := 3
""")
        self.assertEqual({d["fqn"] for d in module["declarations"]}, {
            "Outer.Inner.inside?", "Outer.Inner.afterSection!", "atRoot",
        })

    def test_multiline_declaration_headers_keep_names_docs_and_source_lines(self):
        source = """module
namespace Outer.Inner
/-- A theorem with a split header. -/
private theorem
  /- A gap before the name. -/
  multiline_named : True := True.intro
/-- A definition with its visibility on a separate line. -/
@[inline]
public def
  _root_.«root.name» : Nat := 0
instance
    : Inhabited Unit := ⟨()⟩
theorem sameLine : True := True.intro
end Outer.Inner
"""
        decls = parse_text(source)["declarations"]
        self.assertEqual([(d["fqn"], d["line"]) for d in decls], [
            ("Outer.Inner.multiline_named", 4),
            ("«root.name»", 8),
            ("Outer.Inner.anonymous_11", 11),
            ("Outer.Inner.sameLine", 13),
        ])
        self.assertEqual(decls[0]["doc"], "A theorem with a split header.")
        self.assertEqual(decls[1]["doc"], "A definition with its visibility on a separate line.")

    def test_quoted_module_components_classify_and_link_the_actual_unit(self):
        source = """module
public import Qatlib.Foundations.Seed
public import «Qatlib».«Foundations».«Seed.With.Dot»
public import Qatlib.«Concepts».Other
public import «Qatlib.Foundations».Ignored
"""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Qatlib/Concepts/Example/Main.lean"
            path.parent.mkdir(parents=True)
            path.write_text(source, encoding="utf-8")
            module = build_site._parse_source_file((path, root))
            with patch.object(build_site, "ProcessPoolExecutor", side_effect=OSError):
                catalog = build_site.scan_catalog_sources(root)
        self.assertEqual(module["layer_imports"], {
            "Foundations": ["Qatlib.Foundations.Seed", "«Qatlib».«Foundations».«Seed.With.Dot»"],
            "Concepts": ["Qatlib.«Concepts».Other"],
            "Papers": [],
        })
        self.assertIn("«Qatlib.Foundations».Ignored", module["imports"])
        unit = catalog["units"][0]
        page = build_site.build_unit_detail_body(
            unit=unit, lang="en", root_prefix="../", all_unit_ids={unit["id"]},
        )
        self.assertIn('modules.html#Qatlib/Foundations/Seed.With.Dot"', page)
        self.assertIn('modules.html#Qatlib/Concepts/Other"', page)

    def test_nested_interpolated_literals_and_unicode_line_separator(self):
        source = '''module
namespace Outer
section Defs
def label : String := s!"{s!"{r##"
end Defs
end Outer
namespace Phantom
"##}"}"
def raw : String := r"A\\"
def separator : String := "A\u2028B"
end Defs
def afterSection := 1
end Outer
'''
        module = parse_text(source)
        names = {d["fqn"]: d["line"] for d in module["declarations"]}
        self.assertEqual(set(names), {"Outer.label", "Outer.raw", "Outer.separator", "Outer.afterSection"})
        self.assertEqual(source.split("\n")[names["Outer.afterSection"] - 1], "def afterSection := 1")

    def test_catalog_and_bilingual_pages_include_actual_imports_and_fqn(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for rel in (SELECTIVE, STOPPING):
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(SOURCE / rel, root / rel)
            # Exercise the serial fallback deterministically without spawning test workers.
            with patch.object(build_site, "ProcessPoolExecutor", side_effect=OSError):
                catalog = build_site.scan_catalog_sources(root)
        units = {unit["id"]: unit for unit in catalog["units"]}
        for lang in ("en", "zh"):
            qft = build_site.build_unit_detail_body(
                unit=units["AbelianDecoders"], lang=lang, root_prefix="../", all_unit_ids=set(units))
            for imported in SELECTIVE_IMPORTS:
                self.assertIn(imported, qft)
            self.assertIn("Layer imports" if lang == "en" else "跨层导入", qft)
            stopping = build_site.build_unit_detail_body(
                unit=units["AEMeanReadout"], lang=lang, root_prefix="../", all_unit_ids=set(units))
            self.assertIn("Qatlib.Concepts.AEMeanReadout.LocalAEBackend.finiteSurvival", stopping)


if __name__ == "__main__":
    unittest.main()
