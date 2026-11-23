#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Source-parser regressions for portal imports, declaration identities and output."""

from __future__ import annotations

from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import build_site

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
