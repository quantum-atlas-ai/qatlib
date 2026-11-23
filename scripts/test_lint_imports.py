#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Exercise the compiled native linter on small source trees with real Lean headers."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
COPYRIGHT = """/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

"""


class NativeImportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.linter = Path(os.environ.get("QATLIB_LINT_EXE", ROOT / ".lake/build/bin/lint")).resolve()
        if not cls.linter.is_file():
            raise RuntimeError(f"Build the native driver with lake build lint first: {cls.linter}")

    def lint(self, imports, root_first_import="public import Qatlib.Foundations.Early"):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = {
                "Qatlib.lean": COPYRIGHT +
                    root_first_import + "\npublic import Qatlib.Papers.Later\n",
                "Qatlib/Foundations/Early.lean": COPYRIGHT + imports +
                    "\n\nnamespace Qatlib.Foundations.Early\n"
                    "/-- A small source-tree fixture. -/\ndef value : Nat := 0\n"
                    "end Qatlib.Foundations.Early\n",
                "Qatlib/Papers/Later.lean": COPYRIGHT +
                    "namespace Qatlib.Papers.Later\n"
                    "/-- A small source-tree fixture. -/\ndef value : Nat := 0\n"
                    "end Qatlib.Papers.Later\n",
                "docs/references.bib": "@misc{FixtureReference,\n  title = {Parser fixture}\n}\n",
                "NOTICE": (ROOT / "NOTICE").read_text(encoding="utf-8"),
            }
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            return subprocess.run([str(self.linter)], cwd=root, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)

    def test_six_valid_header_cases_preserve_layer_boundary(self):
        cases = (
            ("ordinary legal", "import Lean", False),
            ("ordinary reverse", "public import Qatlib.Papers.Later", True),
            ("multiline reverse", "public import\n  Qatlib.Papers.Later", True),
            ("comment-separated reverse", "public import /- gap -/ Qatlib.Papers.Later", True),
            ("private all reverse", "import all Qatlib.Papers.Later", True),
            ("commented reverse", "/- Example:\nimport Qatlib.Papers.Later\n"
             "/- nested example -/\n-/\nimport Lean", False),
        )
        for label, source, reverse in cases:
            with self.subTest(label=label):
                result = self.lint(source)
                self.assertEqual(result.returncode, 1 if reverse else 0, result.stdout)
                self.assertEqual("ERR_LAY: Reverse layer import Qatlib.Papers.Later" in result.stdout,
                                 reverse, result.stdout)

    def test_missing_sources_and_aggregate_mathlib_remain_rejected(self):
        for source, diagnostic in (
                ("import Qatlib.Papers.Absent", "ERR_IMP: Missing source file"),
                ("import Mathlib", "ERR_IMP: Only the top-level aggregate")):
            with self.subTest(source=source):
                result = self.lint(source)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(diagnostic, result.stdout)

    def test_invalid_header_fails_instead_of_becoming_an_empty_import_list(self):
        result = self.lint("import )")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Invalid Lean import header", result.stdout)

    def test_root_requires_public_imports(self):
        module = "Qatlib.Foundations.Early"
        result = self.lint("import Lean", f"public import /- gap -/\n  {module}")
        self.assertEqual(result.returncode, 0, result.stdout)
        for command in ("import", "meta import", "public meta import"):
            with self.subTest(command=command):
                result = self.lint("import Lean", f"{command} {module}")
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(f"ERR_ROOT: Expected 'public import {module}'", result.stdout)


if __name__ == "__main__":
    unittest.main()
