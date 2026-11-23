#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Run the source and compiled axiom gates on dependency-free Lake fixtures."""

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
LAKEFILE = """name = "Qatlib"
defaultTargets = ["Qatlib"]
testDriver = "test"

[leanOptions]
autoImplicit = false
warningAsError = true

[[lean_lib]]
name = "Qatlib"
requiresModuleSystem = true

[[lean_lib]]
name = "QatlibTests"
srcDir = "verification"
requiresModuleSystem = true
globs = ["QatlibTests", "QatlibTests.+"]

[[lean_exe]]
name = "test"
srcDir = "scripts"
supportInterpreter = true
"""
LIBRARY = "Qatlib/Foundations/Seed.lean"
CONSUMER = "verification/QatlibTests/Consumer.lean"
UNLISTED = "verification/QatlibTests/Unlisted.lean"
UNSUPPORTED_PROOF = """\nsection LocalEvidence
private axiom fixtureUnsupported : False
private theorem fixtureAssertion : (0 : Nat) = 1 := False.elim fixtureUnsupported
#print axioms fixtureAssertion
end LocalEvidence
"""


class VerificationAxiomAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.linter = Path(os.environ.get("QATLIB_LINT_EXE", ROOT / ".lake/build/bin/lint")).resolve()
        if not cls.linter.is_file():
            raise RuntimeError(f"Build the native driver with lake build lint first: {cls.linter}")

    def run_fixture(self, modified=None, addition=""):
        files = {
            "lean-toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
            "lakefile.toml": LAKEFILE,
            "scripts/test.lean": (ROOT / "scripts/test.lean").read_text(encoding="utf-8"),
            "NOTICE": (ROOT / "NOTICE").read_text(encoding="utf-8"),
            "docs/references.bib": "@misc{AuditFixture, title = {Axiom audit fixture}}\n",
            "Qatlib.lean": COPYRIGHT + "public import Qatlib.Foundations.Seed\n",
            LIBRARY: COPYRIGHT + """namespace Qatlib.Foundations.Seed
private def helper : Nat := 0
@[expose] public section
/-- A public value used by the fixture consumer. -/
def value : Nat := 0
end
end Qatlib.Foundations.Seed
""",
            "verification/QatlibTests.lean": COPYRIGHT + "public import QatlibTests.Consumer\n",
            CONSUMER: COPYRIGHT + """import Qatlib

section Consumer
private theorem usesLibrary : Qatlib.Foundations.Seed.value = 0 := rfl
end Consumer
""",
            UNLISTED: COPYRIGHT + "private def unreferencedHelper : Nat := 1\n",
        }
        if modified is not None:
            files[modified] = files.get(modified, COPYRIGHT) + addition
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory)
            for name, source in files.items():
                path = fixture / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")

            # Reused artifacts can suppress the fixture's `#print axioms` output.
            env = {
                **os.environ,
                "LAKE_CACHE_DIR": str(fixture / ".lake" / "cache"),
                "LEAN_NUM_THREADS": "1",
            }
            options = {"cwd": fixture, "env": env, "stdout": subprocess.PIPE,
                      "stderr": subprocess.STDOUT, "text": True, "timeout": 180}
            lint = subprocess.run([str(self.linter)], **options)
            audit = subprocess.run(["lake", "--fail-fast", "test"], **options)
            return lint, audit

    def assert_rejected(self, file, source, module, axiom):
        lint, audit = self.run_fixture(file, source)
        self.assertEqual(lint.returncode, 1, lint.stdout)
        self.assertIn("forbidden custom-axiom", lint.stdout)
        self.assertEqual(audit.returncode, 1, audit.stdout)
        self.assertIn("Build completed successfully", audit.stdout)
        error = next((line for line in audit.stdout.splitlines() if "AXIOM_AUDIT_ERROR:" in line), "")
        self.assertIn("unexpected axiom", error, audit.stdout)
        self.assertIn(axiom, error)
        self.assertIn(f"(module {module})", error)
        return audit.stdout

    def test_clean_verification_and_library(self):
        lint, audit = self.run_fixture()
        self.assertEqual(lint.returncode, 0, lint.stdout)
        self.assertEqual(audit.returncode, 0, audit.stdout)
        self.assertIn("AXIOM_AUDIT_OK", audit.stdout)
        self.assertRegex(audit.stdout,
                         r"VERIFICATION_AXIOM_AUDIT_OK modules=3 declarations=\d+ private=[1-9]\d*")

    def test_false_verification_assertion_depends_on_private_axiom(self):
        output = self.assert_rejected(
            CONSUMER, UNSUPPORTED_PROOF, "QatlibTests.Consumer", "fixtureUnsupported")
        self.assertRegex(output, r"fixtureAssertion.*depends on axioms: .*fixtureUnsupported")

    def test_unused_private_axiom_in_module_absent_from_root_imports(self):
        self.assert_rejected(UNLISTED, "\nprivate axiom fixtureUnused : True\n",
                             "QatlibTests.Unlisted", "fixtureUnused")

    def test_library_negative_control_is_still_rejected(self):
        self.assert_rejected(
            LIBRARY, UNSUPPORTED_PROOF, "Qatlib.Foundations.Seed", "fixtureUnsupported")

    def test_source_outside_test_target_cannot_alias_the_library_root(self):
        _, audit = self.run_fixture("verification/Qatlib.lean", "\nprivate def hidden : Nat := 0\n")
        self.assertEqual(audit.returncode, 1, audit.stdout)
        self.assertIn("AXIOM_AUDIT_ERROR: verification/Qatlib.lean is outside the QatlibTests target",
                      audit.stdout)


if __name__ == "__main__":
    unittest.main()
