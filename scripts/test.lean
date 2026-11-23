/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Lean

public section

/-!
# Qatlib Kernel Environment Soundness & Axiom Auditor (`lake test` / `lake exe test`)

Loads compiled library and verification artifacts into the Lean 4 kernel environment via `lake -q --no-build lean`
(so Lake resolves `importArts` directly from `LAKE_CACHE_DIR/artifacts/` even on zero-unpack
`LAKE_ARTIFACT_CACHE=true` builds where `.lake/build/lib/lean/` contains no unpacked `.olean`s)
and runs `Lean.collectAxioms` (transitive axiom closure) across all audited declarations.

- **Full audit** (`lake test` or `lake exe test`): builds `QatlibTests` with warnings as errors,
  then audits all declarations from both `Qatlib` and `verification/`.
- **Targeted module audit** (`lake exe test Qatlib.Foundations.Foo ...`): audits only the named module(s).
- Both modes import private module data. Full mode explicitly loads every module listed in
  `Qatlib.lean` and each verification source module, including leaves absent from `QatlibTests.lean`.
- Add `--keep-probe` to retain the generated audit source for inspection.

## Why Kernel-Level `.olean` Auditing Instead of Source Text Search (`grep sorry`)?
In Lean 4, a proof can silently depend on `sorryAx` or unverified computation axioms without
the word `sorry` or `axiom` ever appearing in the `.lean` source text—for example, via:
- macro or elaborator (`elab`) fallbacks that synthesize `sorryAx` under the hood,
- partial or non-terminating definitions, or
- `native_decide` (`Lean.ofReduceBool`), which trusts external native code evaluation.

Inspecting the compiled kernel environment with `collectAxioms` provides a kernel-level
mathematical guarantee that each audited declaration depends exclusively on Lean's three
standard foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
-/

open System

def buildHarnessSource (importMods : Array String) (isTargeted : Bool)
    (scopeMods verificationMods : Array String) : String :=
  let importBlock := "\n".intercalate (importMods.toList.map (s!"import all {·}"))
  let targetList := ", ".intercalate (scopeMods.toList.map (s!"`{·}"))
  let verificationList := ", ".intercalate (verificationMods.toList.map (s!"`{·}"))
  s!"module

import Lean
{importBlock}

set_option maxHeartbeats 0

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let isTargeted : Bool := {if isTargeted then "true" else "false"}
  let targetSet : Std.HashSet Name := Std.HashSet.ofList [{targetList}]
  let verificationSet : Std.HashSet Name := Std.HashSet.ofList [{verificationList}]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for modName in verificationSet do
    if (env.getModuleIdx? modName).isNone then
      throwError s!\"AXIOM_AUDIT_ERROR: missing verification module '\{modName}'\"
  let mut checked : Nat := 0
  let mut privateChecked : Nat := 0
  let mut verificationChecked : Nat := 0
  let mut verificationPrivateChecked : Nat := 0
  for modName in env.header.moduleNames, data in env.header.moduleData do
    let isVerification := verificationSet.contains modName
    let inScope :=
      if isTargeted then
        targetSet.contains modName
      else
        isVerification || (`Qatlib).isPrefixOf modName
    unless inScope do continue
    for name in data.constNames do
      checked := checked + 1
      let isPrivate := isPrivateName name
      if isPrivate then
        privateChecked := privateChecked + 1
      if isVerification then
        verificationChecked := verificationChecked + 1
        if isPrivate then
          verificationPrivateChecked := verificationPrivateChecked + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError s!\"AXIOM_AUDIT_ERROR: unexpected axiom '\{axiomName}' in declaration '\{name}' (module \{modName})\"
  if checked == verificationChecked then
    throwError \"AXIOM_AUDIT_ERROR: no library or selected project declarations audited\"
  if !isTargeted && privateChecked == verificationPrivateChecked then
    throwError \"AXIOM_AUDIT_ERROR: no private library declarations audited\"
  IO.println s!\"SORRY_FREE_OK declarations=\{checked}\"
  IO.println s!\"AXIOM_AUDIT_OK declarations=\{checked} private=\{privateChecked}\"
  unless isTargeted do
    IO.println s!\"VERIFICATION_AXIOM_AUDIT_OK modules=\{verificationSet.size} declarations=\{verificationChecked} private=\{verificationPrivateChecked}\"
"

private def rootAuditModules : IO (Array String) := do
  let source ← IO.FS.readFile "Qatlib.lean"
  let input := Lean.Parser.mkInputContext source "Qatlib.lean"
  let (header, _, messages) ← Lean.Parser.parseHeader input
  if messages.hasErrors then
    throw <| IO.userError "AXIOM_AUDIT_ERROR: errors while parsing Qatlib import header"
  let mut imports := #["Qatlib"]
  if let `(Lean.Parser.Module.header| $[module]? $[prelude]? $importsStx*) := header then
    for stx in importsStx do
      if let `(Lean.Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := stx then
        imports := imports.push mod.getId.toString
  else
    throw <| IO.userError "AXIOM_AUDIT_ERROR: cannot parse Qatlib import header"
  return imports

private def verificationAuditModules : IO (Array String) := do
  let dir : FilePath := "verification"
  let files ← (← dir.walkDir).filterM fun file => do
    return file.extension == some "lean" && !(← file.isDir)
  if files.isEmpty then
    throw <| IO.userError "AXIOM_AUDIT_ERROR: no verification Lean sources found"
  let files := files.qsort (fun a b => a.toString < b.toString)
  files.mapM fun file => do
    let modName ← Lean.moduleNameOfFileName file (some dir)
    -- Match the QatlibTests globs in lakefile.toml. A misplaced source could
    -- otherwise resolve to an artifact from the library or a dependency.
    unless (`QatlibTests).isPrefixOf modName do
      throw <| IO.userError s!"AXIOM_AUDIT_ERROR: {file} is outside the QatlibTests target"
    return modName.toString

def main (args : List String) : IO UInt32 := do
  let modArgs := (args.filter (fun a => !a.startsWith "-")).toArray
  let isTargeted := !modArgs.isEmpty
  let verificationMods ← if isTargeted then pure #[] else verificationAuditModules
  unless isTargeted do
    let consumers ← IO.Process.spawn {
      cmd := "lake"
      args := #["--fail-fast", "build", "--wfail", "QatlibTests"]
      stdin := .inherit
      stdout := .inherit
      stderr := .inherit
    }
    let rc ← consumers.wait
    unless rc == 0 do return rc
  let importMods ← if isTargeted then pure modArgs else pure ((← rootAuditModules) ++ verificationMods)
  let scopeMods := if isTargeted then modArgs else #[]
  let keepProbe := args.contains "--keep-probe"

  IO.println s!"=== Running Kernel Environment Soundness & Axiom Audit (scope={if isTargeted then "selected" else "full"}) ==="
  let tmpDir : FilePath := ".lake" / "qatlas-tmp"
  IO.FS.createDirAll tmpDir
  let stamp ← IO.monoNanosNow
  let probeFile := tmpDir / s!"axiom_audit_{stamp}.lean"
  IO.FS.writeFile probeFile (buildHarnessSource importMods isTargeted scopeMods verificationMods)
  if keepProbe then IO.println s!"AXIOM_AUDIT_PROBE {probeFile}"
  try
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["-q", "--no-build", "lean", probeFile.toString]
      stdin := .inherit
      stdout := .inherit
      stderr := .inherit
    }
    let rc ← child.wait
    unless keepProbe do
      try IO.FS.removeFile probeFile catch _ => pure ()
    return rc
  catch e =>
    unless keepProbe do
      try IO.FS.removeFile probeFile catch _ => pure ()
    IO.eprintln s!"AXIOM_AUDIT_ERROR: failed to execute lake --no-build lean: {e}"
    return 1
