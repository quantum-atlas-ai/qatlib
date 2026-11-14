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

Loads compiled `Qatlib` artifacts into the Lean 4 kernel environment via `lake -q --no-build lean`
(so Lake resolves `importArts` directly from `LAKE_CACHE_DIR/artifacts/` even on zero-unpack
`LAKE_ARTIFACT_CACHE=true` builds where `.lake/build/lib/lean/` contains no unpacked `.olean`s)
and runs `Lean.collectAxioms` (transitive axiom closure) across all audited declarations.

- **Full library audit** (`lake test` or `lake exe test`): audits all declarations under `Qatlib`.
- **Targeted module audit** (`lake exe test Qatlib.Foundations.Foo ...`): audits only the named module(s).
- Both modes import private module data; full mode explicitly loads every module listed in
  `Qatlib.lean`, including private helpers unused by the public interface.
- Add `--keep-probe` to retain the generated audit source for inspection.

## Why Kernel-Level `.olean` Auditing Instead of Source Text Search (`grep sorry`)?
In Lean 4, a proof can silently depend on `sorryAx` or unverified computation axioms without
the word `sorry` or `axiom` ever appearing in the `.lean` source text—for example, via:
- macro or elaborator (`elab`) fallbacks that synthesize `sorryAx` under the hood,
- partial or non-terminating definitions, or
- `native_decide` (`Lean.ofReduceBool`), which trusts external native code evaluation.

Inspecting the compiled kernel environment with `collectAxioms` provides a kernel-level
mathematical guarantee that every theorem in `Qatlib` depends exclusively on Lean's three
standard foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
-/

open System

def buildHarnessSource (importMods : Array String) (isTargeted : Bool) (scopeMods : Array String) : String :=
  let importBlock := "\n".intercalate (importMods.toList.map (s!"import all {·}"))
  let targetList := ", ".intercalate (scopeMods.toList.map (s!"`{·}"))
  s!"module

import Lean
{importBlock}

set_option maxHeartbeats 0

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let isTargeted : Bool := {if isTargeted then "true" else "false"}
  let targetSet : Std.HashSet Name := Std.HashSet.ofList [{targetList}]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut privateChecked : Nat := 0
  for modName in env.header.moduleNames, data in env.header.moduleData do
    let inScope :=
      if isTargeted then
        targetSet.contains modName
      else
        (`Qatlib).isPrefixOf modName
    unless inScope do continue
    for name in data.constNames do
      checked := checked + 1
      if name.toString.startsWith \"_private.\" then
        privateChecked := privateChecked + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          IO.eprintln s!\"AXIOM_AUDIT_ERROR: unexpected axiom '\{axiomName}' in declaration '\{name}'\"
          IO.Process.exit 1
  if checked == 0 then
    IO.eprintln \"AXIOM_AUDIT_ERROR: no project declarations audited\"
    IO.Process.exit 1
  IO.println s!\"SORRY_FREE_OK declarations=\{checked}\"
  if !isTargeted && privateChecked == 0 then
    IO.eprintln \"AXIOM_AUDIT_ERROR: no private project declarations audited\"
    IO.Process.exit 1
  IO.println s!\"AXIOM_AUDIT_OK declarations=\{checked} private=\{privateChecked}\"
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

def main (args : List String) : IO UInt32 := do
  let modArgs := (args.filter (fun a => !a.startsWith "-")).toArray
  let isTargeted := !modArgs.isEmpty
  let importMods ← if isTargeted then pure modArgs else rootAuditModules
  let scopeMods := if isTargeted then modArgs else #[]
  let keepProbe := args.contains "--keep-probe"

  IO.println s!"=== Running Kernel Environment Soundness & Axiom Audit (scope={if isTargeted then "selected" else "full"}) ==="
  let tmpDir : FilePath := ".lake" / "qatlas-tmp"
  IO.FS.createDirAll tmpDir
  let stamp ← IO.monoNanosNow
  let probeFile := tmpDir / s!"axiom_audit_{stamp}.lean"
  IO.FS.writeFile probeFile (buildHarnessSource importMods isTargeted scopeMods)
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
