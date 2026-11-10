/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Lean

/-!
# Qatlib Kernel Environment Soundness & Axiom Auditor (`lake test` / `lake exe test`)

Loads all compiled `.olean` files of `Qatlib` into the Lean 4 kernel environment and runs
`Lean.collectAxioms` (transitive axiom closure) across all 248,000+ declarations in `Qatlib`.

## Why Kernel-Level `.olean` Auditing Instead of Source Text Search (`grep sorry`)?
In Lean 4, a proof can silently depend on `sorryAx` or unverified computation axioms without
the word `sorry` or `axiom` ever appearing in the `.lean` source text—for example, via:
- macro or elaborator (`elab`) fallbacks that synthesize `sorryAx` under the hood,
- partial or non-terminating definitions, or
- `native_decide` (`Lean.ofReduceBool`), which trusts external native code evaluation.

Inspecting the compiled `.olean` environment with `collectAxioms` provides a kernel-level
mathematical guarantee that every theorem in `Qatlib` depends exclusively on Lean's three
standard foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
-/

open Lean

unsafe def main (_args : List String) : IO UInt32 := do
  IO.println "=== Running Kernel Environment Soundness & Axiom Audit ==="
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules (loadExts := true) #[{ module := `Qatlib }] {} 0
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ctx : Core.Context := { fileName := "", options := {}, fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let ((checked, bad?), _) ← Lean.Core.CoreM.toIO (ctx := ctx) (s := state) do
    let mut checked : Nat := 0
    for module in env.header.moduleNames, data in env.header.moduleData do
      unless (`Qatlib).isPrefixOf module do continue
      for name in data.constNames do
        checked := checked + 1
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            return (checked, some (name, axiomName))
    return (checked, none)
  if let some (name, axiomName) := bad? then
    IO.eprintln s!"AXIOM_AUDIT_ERROR: unexpected axiom '{axiomName}' in declaration '{name}'"
    return 1
  if checked == 0 then
    IO.eprintln "AXIOM_AUDIT_ERROR: no project declarations audited"
    return 1
  IO.println s!"SORRY_FREE_OK declarations={checked}"
  IO.println s!"AXIOM_AUDIT_OK declarations={checked}"
  return 0
