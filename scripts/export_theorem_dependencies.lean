/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Lean.DeclarationRange
import Lean.Util.FoldConsts
import Lean.Data.Json.FromToJson

/-!
# Theorem dependencies for the documentation site

Read the public names, server declaration ranges, and private proof bodies of
compiled modules. Emit direct constant references in the elaborated type and
proof of each public theorem. The site packer resolves those references against
the public Qatlib theorems.
-/

open Lean System

/-- Names with their own declaration range in the module's server part.
The extension stores `Name × DeclarationRanges` entries (see
`Lean.declRangeExt`). Looking up the exact name avoids inheriting the
range of an inductive declaration for one of its generated helpers. -/
unsafe def namesWithRanges (part : ModuleData) : NameSet := Id.run do
  let some (_, entries) := part.entries.find? (fun (name, _) => name == declRangeExt.name)
    | return {}
  let ranges : Array (Name × DeclarationRanges) := unsafeCast entries
  return ranges.foldl (fun names (name, _) => names.insert name) {}

/-- Write the exported theorems and their direct references as JSON lines. -/
unsafe def exportTheorems (out : IO.FS.Stream) (root : FilePath) (source : String) : IO Unit := do
  let base := root / FilePath.mk source |>.withExtension "olean"
  let parts ← readModuleDataParts #[base, OLeanLevel.adjustFileName base .server,
    OLeanLevel.adjustFileName base .private]
  let #[(publicPart, _), (serverPart, _), (privatePart, _)] := parts
    | throw (IO.userError s!"missing module parts for {source}")
  let publicNames := publicPart.constNames.foldl (fun (names : NameSet) n => names.insert n) {}
  let rangedNames := namesWithRanges serverPart
  for c in privatePart.constants do
    if let .thmInfo thm := c then
      if publicNames.contains thm.name && rangedNames.contains thm.name then
        let refs := thm.type.getUsedConstantsAsSet ++ thm.value.getUsedConstantsAsSet
        let refs := refs.toArray.map Name.toString
        out.putStrLn (Json.arr #[toJson source, toJson thm.name.toString, toJson refs]).compress

/-- Export a bounded batch of modules relative to the supplied artifact directory. -/
unsafe def main (args : List String) : IO Unit := do
  match args with
  | root :: sources =>
    let out ← IO.getStdout
    for source in sources do
      exportTheorems out (FilePath.mk root) source
  | _ => throw (IO.userError "expected an artifact directory and Qatlib source paths")
