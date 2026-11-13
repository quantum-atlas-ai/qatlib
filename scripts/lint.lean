/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Lean

/-!
# Qatlib Static Source, Style & Import Linter (`lake lint` / `lake exe lint`)

Runs fast, read-only static checks across the repository (~1 second):
1. **Source & Style Check**:
   - Standard Apache-2.0 copyright header on all `.lean` files.
   - Allowed top-level directories under `Qatlib/` (`Foundations`, `Concepts`, `Papers`),
     strict `UpperCamelCase` on all directory and `.lean` file names, and zero
     case-insensitive file or directory path collisions (`ERR_CASE`).
   - Unix `\n` line endings, no trailing whitespace, no `" ;"` before semicolons.
   - No forbidden debug options (`set_option pp.*`, `profiler.*`, `trace.*`).
2. **Module Tree & Import Check**:
   - All `.lean` files under `Qatlib/` are imported in `Qatlib.lean` in sorted order.
   - No bare `import Mathlib` in library modules.
   - Every `import Qatlib.*` statement resolves to an existing `.lean` file on disk.
   - Dependencies follow Foundations ← Concepts ← Papers; reverse imports report `ERR_LAY`.

For kernel-level `.olean` soundness and axiom auditing across all compiled declarations,
run `lake test` (`lake exe test`, implemented in `scripts/test.lean`).
-/

open System

/-- Check whether `s` contains `sub` as a substring. -/
@[inline] def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Recursively collect all `.lean` files under `dir`. -/
partial def collectLeanFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut acc : Array FilePath := #[]
  if !(← dir.pathExists) then
    return acc
  let entries ← dir.readDir
  let sorted := entries.qsort (fun a b => a.fileName < b.fileName)
  for entry in sorted do
    let p := entry.path
    if ← p.isDir then
      acc := acc ++ (← collectLeanFiles p)
    else if p.extension == some "lean" then
      acc := acc.push p
  return acc

/-- Recursively detect case-insensitive file or directory collisions across the repository. -/
partial def collectCaseCollisions (dir : FilePath) : IO (Array String) := do
  let mut errs : Array String := #[]
  if !(← dir.pathExists) then
    return errs
  let entries ← dir.readDir
  let sorted := entries.qsort (fun a b => a.fileName < b.fileName)
  let mut seenLower : Std.HashMap String String := {}
  for entry in sorted do
    let name := entry.fileName
    if name == ".git" || name == ".lake" || name == "_site" || name == "__pycache__" then
      continue
    let lower := name.toLower
    let childPath : FilePath := if dir == FilePath.mk "." then FilePath.mk name else dir / name
    let relCurr := childPath.toString
    if let some prev := seenLower[lower]? then
      let relPrev := if dir == FilePath.mk "." then prev else (dir / prev).toString
      errs := errs.push s!"{relCurr}:1: ERR_CASE: Case-insensitive path collision with '{relPrev}'"
    else
      seenLower := seenLower.insert lower name
    if ← childPath.isDir then
      errs := errs ++ (← collectCaseCollisions childPath)
  return errs

/-- Check whether `s` matches `^[A-Z][A-Za-z0-9]*$`. -/
def isUpperCamelCase (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isUpper && cs.all (fun ch => ch.isAlphanum)

/-- Convert a relative path `Qatlib/Foo/Bar.lean` to module name `Qatlib.Foo.Bar`. -/
def pathToModuleString (p : FilePath) : String :=
  let s := p.withExtension "" |>.toString
  s.replace "/" "." |>.replace "\\" "."

/-- Check Apache-2.0 copyright header in the first 15 lines of a file. -/
def checkCopyrightHeader (lines : Array String) : Option String := Id.run do
  if lines.size < 5 || lines[0]! != "/-" then
    return some "Malformed or missing Apache-2.0 copyright header"
  let mut closed := false
  let mut hasCopyright := false
  let mut hasApache := false
  let mut hasAuthors := false
  let limit := Nat.min lines.size 15
  for i in [0:limit] do
    let line := lines[i]!
    if hasSubstr line "Copyright" then hasCopyright := true
    if hasSubstr line "Apache" then hasApache := true
    if hasSubstr line "Author" then
      hasAuthors := true
      if !line.startsWith "Authors: " || hasSubstr line "  " ||
         hasSubstr line " and " || line.endsWith "." then
        return some s!"Malformed Authors line at line {i + 1}"
    if line == "-/" then
      closed := true
      break
  if !closed || !hasCopyright || !hasApache || !hasAuthors then
    return some "Malformed or missing Apache-2.0 copyright header"
  return none

/-- Parse header imports with Lean's parser, including comments and import modifiers. -/
def extractHeaderImports (lines : Array String) : IO (Array (Nat × String)) := do
  let inputCtx := Lean.Parser.mkInputContext ("\n".intercalate lines.toList) "<lint>"
  let (header, _, _) ← Lean.Parser.parseHeader inputCtx
  let mut imports : Array (Nat × String) := #[]
  if let `(Lean.Parser.Module.header| $[module]? $[prelude]? $importsStx*) := header then
    for stx in importsStx do
      if let `(Lean.Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := stx then
        let line := (inputCtx.fileMap.toPosition (mod.raw.getPos?.getD 0)).line
        imports := imports.push (line, mod.getId.toString)
  return imports

/-- Run static style and import checks in a single pass. -/
def runStaticChecks : IO UInt32 := do
  IO.println "=== Running Static Source, Style & Import Linter ==="
  let qatlibFiles ← collectLeanFiles "Qatlib"
  let allFiles := #[FilePath.mk "Qatlib.lean"] ++ qatlibFiles
  let mut errors ← collectCaseCollisions "."

  let mut moduleSet : Std.HashSet String := {}
  let mut expectedRootImports : Array String := #[]
  for path in qatlibFiles do
    let modName := pathToModuleString path
    moduleSet := moduleSet.insert modName
    expectedRootImports := expectedRootImports.push s!"import {modName}"

  let rootLines ← IO.FS.lines "Qatlib.lean"
  let rootHeaderImports ← extractHeaderImports rootLines
  let mut seenRootLower : Std.HashMap String String := {}
  for (lineNo, modName) in rootHeaderImports do
    let lowerMod := modName.toLower
    if let some prevMod := seenRootLower[lowerMod]? then
      if prevMod != modName then
        errors := errors.push s!"Qatlib.lean:{lineNo}: ERR_CASE: Case-insensitive module collision '{modName}' vs '{prevMod}'"
    else
      seenRootLower := seenRootLower.insert lowerMod modName
  let rootImports := rootHeaderImports.map (fun (_, m) => s!"import {m}")
  -- Aggregate generation sorts module names, not directory-entry names. A file
  -- `Foo.lean` and a directory `Foo/` must follow that same module-name order.
  expectedRootImports := expectedRootImports.qsort (· < ·)
  if rootImports != expectedRootImports then
    errors := errors.push "Qatlib.lean:1: ERR_ROOT: Qatlib.lean imports do not match sorted Qatlib/ module list"

  for path in allFiles do
    let relStr := path.toString
    if relStr.startsWith "Qatlib/" then
      let parts := (path.withExtension "").components
      match parts with
      | "Qatlib" :: top :: _ =>
        if !(["Foundations", "Concepts", "Papers"].contains top) then
          errors := errors.push s!"{relStr}:1: ERR_DIR: Top-level Qatlib directory '{top}' must be one of Foundations, Concepts, or Papers"
      | _ =>
        errors := errors.push s!"{relStr}:1: ERR_DIR: Invalid Qatlib module path"
      for part in parts do
        if !isUpperCamelCase part then
          errors := errors.push s!"{relStr}:1: ERR_CAM: '{part}' is not strict UpperCamelCase"

    let bodyLines ← IO.FS.lines path
    if let some hdrErr := checkCopyrightHeader bodyLines then
      errors := errors.push s!"{relStr}:1: ERR_COP: {hdrErr}"

    let imports ← extractHeaderImports bodyLines
    for (lineNo, modName) in imports do
      if modName == "Mathlib" then
        errors := errors.push s!"{relStr}:{lineNo}: ERR_IMP: Bare 'import Mathlib' is forbidden; import specific Mathlib.* modules"
      else if modName.startsWith "Qatlib." then
        if !moduleSet.contains modName then
          errors := errors.push s!"{relStr}:{lineNo}: ERR_IMP: Missing source file for import {modName}"
      let importsConcepts := modName == "Qatlib.Concepts" || modName.startsWith "Qatlib.Concepts."
      let importsPapers := modName == "Qatlib.Papers" || modName.startsWith "Qatlib.Papers."
      if (relStr.startsWith "Qatlib/Foundations/" && (importsConcepts || importsPapers)) ||
         (relStr.startsWith "Qatlib/Concepts/" && importsPapers) then
        errors := errors.push s!"{relStr}:{lineNo}: ERR_LAY: Reverse layer import {modName}"

    for i in [0:bodyLines.size] do
      let line := bodyLines[i]!
      let lineNo := i + 1
      if line.endsWith "\r" then
        errors := errors.push s!"{relStr}:{lineNo}: ERR_WIN: Windows CR/LF line endings detected"
      if line.endsWith " " || line.endsWith "\t" then
        errors := errors.push s!"{relStr}:{lineNo}: ERR_TWS: Trailing whitespace"
      if line.contains 's' && (hasSubstr line "set_option pp." ||
         hasSubstr line "set_option profiler." ||
         hasSubstr line "set_option trace.") then
        let stripped := line.trimAsciiStart.toString
        if !stripped.startsWith "--" &&
           (stripped.startsWith "set_option pp." ||
            stripped.startsWith "set_option profiler." ||
            stripped.startsWith "set_option trace.") then
          errors := errors.push s!"{relStr}:{lineNo}: ERR_OPT: Forbidden debug set_option"
      if line.contains ';' && hasSubstr line " ;" then
        let stripped := line.trimAsciiStart.toString
        if !stripped.startsWith "--" then
          errors := errors.push s!"{relStr}:{lineNo}: ERR_SEM: Space before semicolon"

  if !errors.isEmpty then
    for err in errors do
      IO.eprintln err
    IO.eprintln s!"LINT_FAILED errors={errors.size}"
    return 1

  IO.println s!"LINT_STYLE_OK files={allFiles.size} errors=0"
  IO.println s!"CHECK_IMPORTS_OK modules={qatlibFiles.size} errors=0"
  return 0

def main (_args : List String) : IO UInt32 :=
  runStaticChecks
