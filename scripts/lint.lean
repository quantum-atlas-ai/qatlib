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
  -- Imports in Qatlib are one per header line. A small lexical scan avoids
  -- constructing a full Lean syntax tree for each of the ten thousand files.
  let mut imports : Array (Nat × String) := #[]
  for i in [0:lines.size] do
    let raw := lines[i]!
    let mut line := raw.trimAscii.toString
    let mut changed := true
    while changed do
      changed := false
      for pfx in ["public ", "meta ", "all ", "module ", "prelude "] do
        if line.startsWith pfx then
          line := line.drop pfx.length |>.toString
          changed := true
    if line.startsWith "import " then
      let rest := line.drop 7 |>.toString
      let mod := String.ofList (rest.toList.takeWhile (fun c => c.isAlphanum || c == '_' || c == '.'))
      if !mod.isEmpty then imports := imports.push (i + 1, mod)
  return imports

/-- Return the first line containing `needle`, case-insensitively. -/
def asciiLower (s : String) : String :=
  String.ofList (s.toList.map (fun c =>
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c))

def firstLineContaining (lines : Array String) (needle : String) : Nat := Id.run do
  let lowered := asciiLower needle
  let mut result := 1
  for i in [0:lines.size] do
    if (asciiLower lines[i]!).contains lowered then
      result := i + 1
      break
  return result

/-- Case-insensitive substring check used for release-hygiene markers. -/
def containsCI (s needle : String) : Bool :=
  (asciiLower s).contains (asciiLower needle)

/-- Consume a quoted Lean string, preserving escaped characters. -/
partial def consumeString (xs : List Char) (out : Array Char) : List Char × Array Char :=
  match xs with
  | [] => ([], out)
  | '\\' :: c :: rest => consumeString rest (out.push '\\' |>.push c)
  | '"' :: rest => (rest, out.push '"')
  | c :: rest => consumeString rest (out.push c)

/-- Consume a line comment, retaining its terminating newline if present. -/
def consumeLineComment (xs : List Char) (out : Array Char) : List Char × Array Char :=
  match xs with
  | [] => ([], out)
  | '\n' :: rest => (rest, out.push '\n')
  | _ :: rest => consumeLineComment rest out

/-- Strip Lean comments while preserving newlines for stable line diagnostics. -/
partial def stripCommentsAux (xs : List Char) (depth : Nat) (out : Array Char) : Array Char :=
  match xs with
  | [] => out
  | '/' :: '-' :: rest =>
      if depth == 0 then stripCommentsAux rest 1 out
      else stripCommentsAux rest (depth + 1) out
  | '-' :: '/' :: rest =>
      if depth == 0 then stripCommentsAux xs depth out
      else if depth == 1 then stripCommentsAux rest 0 out
      else stripCommentsAux rest (depth - 1) out
  | '\n' :: rest =>
      if depth == 0 then stripCommentsAux rest depth (out.push '\n')
      else stripCommentsAux rest depth (out.push '\n')
  | '"' :: rest =>
      if depth == 0 then
        let (remaining, copied) := consumeString rest (out.push '"')
        stripCommentsAux remaining depth copied
      else stripCommentsAux rest depth out
  | '-' :: '-' :: rest =>
      if depth == 0 then
        let (remaining, skipped) := consumeLineComment rest out
        stripCommentsAux remaining depth skipped
      else stripCommentsAux rest depth out
  | c :: rest =>
      if depth == 0 then stripCommentsAux rest depth (out.push c)
      else stripCommentsAux rest depth out

def stripComments (source : String) : String :=
  String.ofList (stripCommentsAux source.toList 0 #[] |>.toList)

structure DocComment where
  startLine : Nat
  text : String

/-- Consume one nested block comment and report its newline count. -/
partial def consumeBlockComment (xs : List Char) (depth : Nat) (buf : Array Char) : List Char × Array Char :=
  match xs with
  | [] => ([], buf)
  | '/' :: '-' :: rest =>
      consumeBlockComment rest (depth + 1) (buf.push '/' |>.push '-')
  | '-' :: '/' :: rest =>
      let nextBuf := buf.push '-' |>.push '/'
      if depth == 1 then (rest, nextBuf) else consumeBlockComment rest (depth - 1) nextBuf
  | c :: rest => consumeBlockComment rest depth (buf.push c)

partial def scanDocCommentsAux (xs : List Char) (line : Nat) (docs : Array DocComment) : Array DocComment :=
  match xs with
  | [] => docs
  | '/' :: '-' :: rest =>
      let isDoc := match rest with
        | '!' :: _ => true
        | '-' :: _ => true
        | _ => false
      let (remaining, buf) := consumeBlockComment rest 1 (#[ '/', '-' ])
      let text := String.ofList buf.toList
      let nextLine := line + (text.toList.count '\n')
      let docs := if isDoc then docs.push { startLine := line, text := text } else docs
      scanDocCommentsAux remaining nextLine docs
  | '-' :: '-' :: rest =>
      let (remaining, _) := consumeLineComment rest #[]
      let skipped := xs.takeWhile (· != '\n')
      let nextLine := line + (skipped.count '\n')
      scanDocCommentsAux remaining nextLine docs
  | '"' :: rest =>
      let (remaining, copied) := consumeString rest #['"']
      let nextLine := line + (copied.toList.count '\n')
      scanDocCommentsAux remaining nextLine docs
  | '\n' :: rest => scanDocCommentsAux rest (line + 1) docs
  | _ :: rest => scanDocCommentsAux rest line docs

def scanDocComments (source : String) : Array DocComment :=
  scanDocCommentsAux source.toList 1 #[]

/-- Count a run of one marker character. -/
partial def countMarkerRun (marker : Char) (xs : List Char) (n : Nat := 0) : Nat × List Char :=
  match xs with
  | c :: rest => if c == marker then countMarkerRun marker rest (n + 1) else (n, xs)
  | [] => (n, [])

/-- Mask one Markdown code span, preserving line structure. -/
partial def maskUntilMarker (marker : Char) (run : Nat) (xs : List Char)
    (maskedRev : List Char := []) : Option (List Char × List Char) :=
  match xs with
  | [] => none
  | c :: rest =>
      if c == marker then
        let (found, after) := countMarkerRun marker xs
        if found == run then
          some (after, (List.replicate run ' ' ++ maskedRev.reverse))
        else maskUntilMarker marker run rest (' ' :: maskedRev)
      else maskUntilMarker marker run rest (' ' :: maskedRev)

partial def maskMarkdownLine (xs : List Char) : List Char :=
  match xs with
  | [] => []
  | c :: rest =>
      if c == '`' || c == '~' then
        let (run, afterOpen) := countMarkerRun c xs
        let valid := c == '`' || run >= 3
        if valid then
          match maskUntilMarker c run afterOpen with
          | some (remaining, masked) => List.replicate run ' ' ++ masked ++ maskMarkdownLine remaining
          | none => List.replicate run c ++ maskMarkdownLine afterOpen
        else c :: maskMarkdownLine rest
      else c :: maskMarkdownLine rest

/-- Mask Markdown code spans/fences. Citations in code spans are ignored by the checker. -/
def maskMarkdownCode (source : String) : String :=
  "\n".intercalate (source.splitOn "\n" |>.map (fun line => String.ofList (maskMarkdownLine line.toList)))

/-- Whether a string is an author/year citation key. -/
def isAuthorYearKey (s : String) : Bool :=
  let chars := s.toList
  match chars with
  | [] => false
  | first :: rest =>
      let allowed := rest.all (fun c => c.isAlphanum || c == ':' || c == '_' || c == '-')
      let rec hasYear : List Char → Bool
        | a :: b :: c :: d :: tail =>
            (a.isDigit && b.isDigit && c.isDigit && d.isDigit) || hasYear (b :: c :: d :: tail)
        | _ => false
      first.isAlpha && allowed && hasYear chars

/-- Parse citation references in one documentation comment. -/
def checkDocCitations (comment : DocComment) (keys : Std.HashSet String) : Nat × Array String :=
  let masked := maskMarkdownCode comment.text
  let chars := masked.toList
  let isKeyChar (c : Char) := c.isAlphanum || c == ':' || c == '_' || c == '-'
  let rec scan : List Char → Nat → Nat → Nat → Nat → Array String → Nat × Array String
    | [], _, _, _, count, errors => (count, errors)
    | head :: rest, pos, lineOffset, skip, count, errors =>
        let nextLineOffset := if head == '\n' then lineOffset + 1 else lineOffset
        if skip > 0 then scan rest (pos + 1) nextLineOffset (skip - 1) count errors
        else if head != '[' then scan rest (pos + 1) nextLineOffset 0 count errors
        else
          let rec takeLabel : List Char → List Char → Option (List Char × List Char)
            | [], _ => none
            | ']' :: more, acc => some (acc.reverse, more)
            | '\n' :: _, _ => none
            | c :: more, acc => takeLabel more (c :: acc)
          match takeLabel rest [] with
          | none => scan rest (pos + 1) nextLineOffset 0 count errors
          | some (labelChars, afterLabel) =>
              let label := String.ofList labelChars
              let (target?, afterTarget) := match afterLabel with
                | '[' :: targetTail =>
                    match targetTail with
                    | first :: more =>
                        if first.isAlpha then
                          let rec takeTarget : List Char → List Char → Option (String × List Char)
                            | [], _ => none
                            | ']' :: tailMore, acc =>
                                if acc.all isKeyChar then some (String.ofList acc.reverse, tailMore) else none
                            | c :: tailMore, acc => takeTarget tailMore (c :: acc)
                          match takeTarget more [first] with
                          | some (target, more) => (some target, more)
                          | none => (none, afterLabel)
                        else (none, afterLabel)
                    | _ => (none, afterLabel)
                | _ => (none, afterLabel)
              let key := target?.getD label
              let inlineLink := target?.isNone && (match afterLabel with | '(' :: _ => true | ':' :: _ => true | _ => false)
              let candidate := !inlineLink && (target?.isSome || keys.contains key || isAuthorYearKey key)
              let count := if candidate then count + 1 else count
              let errors := if candidate && !keys.contains key then
                  errors.push s!"Qatlib citation line {comment.startLine + lineOffset}: unknown bibliography key `{key}`"
                else errors
              let consumed := rest.length - afterTarget.length
              scan rest (pos + 1) nextLineOffset (if consumed == 0 then 0 else consumed - 1) count errors
  scan chars 0 0 0 0 #[]

/-- Parse a BibTeX entry key from one line. -/
partial def parseBibKey (line : String) : Option String :=
  let chars := line.trimAsciiStart.toString.toList
  let rec skipSpaces : List Char → List Char
    | c :: rest => if c == ' ' || c == '\t' then skipSpaces rest else c :: rest
    | [] => []
  let rec takeWord : List Char → List Char → List Char × List Char
    | c :: rest, acc => if c.isAlphanum || c == '_' then takeWord rest (c :: acc) else (acc.reverse, c :: rest)
    | [], acc => (acc.reverse, [])
  match chars with
  | '@' :: rest =>
      let (kind, afterKind) := takeWord (skipSpaces rest) []
      if kind.isEmpty then none else
      match skipSpaces afterKind with
      | '{' :: afterBrace =>
          let afterBrace := skipSpaces afterBrace
          match afterBrace with
          | first :: restKey =>
              if !first.isAlpha then none else
              let rec takeKey : List Char → List Char → List Char × List Char
                | c :: more, acc => if c.isAlphanum || c == ':' || c == '_' || c == '-' then takeKey more (c :: acc) else (acc.reverse, c :: more)
                | [], acc => (acc.reverse, [])
              let (keyChars, afterKey) := takeKey restKey [first]
              match skipSpaces afterKey with
              | ',' :: _ => some (String.ofList keyChars)
              | _ => none
          | _ => none
      | _ => none
  | _ => none

structure PropDefInfo where
  file : String
  line : Nat
  name : String
  hasBanner : Bool

/-- Extract a declaration name after `def` on a source line. -/
def parsePropDefLine (line : String) : Option String :=
  let trimmed := line.trimAscii.toString
  let prefixes := ["def ", "public def ", "noncomputable def ", "public noncomputable def ", "noncomputable public def "]
  let prefix? := prefixes.find? (fun p => trimmed.startsWith p)
  match prefix? with
  | none => none
  | some pfx =>
      let rest := trimmed.drop pfx.length |>.toString
      let name := String.ofList (rest.toList.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\''))
      if name.isEmpty then none else
      let after := rest.drop name.length |>.toString
      let marker := if after.contains ": Prop :=" then ": Prop :=" else ":Prop :="
      if after.contains marker then
        let beforeMarker := (after.splitOn marker).headD ""
        if !beforeMarker.contains ":" && !beforeMarker.contains "=" then some name else none
      else none

/-- Identify a declaration line for root-namespace checking. -/
def parseDeclName (line : String) : Option String :=
  let t := line.trimAsciiStart.toString
  let modifiers := ["public ", "protected ", "noncomputable ", "public protected ", "public noncomputable ", "noncomputable public "]
  let t := modifiers.foldl (fun s p => if s.startsWith p then s.drop p.length |>.toString else s) t
  let keywords := ["def ", "abbrev ", "structure ", "class ", "inductive ", "theorem ", "lemma "]
  let kw? := keywords.find? (fun p => t.startsWith p)
  match kw? with
  | none => none
  | some kw =>
      let rest := t.drop kw.length |>.toString
      let name := String.ofList (rest.toList.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\''))
      if name.isEmpty then none else some name

/-- Check root namespace discipline using the same line-oriented rules as the original gate. -/
def checkRootNamespace (code : String) (rel : String) : Array String := Id.run do
  let lines := code.splitOn "\n" |>.toArray
  let mut nsStack : Array String := #[]
  let mut secStack : Array String := #[]
  let mut errors : Array String := #[]
  for i in [0:lines.size] do
    let raw := lines[i]!
    let line := raw.trimAscii.toString
    if line.isEmpty then continue
    if line.startsWith "namespace " then
      nsStack := nsStack.push (String.ofList ((line.drop 10 |>.toString).toList.takeWhile (fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'')))
      continue
    let isSection := line == "section" || line.startsWith "section " ||
      line == "noncomputable section" || line.startsWith "noncomputable section " ||
      line == "public section" || line.startsWith "public section "
    if isSection then
      let sectionPrefix := if line.startsWith "noncomputable " then 21 else if line.startsWith "public " then 14 else 7
      let rest := line.drop sectionPrefix |>.toString.trimAscii.toString
      secStack := secStack.push rest
      continue
    if line == "end" || line.startsWith "end " then
      let target := if line == "end" then "" else line.drop 4 |>.toString.trimAscii.toString
      if target.isEmpty then
        if !secStack.isEmpty then secStack := secStack.pop
        else if !nsStack.isEmpty then nsStack := nsStack.pop
      else if !secStack.isEmpty && secStack.back! == target then
        secStack := secStack.pop
      else if !nsStack.isEmpty then
        nsStack := nsStack.pop
      continue
    match parseDeclName raw with
    | some name =>
        if nsStack.isEmpty && !name.startsWith "Qatlib." then
          errors := errors.push s!"{rel}:{i + 1}: root-namespace declaration `{name}` outside `namespace Qatlib.*`"
    | none => pure ()
  errors

/-- Count identifier tokens for unreferenced Prop declaration checks. -/
def identifierCounts (code : String) (counts : Std.HashMap String Nat) : Std.HashMap String Nat :=
  let isWord (c : Char) := c.isAlphanum || c == '_' || c == '\''
  let rec flush (buf : Array Char) (out : Std.HashMap String Nat) : Std.HashMap String Nat :=
    if buf.isEmpty then out
    else
      let key := String.ofList buf.toList
      out.insert key ((out[key]?.getD 0) + 1)
  let rec loop (xs : List Char) (buf : Array Char) (out : Std.HashMap String Nat) : Std.HashMap String Nat :=
    match xs with
    | [] => flush buf out
    | c :: rest => if isWord c then loop rest (buf.push c) out else loop rest #[] (flush buf out)
  loop code.toList #[] counts

/-- Count only selected identifiers, avoiding a large global token table. -/
def countCandidateNames (code : String) (candidates : Std.HashSet String)
    (counts : Std.HashMap String Nat) : Std.HashMap String Nat :=
  let isWord (c : Char) := c.isAlphanum || c == '_' || c == '\''
  let flush (buf : Array Char) (out : Std.HashMap String Nat) : Std.HashMap String Nat :=
    if buf.isEmpty then out
    else
      let key := String.ofList buf.toList
      if candidates.contains key then out.insert key ((out[key]?.getD 0) + 1) else out
  let rec loop (xs : List Char) (buf : Array Char) (out : Std.HashMap String Nat) : Std.HashMap String Nat :=
    match xs with
    | [] => flush buf out
    | c :: rest => if isWord c then loop rest (buf.push c) out else loop rest #[] (flush buf out)
  loop code.toList #[] counts

/-- Check statement-fidelity and source-hygiene rules for one Lean file. -/
def checkFidelityFile (rel _raw code : String) (lines : Array String) (freq : Std.HashMap String Nat)
    (props : Array PropDefInfo) (costNotices : Nat) :
    Array String × Array PropDefInfo × Nat × Std.HashMap String Nat := Id.run do
  let mut errors : Array String := #[]
  let mut props := props
  let mut costNotices := costNotices
  let codeLines := code.splitOn "\n" |>.toArray
  if rel.startsWith "Qatlib/" then errors := errors ++ checkRootNamespace code rel
  let leaks : Array (String × String) := #[
    ("workflow-leak(Lean gap)", "lean gap"),
    ("workflow-leak(Suggested next/route)", "suggested next"),
    ("workflow-leak(Suggested next/route)", "suggested continuation"),
    ("workflow-leak(Suggested next/route)", "suggested takeover"),
    ("workflow-leak(Suggested next/route)", "suggested route"),
    ("workflow-leak(Candidate reuse)", "candidate reuse:"),
    ("workflow-leak(prefetched PDF)", "prefetched pdf"),
    ("workflow-leak(Gap record)", "gap record"),
    ("workflow-leak(Frozen v2.x)", "frozen v2."),
    ("workflow-leak(prove/assets)", "prove/assets/"),
    ("workflow-leak(peer-review record)", "peer-review record"),
    ("workflow-leak(documented sorry)", "documented sorry"),
    ("legacy-namespace(QuantumAlgorithm.)", "quantumalgorithm."),
    ("boilerplate(No axiom...)", "no axiom, no admit, no native_decide")
  ]
  for i in [0:lines.size] do
    let rawLine := lines[i]!
    let line := asciiLower rawLine
    let lineNo := i + 1
    let declarationLine :=
      ["def ", "abbrev ", "theorem ", "lemma ", "structure ", "class ", "inductive ", "instance ",
       "noncomputable def ", "public def ", "private def ", "protected def "]
        |>.any (fun p => line.trimAsciiStart.toString.startsWith p)
    for (label, needle) in leaks do
      -- Type names such as `TriangleCheckQuantumAlgorithm` contain the
      -- historical identifier without using the legacy namespace.
      let allowedTypeName := needle == "quantumalgorithm." && declarationLine
      if line.contains needle && !allowedTypeName then
        errors := errors.push s!"{rel}:{lineNo}: {label}: '{needle}'"
    let codeLine := if i < codeLines.size then codeLines[i]! else ""
    if codeLine.contains "debug.skipKernelTC" then errors := errors.push s!"{rel}:{lineNo}: forbidden skipKernelTC"
    if codeLine.contains "native_decide" then errors := errors.push s!"{rel}:{lineNo}: forbidden native_decide"
    if codeLine.contains "set_option warningAsError false" then errors := errors.push s!"{rel}:{lineNo}: forbidden warningAsError-false"
    if codeLine.contains "set_option linter." && codeLine.contains " false" then errors := errors.push s!"{rel}:{lineNo}: forbidden linter-false"
    let words := codeLine.splitOn " " |>.flatMap (fun x => x.splitOn "\t")
    if words.any (fun w => w == "sorry") then errors := errors.push s!"{rel}:{lineNo}: forbidden sorry"
    if words.any (fun w => w == "admit") then errors := errors.push s!"{rel}:{lineNo}: forbidden admit"
    let trimmed := codeLine.trimAscii.toString
    let trimmed := ["public ", "private ", "protected ", "noncomputable "].foldl
      (fun t p => if t.startsWith p then t.drop p.length |>.toString else t) trimmed
    if trimmed.startsWith "axiom " || trimmed == "axiom" then errors := errors.push s!"{rel}:{lineNo}: forbidden custom-axiom"
    if trimmed.startsWith "unsafe " || trimmed == "unsafe" then errors := errors.push s!"{rel}:{lineNo}: forbidden unsafe-decl"
    if rel.startsWith "Qatlib/Papers/" then
      match parsePropDefLine codeLine with
      | some name =>
          let mut banner := false
          let bannerStart := if i > 12 then i - 12 else 0
          for j in [bannerStart:i] do
            let prior := asciiLower (lines[j]!)
            if prior.contains "statement only" || prior.contains "statement-only" then banner := true
          props := props.push { file := rel, line := lineNo, name := name, hasBanner := banner }
      | none => pure ()
      let t := codeLine.trimAscii.toString
      if ["queries : ℕ", "queries : Nat", "queries : ℝ", "queries : Real", "cost : ℕ", "cost : Nat", "cost : ℝ", "cost : Real", "time : ℕ", "time : Nat", "time : ℝ", "time : Real", "runtime : ℕ", "runtime : Nat", "runtime : ℝ", "runtime : Real", "depth : ℕ", "depth : Nat", "depth : ℝ", "depth : Real"].contains t then
        costNotices := costNotices + 1
  (errors, props, costNotices, freq)

structure FileCheckResult where
  errors : Array String
  fidelityErrors : Array String
  propDefs : Array PropDefInfo
  costNotices : Nat
  citationCount : Nat
  citationErrors : Array String
  code : String

/-- Perform all checks that depend only on one source file.  Keeping this unit
parallel-friendly lets the driver overlap filesystem reads and parsing across
the large paper corpus. -/
def checkOneFile (path : FilePath) (moduleSet bibKeys : Std.HashSet String) : IO FileCheckResult := do
  let relStr := path.toString
  let raw ← IO.FS.readFile path
  let bodyLines := raw.splitOn "\n" |>.toArray
  let mut errors : Array String := #[]
  let mut fidelityErrors : Array String := #[]
  let mut propDefs : Array PropDefInfo := #[]
  let mut costNotices : Nat := 0
  let mut citationCount : Nat := 0
  let mut citationErrors : Array String := #[]
  let mut code : String := ""
  if relStr.startsWith "Qatlib/" then
    let parts := (path.withExtension "").components
    match parts with
    | "Qatlib" :: top :: _ =>
        if !(#["Foundations", "Concepts", "Papers"].contains top) then
          errors := errors.push s!"{relStr}:1: ERR_DIR: Top-level Qatlib directory '{top}' must be one of Foundations, Concepts, or Papers"
    | _ => errors := errors.push s!"{relStr}:1: ERR_DIR: Invalid Qatlib module path"
    for part in parts do
      if !isUpperCamelCase part then
        errors := errors.push s!"{relStr}:1: ERR_CAM: '{part}' is not strict UpperCamelCase"
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
       hasSubstr line "set_option profiler." || hasSubstr line "set_option trace.") then
      let stripped := line.trimAsciiStart.toString
      if !stripped.startsWith "--" &&
         (stripped.startsWith "set_option pp." || stripped.startsWith "set_option profiler." ||
          stripped.startsWith "set_option trace.") then
        errors := errors.push s!"{relStr}:{lineNo}: ERR_OPT: Forbidden debug set_option"
    if line.contains ';' && hasSubstr line " ;" then
      let stripped := line.trimAsciiStart.toString
      if !stripped.startsWith "--" then
        errors := errors.push s!"{relStr}:{lineNo}: ERR_SEM: Space before semicolon"
  if relStr.startsWith "Qatlib/" then
    code := stripComments raw
    let (fErrs, newProps, newCosts, _) :=
      checkFidelityFile relStr raw code bodyLines {} #[] 0
    fidelityErrors := fidelityErrors ++ fErrs
    propDefs := newProps
    costNotices := newCosts
    let docs := scanDocComments raw
    for doc in docs do
      let (count, errs) := checkDocCitations doc bibKeys
      citationCount := citationCount + count
      for err in errs do citationErrors := citationErrors.push s!"{relStr}:{err}"
  return {
    errors := errors
    fidelityErrors := fidelityErrors
    propDefs := propDefs
    costNotices := costNotices
    citationCount := citationCount
    citationErrors := citationErrors
    code := code
  }

def checkFileChunk (paths : Array FilePath) (moduleSet bibKeys : Std.HashSet String) : IO (Array FileCheckResult) := do
  let mut results : Array FileCheckResult := #[]
  for path in paths do
    results := results.push (← checkOneFile path moduleSet bibKeys)
  return results

def countCandidateCodeChunk (codes : Array String) (candidates : Std.HashSet String) :
    IO (Std.HashMap String Nat) := do
  let mut counts : Std.HashMap String Nat := {}
  for code in codes do
    counts := countCandidateNames code candidates counts
  return counts

/-- Run static style, import, statement-fidelity, and bibliography checks in one pass. -/
def runStaticChecks : IO UInt32 := do
  IO.println "=== Running Static Source, Style, Import, Fidelity & Reference Linter ==="
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
  expectedRootImports := expectedRootImports.qsort (· < ·)
  if rootImports != expectedRootImports then
    errors := errors.push "Qatlib.lean:1: ERR_ROOT: Qatlib.lean imports do not match sorted Qatlib/ module list"

  let mut fidelityErrors : Array String := #[]
  let mut propDefs : Array PropDefInfo := #[]
  let mut costNotices : Nat := 0
  let mut citationCount : Nat := 0
  let mut citationErrors : Array String := #[]
  let mut sourceCodes : Array String := #[]
  let mut bibKeys : Std.HashSet String := {}
  let mut bibCounts : Std.HashMap String Nat := {}
  try
    let bibLines ← IO.FS.lines "docs/references.bib"
    for line in bibLines do
      match parseBibKey line with
      | some key =>
          bibKeys := bibKeys.insert key
          bibCounts := bibCounts.insert key ((bibCounts[key]?.getD 0) + 1)
      | none => pure ()
    if bibKeys.isEmpty then errors := errors.push "docs/references.bib: no bibliography entries found"
  catch _ =>
    errors := errors.push "docs/references.bib: unable to read bibliography"

  -- Per-file checks are independent once the module and bibliography indexes
  -- are known. Use contiguous chunks so result ordering remains stable while
  -- up to sixteen workers overlap filesystem reads and parsing.
  let workerCount := Nat.min 96 allFiles.size
  let chunkSize := if workerCount == 0 then 1 else (allFiles.size + workerCount - 1) / workerCount
  let mut tasks : Array (Task (Except IO.Error (Array FileCheckResult))) := #[]
  for worker in [0:workerCount] do
    let start := worker * chunkSize
    let stop := Nat.min allFiles.size (start + chunkSize)
    if start < stop then
      tasks := tasks.push (← IO.asTask (checkFileChunk (allFiles.extract start stop) moduleSet bibKeys))
  for task in tasks do
    let results : Array FileCheckResult ← IO.ofExcept (← IO.wait task)
    for result in results do
      errors := errors ++ result.errors
      fidelityErrors := fidelityErrors ++ result.fidelityErrors
      propDefs := propDefs ++ result.propDefs
      costNotices := costNotices + result.costNotices
      citationCount := citationCount + result.citationCount
      citationErrors := citationErrors ++ result.citationErrors
      if !result.code.isEmpty then sourceCodes := sourceCodes.push result.code

  let noticePath : FilePath := "NOTICE"
  if !(← noticePath.pathExists) then
    fidelityErrors := fidelityErrors.push "NOTICE: missing root NOTICE file for third-party Apache-2.0 attributions"
  else
    let notice ← IO.FS.readFile noticePath
    for vendor in #["TauCeti", "Causal"] do
      if !notice.contains vendor then
        fidelityErrors := fidelityErrors.push s!"NOTICE: missing attribution entry matching `{vendor}`"

  for (key, count) in bibCounts.toList do
    if count > 1 then citationErrors := citationErrors.push s!"docs/references.bib: duplicate key `{key}`"
  if qatlibFiles.isEmpty then citationErrors := citationErrors.push "Qatlib/: no Lean source files found"

  let isTheoremLike (name : String) : Bool :=
    let n := name.toLower
    ["theorem", "thm", "lemma", "lem", "corollary", "cor", "proposition", "prop"].any (n.startsWith ·)
  let suffixOK (name : String) : Bool := name.endsWith "_statement" || name.endsWith "Statement" || name.endsWith "Spec"
  let mut candidates : Std.HashSet String := {}
  for prop in propDefs do
    if isTheoremLike prop.name && !suffixOK prop.name then
      candidates := candidates.insert prop.name
  let mut candidateCounts : Std.HashMap String Nat := {}
  if !candidates.isEmpty then
    let workerCount := Nat.min 96 sourceCodes.size
    let chunkSize := if workerCount == 0 then 1 else (sourceCodes.size + workerCount - 1) / workerCount
    let mut countTasks : Array (Task (Except IO.Error (Std.HashMap String Nat))) := #[]
    for worker in [0:workerCount] do
      let start := worker * chunkSize
      let stop := Nat.min sourceCodes.size (start + chunkSize)
      if start < stop then
        countTasks := countTasks.push
          (← IO.asTask (countCandidateCodeChunk (sourceCodes.extract start stop) candidates))
    for task in countTasks do
      let part : Std.HashMap String Nat ← IO.ofExcept (← IO.wait task)
      for (name, count) in part.toList do
        candidateCounts := candidateCounts.insert name
          (candidateCounts[name]?.getD 0 + count)
  for prop in propDefs do
    let occurrences := candidateCounts[prop.name]?.getD 0
    if isTheoremLike prop.name && !suffixOK prop.name && occurrences <= 1 then
      fidelityErrors := fidelityErrors.push
        s!"{prop.file}:{prop.line}: unproved theorem-like Prop definition `{prop.name}` must either be proved by a theorem or carry `_statement`/`Statement`/`Spec` suffix"
    if isTheoremLike prop.name && !suffixOK prop.name && occurrences <= 1 && !prop.hasBanner then
      fidelityErrors := fidelityErrors.push
        s!"{prop.file}:{prop.line}: statement-only Prop definition `{prop.name}` requires a statement-only doc banner"

  errors := errors ++ fidelityErrors ++ citationErrors
  if !errors.isEmpty then
    for err in errors do IO.eprintln err
    IO.eprintln s!"LINT_FAILED errors={errors.size}"
    return 1

  IO.println s!"LINT_STYLE_OK files={allFiles.size} errors=0"
  IO.println s!"CHECK_IMPORTS_OK modules={qatlibFiles.size} errors=0"
  IO.println s!"CHECK_FIDELITY_OK files={qatlibFiles.size} errors=0 (paper_prop_defs={propDefs.size}, cost_field_notices={costNotices})"
  IO.println s!"CHECK_REFERENCES_OK files={qatlibFiles.size} citations={citationCount} errors=0"
  return 0

def main (_args : List String) : IO UInt32 :=
  runStaticChecks
