/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

open IO Process

def runCmd (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) : IO UInt32 := do
  let child ← spawn {
    cmd := cmd
    args := args
    env := env
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  child.wait

def configValue (cfg : String) (key : String) : Option String := do
  let line ← (cfg.splitOn "\n").find? fun line =>
    line.trimAscii.toString.startsWith (key ++ " = \"")
  let value := line.trimAscii.toString.drop (key.length + 4) |>.toString
  if value.endsWith "\"" then some (value.dropEnd 1).toString else none

def gitRaw (repo : System.FilePath) (args : Array String) : IO (Option String) := do
  let result ← IO.Process.output { cmd := "git", args := #["-C", repo.toString] ++ args }
  return if result.exitCode == 0 then some result.stdout else none

def gitOutput (repo : System.FilePath) (args : Array String) : IO String := do
  return (← gitRaw repo args).getD "" |>.trimAscii.toString

def sha256Hex (input : String) : IO String := do
  for (cmd, args) in #[ ("sha256sum", #[]), ("shasum", #["-a", "256"]) ] do
    try
      let res ← IO.Process.output { cmd := cmd, args := args } (some input)
      if res.exitCode == 0 then
        let hex := (res.stdout.trimAscii.toString.splitOn " ").headD ""
        if hex.length == 64 then return hex
    catch _ => pure ()
  return ""

def inputTree (repo : System.FilePath) (paths : Array String) : IO String := do
  -- git rev-parse emits one trailing newline; hash those exact bytes, matching Python.
  let raw? ← gitRaw repo (#["rev-parse"] ++ paths.map ("HEAD:" ++ ·))
  match raw? with
  | some raw => sha256Hex raw
  | none => pure ""

def writeCurlRc (tmpDir : System.FilePath) (auth? : Option String) : IO Unit := do
  let auth := auth?.map (fun key => s!"aws-sigv4 = \"aws:amz:auto:s3\"\nuser = \"{key}\"\n") |>.getD ""
  IO.FS.writeFile (tmpDir / ".curlrc") (auth ++
    "connect-timeout = 15\nmax-time = 120\nspeed-time = 20\nspeed-limit = 1024\nretry = 2\nretry-delay = 1\n")

def manifestHasEntries (path : System.FilePath) : IO Bool := do
  let contents ← IO.FS.readFile path
  let nonEmpty := contents.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  return nonEmpty.length >= 2

def runLakeManifestGet (pkg repoSlug : String)
    (cfgPath manifest : System.FilePath) (auth? : Option String) : IO UInt32 := do
  let args := #["cache", "get", manifest.toString, s!"--package={pkg}", s!"--repo={repoSlug}"]
  IO.FS.withTempDir fun tmpDir => do
    writeCurlRc tmpDir auth?
    runCmd "lake" args #[ ("LAKE_CONFIG", some cfgPath.toString), ("CURL_HOME", some tmpDir.toString) ]

def fetchRepoCache (pkg repoSlug tcDir : String) (repo cfgPath : System.FilePath)
    (inputPaths : Array String) (keyEnv : String := "LAKE_CACHE_KEY") : IO UInt32 := do
  unless ← cfgPath.pathExists do
    IO.println s!"Note: {pkg} cache configuration unavailable; compile locally."
    return 1
  let cfg ← IO.FS.readFile cfgPath
  let auth? := (← IO.getEnv keyEnv).filter (!·.trimAscii.isEmpty) <|> configValue cfg "s3Auth"
  let endpoint := (configValue cfg "revisionEndpoint").getD "https://lake-cache.quantum-atlas.ai/revisions"
  let rev ← gitOutput repo #["rev-parse", "HEAD"]
  let ancestors ← gitOutput repo #["rev-list", "--max-count=25", "HEAD~1"]
  let keys ← do
    let mut out := if rev.isEmpty then #[] else #[rev]
    let tree ← inputTree repo inputPaths
    unless tree.isEmpty do out := out.push s!"inputs/{tree}"
    for anc in ancestors.splitOn "\n" do
      let a := anc.trimAscii.toString
      unless a.isEmpty do out := out.push a
    pure out
  IO.FS.withTempDir fun tmpDir => do
    writeCurlRc tmpDir auth?
    let env := #[ ("LAKE_CONFIG", some cfgPath.toString), ("CURL_HOME", some tmpDir.toString) ]
    let manifest := tmpDir / "outputs.jsonl"
    let canonicalBase := s!"{endpoint}/{repoSlug}/tc/{tcDir}"
    let tryBase (base : String) : IO Bool := do
      for key in keys do
        -- A failed curl may leave an existing output file untouched. Remove it
        -- first so a previous key cannot be mistaken for this response.
        if ← manifest.pathExists then
          try IO.FS.removeFile manifest catch _ => pure ()
        let result ← output { cmd := "curl", args := #["--fail", "--silent", "--location", "--output", manifest.toString,
          s!"{base}/{key}.jsonl"], env := env }
        if result.exitCode == 0 then
          try
            let metadata ← manifest.metadata
            if metadata.byteSize > 0 && (← manifestHasEntries manifest) then
              if (← runLakeManifestGet pkg repoSlug cfgPath manifest auth?) == 0 then return true
          catch _ => pure ()
      return false
    if ← tryBase canonicalBase then return 0
    IO.println s!"Note: No usable {pkg} cache found; lake build will compile locally."
    return 1

def runLakeScopeGet (pkg scope : String) (cfgPath : System.FilePath) : IO UInt32 :=
  IO.FS.withTempDir fun tmpDir => do
    writeCurlRc tmpDir none
    runCmd "lake" #["cache", "get", s!"--package={pkg}", s!"--scope={scope}"]
      #[ ("LAKE_CONFIG", some cfgPath.toString), ("CURL_HOME", some tmpDir.toString) ]

def main (args : List String) : IO UInt32 := do
  let skipMathlib := args.contains "--no-mathlib"
  let skipPhyslib := args.contains "--no-physlib"
  let skipQatlib := args.contains "--no-qatlib"
  unless skipMathlib do
    println! "=== [1/3] Fetching upstream Mathlib cache ==="
    if (← runCmd "lake" #["exe", "cache", "get"]) != 0 then
      IO.eprintln "Warning: Mathlib cache unavailable; compile locally."
  let tcRaw ← IO.FS.readFile "lean-toolchain"
  let tcRaw := tcRaw.trimAscii.toString
  let tcDir := (tcRaw.replace "/" "--").replace ":" "---"
  let tcLegacy := (tcRaw.replace "/" "-").replace ":" "-"
  let cwd ← IO.currentDir
  unless skipPhyslib do
    println! "=== [2/3] Fetching upstream Physlib build cache ==="
    let cfg := cwd / ".lake" / "packages" / "Physlib" / "lake-cache.toml"
    if ← cfg.pathExists then
      let rc ← runLakeScopeGet "Physlib" (s!"physlib-master/{tcLegacy}/physlib") cfg
      if rc != 0 then IO.eprintln "Warning: Physlib cache unavailable; compile locally."
  unless skipQatlib do
    println! "=== [3/3] Fetching Qatlib build cache ==="
    let dir ← if (← (cwd / "Qatlib.lean").pathExists) then pure cwd else pure (cwd / ".lake" / "packages" / "Qatlib")
    let cfg := dir / "lake-cache.toml"
    if ← cfg.pathExists then
      let rc ← fetchRepoCache "Qatlib" "quantum-atlas-ai/qatlib" tcDir dir cfg
        #["Qatlib", "Qatlib.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"]
      if rc != 0 then IO.println "Note: No prebuilt Qatlib cache found; lake build will compile locally."
  return 0
