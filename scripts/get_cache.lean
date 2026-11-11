/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Lean

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

def runLakeCacheGet (pkg scope : String) (cfgPath : System.FilePath) : IO UInt32 :=
  IO.FS.withTempDir fun tmpDir => do
    let curlRcFile := tmpDir / ".curlrc"
    IO.FS.writeFile curlRcFile "connect-timeout = 15\nspeed-time = 20\nspeed-limit = 1024\nretry = 3\nretry-delay = 1\n"
    runCmd "lake" #["cache", "get", s!"--package={pkg}", s!"--scope={scope}"] #[
      ("LAKE_CONFIG", some cfgPath.toString),
      ("CURL_HOME", some tmpDir.toString)
    ]

def main (args : List String) : IO UInt32 := do
  let skipMathlib := args.contains "--no-mathlib"
  let skipPhyslib := args.contains "--no-physlib"
  let skipQatlib := args.contains "--no-qatlib"

  unless skipMathlib do
    println! "=== [1/3] Fetching upstream Mathlib cache ==="
    let rc1 ← runCmd "lake" #["exe", "cache", "get"]
    if rc1 != 0 then
      IO.eprintln "Warning: `lake exe cache get` returned non-zero exit code."

  let tcRaw ← IO.FS.readFile "lean-toolchain"
  let tc := (tcRaw.trimAscii.toString.replace "/" "-").replace ":" "-"
  let cwd ← IO.currentDir

  unless skipPhyslib do
    println! "=== [2/3] Fetching upstream Physlib build cache ==="
    let physlibCfg := cwd / ".lake" / "packages" / "Physlib" / "lake-cache.toml"
    if ← physlibCfg.pathExists then
      let physlibScope := s!"physlib-master/{tc}/physlib"
      let rc2 ← runLakeCacheGet "Physlib" physlibScope physlibCfg
      if rc2 != 0 then
        IO.eprintln "Warning: `lake cache get --package=Physlib` returned non-zero exit code."

  unless skipQatlib do
    println! "=== [3/3] Fetching Qatlib build cache ==="
    let rootCfg := cwd / "lake-cache.toml"
    let depCfg := cwd / ".lake" / "packages" / "Qatlib" / "lake-cache.toml"
    let cfgPath? ←
      if ← rootCfg.pathExists then pure (some rootCfg)
      else if ← depCfg.pathExists then pure (some depCfg)
      else pure none
    if let some cfgPath := cfgPath? then
      let scope := s!"qatlib-main/{tc}/qatlib"
      let rc3 ← runLakeCacheGet "Qatlib" scope cfgPath
      if rc3 != 0 then
        println! "Note: No prebuilt Qatlib cache found for this revision; `lake build` will compile locally."
  return 0
