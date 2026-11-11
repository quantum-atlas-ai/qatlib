# Getting Started & Cache Guide

> 🌐 [中文版](./getting-started.md)

This guide covers toolchain installation, using `Qatlib` as a downstream dependency, fetching the three-tier prebuilt cache for local development, and troubleshooting common build or editor issues.

## 1. Prerequisites

1. **Install `elan` (Lean 4 version manager)**:
   Follow the [official Lean 4 quickstart](https://lean-lang.org/lean4/doc/quickstart.html) to install `elan`. When you enter the repository directory, `elan` automatically downloads and activates the pinned toolchain specified in [`lean-toolchain`](../lean-toolchain) (`leanprover/lean4:v4.35.0`).
2. **Recommended hardware**:
   - With prebuilt caches (`lake exe get_cache`): at least **15 GB** of free disk space and **8 GB+** RAM.
   - Building the entire library from scratch without cache: **16 GB+** RAM and a multi-core CPU.

## 2. Using `Qatlib` as a Downstream Dependency

In your Lean 4 project's `lakefile.toml` (using the matching [`lean-toolchain`](../lean-toolchain) `leanprover/lean4:v4.35.0`), add:

```toml
[[require]]
name = "Qatlib"
git = "https://github.com/quantum-atlas-ai/qatlib.git"
rev = "main" # Track the latest theorems (recommended); or pin to "v4.35.0" for the initial toolchain baseline
```

From your project root, lock the current commit in `lake-manifest.json` and fetch all three layers of prebuilt caches (`Mathlib`, `Physlib`, and `Qatlib`) so you do not have to compile `Qatlib` from source:

```bash
lake update
lake exe get_cache
```

> **How version locking and cache updates work**:
> - Setting `rev = "main"` fetches the latest theorems on `main` when you run `lake update` and records the exact commit SHA in `lake-manifest.json`; if you prefer to freeze at the initial toolchain release snapshot, set `rev = "v4.35.0"`.
> - `lake update` only updates source checkouts and `lake-manifest.json`—it **does not automatically fetch prebuilt caches**. Whenever you run `lake update` (or `lake update Qatlib`), follow it with `lake exe get_cache`.

Then import `Qatlib` or the specific modules you need in your `.lean` files (prefer importing specific submodules in large projects to keep your import closure minimal):

```lean
import Qatlib.Foundations.ChannelTheory.ChoiKraus
import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow
import Qatlib.Papers.GroverSearch96.MainResults.GainConvergence
```

## 3. Local Development, Three-Tier Cache & Incremental Builds

### 3.1 Cloning and Fetching the Cache

```bash
git clone https://github.com/quantum-atlas-ai/qatlib.git
cd qatlib

# Fetch all three tiers of prebuilt caches
lake exe get_cache
```

`lake exe get_cache` (implemented in [`scripts/get_cache.lean`](../scripts/get_cache.lean)) runs three steps in sequence:
1. **`[1/3] Mathlib cache`**: Runs `lake exe cache get` to download prebuilt `.olean` artifacts for `Mathlib` and its upstream dependencies (`Batteries`, `Aesop`, `Qq`, etc.).
2. **`[2/3] Physlib cache`**: Reads `.lake/packages/Physlib/lake-cache.toml` and runs `lake cache get Physlib` to fetch upstream `Physlib` / `QuantumInfo` artifacts.
3. **`[3/3] Qatlib cache`**: Reads [`lake-cache.toml`](../lake-cache.toml) (public read endpoint `https://lake-cache.quantum-atlas.ai`) and runs `lake cache get Qatlib` to restore prebuilt `Qatlib` artifacts into the local Lake cache and `.lake/build/`.

### 3.2 Targeted Builds & Unified Linter

Once the cache is populated, `lake build` only recompiles modified files and their downstream dependents:

```bash
# Build a specific module (recommended for day-to-day development)
lake build Qatlib.Foundations.ChannelTheory.ChoiKraus
lake build Qatlib.Papers.GroverSearch96.MainResults.GainConvergence

# Build the entire library
lake build Qatlib

# Run fast static style and module import checks (~1 second)
lake lint

# Run kernel-level zero-sorryAx and standard-axiom verification on compiled .olean files
lake test
```

## 4. VS Code Setup & Troubleshooting

1. **Open the repository root folder**:
   After installing the official [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4), always open the top-level `qatlib` directory via **File → Open Folder** (do not open a subdirectory such as `Qatlib/Papers` directly, or Lake will not find `lakefile.toml` and `lean-toolchain`).
2. **Go-to-Definition and hover support**:
   After running `lake exe get_cache`, `lean --server` reuses the prebuilt `.olean` and `.ilean` artifacts from the local Lake cache directly without recompiling imported modules in the background.
3. **Troubleshooting**:
   - If you encounter stale or mismatched `.olean` errors after switching branches, re-run `lake exe get_cache`.
   - To reset local build outputs completely, run `lake clean` followed by `lake exe get_cache && lake build`.
