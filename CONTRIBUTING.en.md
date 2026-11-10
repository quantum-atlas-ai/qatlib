# Contributing to Qatlib

> 🌐 [中文版](./CONTRIBUTING.md)

Issues and pull requests are welcome. For large additions or changes to core definitions, please open an issue first to discuss the design.

## Setting Up Your Environment

1. Install [Lean 4 (`elan`)](https://lean-lang.org/lean4/doc/quickstart.html).
2. Clone the repository and fetch prebuilt caches:

```bash
git clone https://github.com/quantum-atlas-ai/qatlib.git
cd qatlib

# Fetch prebuilt upstream (Mathlib / Physlib) and Qatlib caches (recommended)
lake exe get_cache
```

3. Build the module you are working on:

```bash
lake build Qatlib.Foundations.ChannelTheory.ChoiKraus
```

## Coding & Formalization Conventions

- **Module placement (one-way dependency `Foundations → Concepts → Papers`)**:
  - General operator analysis, quantum channels, measurements, and execution semantics belong in `Qatlib/Foundations/` (must not import `Concepts` or `Papers`).
  - Reusable algorithmic primitives and lower-bound techniques (block-encoding, QSVT/QSP, amplitude amplification, quantum walks, adversary bounds) belong in `Qatlib/Concepts/` (must not import `Papers`).
  - Formalizations of specific research papers belong in `Qatlib/Papers/`.
- **Minimal imports**: Import only the specific modules needed by each file; do not `import Qatlib` inside library modules.
- **Documentation**: Include a module docstring (`/-! ... -/`) at the top of each `.lean` file and docstrings (`/-- ... -/`) on public definitions and main theorems.
- **Complete proofs**: Pull requests must compile cleanly with `autoImplicit = false` without `sorry`, `admit`, or custom `axiom` declarations (only Lean's standard axioms `propext`, `Quot.sound`, `Classical.choice` are permitted).
- **Third-party attribution**: If any code is adapted or ported from an external project or repository, please note the original source, author(s), and license in the file header and PR description.

## Pre-PR Checks

```bash
# 1. Build the modified module(s)
lake build <YourModule>

# 2. Run static style/import checks and kernel axiom verification
lake lint
lake test
```

## License

By contributing to `Qatlib`, you agree that your contributions will be licensed under the [Apache License 2.0](./LICENSE).
