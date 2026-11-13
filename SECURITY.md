# Security Policy

## Scope

Qatlib is a Lean 4 mathematical library distributed with Lake build scripts,
static/kernel verification drivers (`scripts/`), and precompiled `.olean` cache
fetching utilities (`lake exe get_cache`).

Security-relevant issues include:

1. **Kernel soundness or axiom-audit bypasses**: any declaration in `Qatlib`
   relying on `sorryAx`, `Lean.ofReduceBool` (`native_decide`), custom axioms
   outside `{propext, Classical.choice, Quot.sound}`, `debug.skipKernelTC`, or
   metaprogramming environment manipulation that evades `lake test`.
2. **Build / cache supply-chain issues**: vulnerabilities in `scripts/get_cache.lean`,
   CI workflows, or artifact verification.
3. **Credential or secret exposure** in repository files or workflows.

*(Note: mathematical misformalisations — such as missing hypotheses or overly
permissive model definitions that remain sound in Lean's kernel — should be
reported via the **Statement Fidelity Report** issue template so the community
can track and audit them openly.)*

## Reporting a Vulnerability

Please report security or soundness-bypass vulnerabilities privately via
[**GitHub Private Vulnerability Reporting**](https://github.com/quantum-atlas-ai/qatlib/security/advisories/new)
rather than opening a public issue.

Include:
* Affected commit SHA, file path(s), and Lean toolchain version;
* Minimal reproduction steps (e.g., `#print axioms` or `lake test` output);
* Impact assessment (soundness bypass vs. build/cache execution).

We aim to acknowledge reports within 72 hours and publish a fix and advisory
once verified.
