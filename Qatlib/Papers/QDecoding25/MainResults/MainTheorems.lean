/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-!
# Main theorem statements of *The Quantum Decoding Problem* (arXiv:2509.24796v2)

Earlier revisions of this branch recorded the paper's main theorem statements
as statement-only declarations ending in `sorry` (Theorems 1, 2, 3, 4, 5, 6,
9, 10 and Propositions 7, 8). Repository policy forbids `sorry`, and the
statements depended on unproved analytic and probabilistic core lemmas, so the
unproved declarations were removed from the build.

The independently proved lower-level results remain in `TypicalEntropy.lean`
(Lemma 1) and `PgmCore.lean` (Proposition 5). See this paper's PR body for the
full list of unformalized claims and the infrastructure each one requires.
-/
