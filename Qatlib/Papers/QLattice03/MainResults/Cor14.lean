/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma45
import Qatlib.Papers.QLattice03.MainResults.Lemma49
import Qatlib.Papers.QLattice03.MainResults.Reductions

/-!
# QLattice03 — Corollary 1.4: average-case subset sum implies the dihedral HSP

Paper: Oded Regev, *Quantum Computation and Lattice Problems*,
arXiv:cs/0304005v1, Section 1, Corollary 1.4 (page 2).

> Corollary 1.4  If there exists an algorithm `S` that solves a
> `1/poly(log N)` fraction of the legal subset sum inputs with parameter `N`
> then there exists a solution to the dihedral HSP.

The paper derives it from Theorem 1.3: the dihedral HSP reduces (d'Aris-Bacon
[6]) to the case of subgroups `{(0,0), (1,d)}`, where sampling cosets yields
DCP states `|0,x⟩ + |1,(x+d) mod N⟩` with no error; feeding those to the DCP
solution of Theorem 1.3 solves the dihedral HSP.

## Status

Recorded as an *open obligation* (`def … : Prop`), not asserted as a theorem.
The statement is the paper's: a routine solving a positive fraction of the
legal subset sum inputs yields *some* dihedral-HSP solver.  What is missing is
the reduction of [6] and the coset-sampling procedure that produces exact DCP
registers from an oracle hiding a slope.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

open Qatlib.Papers.QLattice03.MainResults

/-- **Corollary 1.4** (open obligation, existence form): a routine that solves
a positive fraction of the legal subset sum inputs yields a dihedral-HSP
solver. -/
def subsetSum_implies_dihedralHSP : Prop :=
  ∀ (S : SubsetSumRoutine), SolvesSubsetSum S → ∃ A, SolvesDihedralHSP A

end Qatlib.Papers.QLattice03.MainResults
