/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteCounts.SubsetMoments.SubsetSumMaskBridge
public import Qatlib.Foundations.FiniteCounts.SubsetMoments.TargetCauchyInterpolation

@[expose] public section


/-! # Exact subset-sum coefficient interfaces

Theorem 1.3 of *Quantum Computation and Lattice Problems*, fixed
arXiv:cs/0304005v1, reduces the
dihedral coset problem to legal modular subset-sum instances. The following
algebraic support identifies an actual solution set with the nonzero
coefficients of its unit-weight generating table. The fixed-cardinality
interface supplies the individual layers of the full subset table.
No efficient solver or dihedral reduction is inferred from this identity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

open Qatlib.Foundations.FiniteCounts.SubsetMoments

/-- The nonzero unit-weight coefficient support equals the actual attained subset-sum residues. -/
theorem subsetCoefficient_support {m N : ℕ} (labels : Fin m → ZMod N) (k : ℕ) :
    sourceResidueNonzeroSet labels k = subsetSumResidues labels k :=
  sourceResidueNonzeroSet_eq_residues labels k

/-- A nonzero unit-weight coefficient is equivalent to a legal fixed-cardinality subset-sum witness. -/
theorem subsetCoefficient_nonzero_iff {m N : ℕ} (labels : Fin m → ZMod N)
    (k : ℕ) (target : ZMod N) :
    sourceResidueCoefficient labels (fun _ => 1) k target ≠ 0 ↔
      subsetSumSupportExists labels k target :=
  sourceResidueCoefficient_one_ne_zero_iff labels k target

end Qatlib.Papers.QLattice03.MainResults
