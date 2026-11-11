/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs

/-!
# Collapse of quadratic signs on the kernel

This module removes the quadratic signs from the Eulerian sum when `parityCondition` holds. The
pointwise and summed identities isolate the parity hypothesis used in the partition
correspondence of Theorem 1 in [Geraci2008].

## Main statements

* `parity_collapse`: identifies the signed and unsigned Eulerian sums under the parity
  condition.
* `parity_summand_eq`: removes the sign from a summand whose quadratic form vanishes.

## References

* [Geraci, 2008][Geraci2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

/-- If the quadratic form vanishes on the kernel, the signed Eulerian sum equals the unsigned
Eulerian sum. See [Geraci2008]. -/
theorem parity_collapse {R N : ℕ} {B : Matrix (Fin N) (Fin N) (ZMod 2)}
    {CH : Matrix (Fin R) (Fin N) (ZMod 2)} {lam : ℝ}
    (h : parityCondition B CH) :
    signedEulerianSum B CH lam = eulerianSum CH lam := by
  unfold signedEulerianSum eulerianSum
  apply Finset.sum_congr rfl
  intro a ha
  have hzero : quadForm B a = 0 := h a ha
  simp [paritySign, hzero]

/-- A kernel-vector summand whose quadratic form is zero equals its unsigned weight `lam ^ wt
a`. -/
theorem parity_summand_eq {R N : ℕ} {B : Matrix (Fin N) (Fin N) (ZMod 2)}
    {CH : Matrix (Fin R) (Fin N) (ZMod 2)} {lam : ℝ} {a : F2Vec N}
    (_ha : a ∈ kerSet CH) (hzero : quadForm B a = 0) :
    paritySign (quadForm B a) * lam ^ wt a = lam ^ wt a := by
  simp [paritySign, hzero]

end Qatlib.Papers.IsingPartit08.MainResults
