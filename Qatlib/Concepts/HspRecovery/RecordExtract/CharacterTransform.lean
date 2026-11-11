/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Group-register transformations

This module defines three matrices for transformations of two finite group registers: the
relative-coordinate map, simultaneous left multiplication, and left multiplication of the second
factor. These are the group-register operations used in the representation-based sampling
discussion of [Kuperberg2005].

## Main statements

* `sourceDifferenceGate`: the relative-coordinate permutation matrix.
* `sourceDiagonalLeft`: simultaneous left multiplication on both registers.
* `sourceRightFactorLeft`: left multiplication on the second register.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib

/-- The permutation matrix associated with the relative-coordinate map `(x, y) ↦ (y⁻¹ * x, y)`
on two group registers. -/
noncomputable def sourceDifferenceGate (G : Type*) [Group G] [Fintype G] :
    Matrix (G × G) (G × G) ℂ := by
  classical
  exact permMatrix (fun p : G × G => (p.2⁻¹ * p.1, p.2))

/-- The permutation matrix associated with simultaneous left multiplication `(x, y) ↦ (g * x, g
* y)`. -/
noncomputable def sourceDiagonalLeft (G : Type*) [Group G] [Fintype G] (g : G) :
    Matrix (G × G) (G × G) ℂ := by
  classical
  exact permMatrix (fun p : G × G => (g * p.1, g * p.2))

/-- The permutation matrix associated with left multiplication on the second register, `(x, y) ↦
(x, g * y)`. -/
noncomputable def sourceRightFactorLeft (G : Type*) [Group G] [Fintype G] (g : G) :
    Matrix (G × G) (G × G) ℂ := by
  classical
  exact permMatrix (fun p : G × G => (p.1, g * p.2))

end Qatlib.Concepts.HspRecovery.RecordExtract
