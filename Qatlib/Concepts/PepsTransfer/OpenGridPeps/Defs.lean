/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Open-grid PEPS contraction definitions

This module defines a rectangular projected entangled pair state by local tensors with one
physical index and four virtual indices. The amplitude `amplitude` sums over internal horizontal
and vertical bonds while fixing every external virtual index to zero.

The alternative contraction `rowAmplitude` is the zero-boundary entry of an ordered product of
row transfer matrices. This implements the row-contraction viewpoint for PEPS described in
[VerstraeteMurgCirac2008].

## Main statements

* `Tensor`: local tensor data on the rectangular grid.
* `value`: local evaluation with internal bonds and fixed outer boundary.
* `amplitude`: contraction over internal bonds.
* `rowMatrix` and `rowAmplitude`: row transfer matrices and their boundary contraction.

## References

* [Verstraete, Murg, and Cirac, 2008][VerstraeteMurgCirac2008]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.PepsTransfer.OpenGridPeps
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- A rectangular array of complex PEPS tensors with one physical index and four virtual indices
at each cell. -/
abbrev Tensor (a b d D : ℕ) := Fin a→Fin b→Fin d→Fin D→Fin D→Fin D→Fin D→ℂ

/-- Evaluates a local tensor using the assigned internal horizontal and vertical bonds and zero
virtual indices on the outer boundary. -/
def value {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d)
    (h : Fin a×Fin (b-1)→Fin D) (v : Fin (a-1)×Fin b→Fin D) (i : Fin a) (j : Fin b) : ℂ :=
  let z : Fin D := ⟨0,hD⟩
  let up : Fin D := if hi : 0 < i.val then v (⟨i.val-1,by omega⟩,j) else z
  let dn : Fin D := if hi : i.val+1 < a then v (⟨i.val,by omega⟩,j) else z
  let lf : Fin D := if hj : 0 < j.val then h (i,⟨j.val-1,by omega⟩) else z
  let rt : Fin D := if hj : j.val+1 < b then h (i,⟨j.val,by omega⟩) else z
  A i j (x i j) up dn lf rt

/-- The open-grid PEPS amplitude obtained by summing the product of local tensor values over
internal bond assignments. -/
noncomputable def amplitude {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d) : ℂ :=
  ∑ h : Fin a×Fin (b-1)→Fin D, ∑ v : Fin (a-1)×Fin b→Fin D, ∏ i, ∏ j, value hD A x h v i j

/-- The row transfer matrix obtained by contracting horizontal internal bonds with zero
horizontal boundary indices and specified upper and lower virtual rows. -/
noncomputable def rowMatrix {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D)
    (x : Fin a→Fin b→Fin d) (i : Fin a) : Matrix (Fin b→Fin D) (Fin b→Fin D) ℂ := fun up dn=>
  ∑ h : Fin (b-1)→Fin D, ∏ j : Fin b,
    A i j (x i j) (up j) (dn j)
      (if hj : 0 < j.val then h ⟨j.val-1,by omega⟩ else ⟨0,hD⟩)
      (if hj : j.val+1 < b then h ⟨j.val,by omega⟩ else ⟨0,hD⟩)

/-- The zero-boundary matrix entry of the ordered product of row transfer matrices. -/
noncomputable def rowAmplitude {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d) : ℂ :=
  ((List.ofFn (rowMatrix hD A x)).prod) (fun _=>⟨0,hD⟩) (fun _=>⟨0,hD⟩)

end Qatlib.Concepts.PepsTransfer.OpenGridPeps
