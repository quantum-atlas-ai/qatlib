/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support

/-!
# Elementary frame obstructions

This module records finite-dimensional obstructions relevant to the frame assumptions used in
quantum signal processing constructions [LowChuang2017]. `no_orthonormal_pair_singleton` rules
out an orthonormal pair in a one-dimensional complex space, while the remaining statements
evaluate concrete choices of opposite frames.

The identities `plusCorner_neg_frames` and `sparseOverlap_neg_one_frames` expose cancellation
for `plusCorner` and for the sparse overlap frames of the singleton matrix `-1`. They provide
explicit algebraic facts for checking proposed encoding contracts.

## Main statements

* `no_orthonormal_pair_singleton` derives a contradiction from two unit singleton vectors with
  zero inner product.
* `plusCorner_neg_frames` proves that opposite frames give a zero plus corner.
* `sparseOverlap_neg_one_frames` identifies the right sparse overlap frame with the negative
  left frame in the singleton example.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

/-- Two complex vectors indexed by `Unit` cannot both have squared norm one and have zero inner
product. -/
theorem no_orthonormal_pair_singleton (wp wm : Unit → ℂ)
    (hp : ∑ j, ‖wp j‖ ^ 2 = 1) (hm : ∑ j, ‖wm j‖ ^ 2 = 1)
    (ho : ∑ j, star (wp j) * wm j = 0) : False := by
  simp only [Fintype.sum_unique] at hp hm ho
  rcases mul_eq_zero.mp ho with hz | hz
  · have hz' : wp () = 0 := star_eq_zero.mp hz
    simp [hz'] at hp
  · simp [hz] at hm

/-- The plus corner vanishes when its right frame is the negative of its left frame. -/
theorem plusCorner_neg_frames {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (V : Matrix W W ℂ) (L : Matrix W I ℂ)
    (ψ : I → ℂ) : plusCorner V L (-L) ψ = 0 := by
  simp [plusCorner, Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.neg_mulVec]

/-- For the singleton matrix `-1` and parameter `1`, the right sparse overlap frame is the
negative of the left sparse overlap frame. -/
theorem sparseOverlap_neg_one_frames :
    sparseOverlapRight (-1 : Matrix Unit Unit ℂ) 1 =
      -sparseOverlapLeft (-1 : Matrix Unit Unit ℂ) 1 := by
  ext j i
  rcases j with ⟨u, v⟩ | (u | v) <;>
    simp [sparseOverlapRight, sparseOverlapLeft]

end Qatlib.Concepts.QspSimulation.Achievability
