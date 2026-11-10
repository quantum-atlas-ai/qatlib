/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
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

theorem no_orthonormal_pair_singleton (wp wm : Unit → ℂ)
    (hp : ∑ j, ‖wp j‖ ^ 2 = 1) (hm : ∑ j, ‖wm j‖ ^ 2 = 1)
    (ho : ∑ j, star (wp j) * wm j = 0) : False := by
  simp only [Fintype.sum_unique] at hp hm ho
  rcases mul_eq_zero.mp ho with hz | hz
  · have hz' : wp () = 0 := star_eq_zero.mp hz
    simp [hz'] at hp
  · simp [hz] at hm

theorem plusCorner_neg_frames {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (V : Matrix W W ℂ) (L : Matrix W I ℂ)
    (ψ : I → ℂ) : plusCorner V L (-L) ψ = 0 := by
  simp [plusCorner, Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.neg_mulVec]

theorem sparseOverlap_neg_one_frames :
    sparseOverlapRight (-1 : Matrix Unit Unit ℂ) 1 =
      -sparseOverlapLeft (-1 : Matrix Unit Unit ℂ) 1 := by
  ext j i
  rcases j with ⟨u, v⟩ | (u | v) <;>
    simp [sparseOverlapRight, sparseOverlapLeft]

end Qatlib.Concepts.QspSimulation.Achievability
