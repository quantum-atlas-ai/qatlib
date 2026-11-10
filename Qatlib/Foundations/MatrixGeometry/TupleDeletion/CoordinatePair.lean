/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.SliceGram
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.SliceInner
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.CoordinateEnergy
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

theorem coordinate_pair_bound (v : EuclideanSpace ℂ (InjectiveTuple I L)) (i j : I)
    (hij : i ≠ j) (hL : 0 < Fintype.card L) :
    -(inner ℂ v (coordinateAction (L := L) i v)).re-
      (inner ℂ v (coordinateAction (L := L) j v)).re ≤
        2*(inner ℂ (coordinateAction (L := L) i v) (coordinateAction (L := L) j v)).re := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (I → L)))
    (fun f _hf => coordinateGram_slice_bound (WithLp.ofLp v) f i j hij)
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib,← Finset.mul_sum] at h
  rw [sum_pair_inner_re (WithLp.ofLp v) (coordinateGram i*ᵥ WithLp.ofLp v) i j hij,
    sum_pair_inner_re (WithLp.ofLp v) (coordinateGram j*ᵥ WithLp.ofLp v) i j hij,
    sum_pair_inner_re (coordinateGram i*ᵥ WithLp.ofLp v) (coordinateGram j*ᵥ WithLp.ofLp v) i j hij] at h
  simp only [nsmul_eq_mul,WithLp.toLp_ofLp] at h
  have hc : (0 : ℝ) < (Fintype.card L*Fintype.card L : ℕ) := by exact_mod_cast Nat.mul_pos hL hL
  apply (mul_le_mul_iff_right₀ hc).mp
  simpa only [coordinateAction,Matrix.toLpLin_apply,mul_add,mul_sub,mul_neg,mul_assoc,mul_comm,mul_left_comm] using! h
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
