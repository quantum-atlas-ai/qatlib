/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.SliceSum
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.PairSlices
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

theorem sum_pair_inner (u v : InjectiveTuple I L → ℂ) (i j : I) (hij : i ≠ j) :
    (∑ f : I → L,inner ℂ (pairSlice u f i j) (pairSlice v f i j))=
      (Fintype.card L*Fintype.card L) •
        inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (InjectiveTuple I L)) (WithLp.toLp 2 v) := by
  let w : InjectiveTuple I L → ℂ := fun y => star (u y)*v y
  have he (f : I → L) : inner ℂ (pairSlice u f i j) (pairSlice v f i j)=
      ∑ p : Pair L,extend w (Function.update (Function.update f i p.val.1) j p.val.2) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro p hp
    rw [RCLike.inner_apply']
    by_cases h : Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2)
    · simp [pairSlice,extend,h,w]
    · simp [pairSlice,extend,h]
  simp_rw [he]
  rw [sum_pair_slices (extend w) i j hij (by
    intro f hf
    have hn : ¬ Function.Injective f := fun h => hij (h hf)
    simp [extend,hn]),sum_extend]
  congr 1
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro y hy
  rw [RCLike.inner_apply']
  rfl

theorem sum_pair_inner_re (u v : InjectiveTuple I L → ℂ) (i j : I) (hij : i ≠ j) :
    (∑ f : I → L,(inner ℂ (pairSlice u f i j) (pairSlice v f i j)).re)=
      (Fintype.card L*Fintype.card L) •
        (inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (InjectiveTuple I L)) (WithLp.toLp 2 v)).re := by
  have h := congrArg (Complex.reAddGroupHom : ℂ → ℝ) (sum_pair_inner u v i j hij)
  simpa only [map_sum,map_nsmul] using! h
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
