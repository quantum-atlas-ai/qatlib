/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.PairSlices
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

def sliceMask (f : I → L) (i j : I) (u : EuclideanSpace ℂ (Pair L)) : EuclideanSpace ℂ (Pair L) :=
  WithLp.toLp 2 (fun p => if Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2) then u p else 0)
omit [Fintype L] in

theorem sliceMask_pairSlice (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) :
    sliceMask f i j (pairSlice v f i j)=pairSlice v f i j := by
  ext p
  change (if Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2) then
    extend v (Function.update (Function.update f i p.val.1) j p.val.2) else 0)=_
  by_cases h : Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2)
  · rw [if_pos h]
    rfl
  · change _=extend v (Function.update (Function.update f i p.val.1) j p.val.2)
    simp [h,extend]

theorem sliceMask_expectation (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I)
    (u : EuclideanSpace ℂ (Pair L)) :
    inner ℂ (pairSlice v f i j) (sliceMask f i j u)=inner ℂ (pairSlice v f i j) u := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [RCLike.inner_apply',RCLike.inner_apply']
  by_cases h : Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2)
  · change star (pairSlice v f i j p)*(if Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2) then u p else 0)=_
    rw [if_pos h]
    rfl
  · have hz : pairSlice v f i j p=0 := by
      change extend v (Function.update (Function.update f i p.val.1) j p.val.2)=0
      simp [extend,h]
    simp [hz]

theorem sliceMask_cross (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) :
    inner ℂ (sliceMask f i j (R (pairSlice v f i j))) (sliceMask f i j (S (pairSlice v f i j)))=
      inner ℂ (R (pairSlice v f i j)) (S (pairSlice v f i j)) := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [RCLike.inner_apply',RCLike.inner_apply']
  by_cases h : Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2)
  · change star (if Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2) then R (pairSlice v f i j) p else 0)*
      (if Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2) then S (pairSlice v f i j) p else 0)=_
    rw [if_pos h,if_pos h]
    rfl
  · have hmR : sliceMask f i j (R (pairSlice v f i j)) p=0 := if_neg h
    have hmS : sliceMask f i j (S (pairSlice v f i j)) p=0 := if_neg h
    rcases pairSlice_invalid_output v f i j hij p h with hr | hs
    · rw [hmR,hr];simp
    · rw [hmS,hs];simp

theorem masked_pair_resampling (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) :
    -(inner ℂ (pairSlice v f i j) (sliceMask f i j (R (pairSlice v f i j)))).re-
      (inner ℂ (pairSlice v f i j) (sliceMask f i j (S (pairSlice v f i j)))).re ≤
        2*(inner ℂ (sliceMask f i j (R (pairSlice v f i j))) (sliceMask f i j (S (pairSlice v f i j)))).re := by
  rw [sliceMask_expectation,sliceMask_expectation,sliceMask_cross v f i j hij]
  exact pair_resampling_unscaled (pairSlice v f i j)
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
