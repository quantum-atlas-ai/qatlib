/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.GramAction
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.SliceMask
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

theorem masked_R_coordinateGram (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) :
    sliceMask f i j (R (pairSlice v f i j))=pairSlice (coordinateGram (L := L) i*ᵥ v) f i j := by
  ext p
  let g := Function.update (Function.update f i p.val.1) j p.val.2
  by_cases hg : Function.Injective g
  · change (if Function.Injective g then R (pairSlice v f i j) p else 0)=extend (coordinateGram i*ᵥ v) g
    rw [if_pos hg]
    have he := extend_injective (coordinateGram i*ᵥ v) (⟨g,hg⟩ : InjectiveTuple I L)
    change extend (coordinateGram i*ᵥ v) g=(coordinateGram i*ᵥ v)
        (⟨g,hg⟩ : InjectiveTuple I L) at he
    rw [he,coordinateGram_apply,pairSlice_R v f i j hij]
    apply Finset.sum_congr rfl
    intro a ha
    have hu : Function.update g i a=Function.update (Function.update f i a) j p.val.2 := by
      dsimp [g]
      rw [Function.update_comm hij.symm,Function.update_idem]
    exact congrArg (extend v) hu.symm
  · change (if Function.Injective g then _ else 0)=extend (coordinateGram i*ᵥ v) g
    simp [hg,extend]

theorem masked_S_coordinateGram (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) :
    sliceMask f i j (S (pairSlice v f i j))=pairSlice (coordinateGram (L := L) j*ᵥ v) f i j := by
  ext p
  let g := Function.update (Function.update f i p.val.1) j p.val.2
  by_cases hg : Function.Injective g
  · change (if Function.Injective g then S (pairSlice v f i j) p else 0)=extend (coordinateGram j*ᵥ v) g
    rw [if_pos hg]
    have he := extend_injective (coordinateGram j*ᵥ v) (⟨g,hg⟩ : InjectiveTuple I L)
    change extend (coordinateGram j*ᵥ v) g=(coordinateGram j*ᵥ v)
        (⟨g,hg⟩ : InjectiveTuple I L) at he
    rw [he,coordinateGram_apply,pairSlice_S v f i j hij]
    apply Finset.sum_congr rfl
    intro a ha
    have hu : Function.update g j a=Function.update (Function.update f i p.val.1) j a := by
      dsimp [g]
      rw [Function.update_idem]
    exact congrArg (extend v) hu.symm
  · change (if Function.Injective g then _ else 0)=extend (coordinateGram j*ᵥ v) g
    simp [hg,extend]

theorem coordinateGram_slice_bound (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) :
    -(inner ℂ (pairSlice v f i j) (pairSlice (coordinateGram (L := L) i*ᵥ v) f i j)).re-
      (inner ℂ (pairSlice v f i j) (pairSlice (coordinateGram (L := L) j*ᵥ v) f i j)).re ≤
      2*(inner ℂ (pairSlice (coordinateGram (L := L) i*ᵥ v) f i j)
        (pairSlice (coordinateGram (L := L) j*ᵥ v) f i j)).re := by
  simpa only [masked_R_coordinateGram v f i j hij,masked_S_coordinateGram v f i j hij] using
    masked_pair_resampling v f i j hij
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
