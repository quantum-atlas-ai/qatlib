/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClusterColumns

@[expose] public section


/-! The six exact orders of the fixed three-projector model.
The finite permutation cases preserve the original projector labels and source matrices. -/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels

open ThreeLevelCluster

namespace ThreeLevelCollisionRelabeling

open ThreeLevelCollisionRelabeling
def lowSwap (σ : Perm) : Perm := (Equiv.swap 0 1).trans σ

def highSwap (σ : Perm) : Perm := (Equiv.swap 1 2).trans σ

def order102 : Perm := lowSwap (Equiv.refl (Fin 3))

def order021 : Perm := highSwap (Equiv.refl (Fin 3))

/-- Order102 apply for the stated finite source data. -/
theorem order102_apply (i : Fin 3) : order102 i = ![1,0,2] i := by
  fin_cases i <;> decide

/-- Order021 apply for the stated finite source data. -/
theorem order021_apply (i : Fin 3) : order021 i = ![0,2,1] i := by
  fin_cases i <;> decide

end ThreeLevelCollisionRelabeling

namespace ThreeLevelOrder201

open ThreeLevelCollisionRelabeling
def order201 : Perm := lowSwap order021

def order210 : Perm := highSwap order201

/-- Order210 apply for the stated finite source data. -/
theorem order210_apply (i : Fin 3) : order210 i = ![2,1,0] i := by
  fin_cases i <;> decide

/-- Order201 apply for the stated finite source data. -/
theorem order201_apply (i : Fin 3) : order201 i = ![2,0,1] i := by
  fin_cases i <;> decide

end ThreeLevelOrder201

namespace ThreeLevelOrder120

open ThreeLevelCollisionRelabeling
open ThreeLevelOrder201
def order120 : Perm := highSwap order102

/-- Order120 apply for the stated finite source data. -/
theorem order120_apply (i : Fin 3) : order120 i = ![1,2,0] i := by
  fin_cases i <;> decide

end ThreeLevelOrder120

namespace ThreeLevelCollisionCoverage

open ThreeLevelCollisionRelabeling ThreeLevelOrder201 ThreeLevelOrder120

/-- Permutation cases for the stated finite source data. -/
theorem permutation_cases : ∀ σ : Perm,
    σ = Equiv.refl (Fin 3) ∨ σ = order102 ∨ σ = order021 ∨
      σ = order201 ∨ σ = order120 ∨ σ = order210 := by decide

end ThreeLevelCollisionCoverage

end Qatlib.Papers.GibbsSampl26.FiniteModels
