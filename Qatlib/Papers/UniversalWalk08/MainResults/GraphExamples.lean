/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.Basic
import Mathlib.Data.Fin.Basic
set_option warningAsError false

namespace Qatlib.Papers.UniversalWalk08.MainResults.GraphExamples

open Matrix
open Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore

set_option autoImplicit false

theorem zero_isZeroOneHermitianAdjacency :
    IsZeroOneHermitianAdjacency (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · intro i j
    left
    simp
  · simp

theorem zero_maxDegreeLe : MaxDegreeLe (0 : Matrix (Fin 2) (Fin 2) ℂ) 3 := by
  intro i
  simp

def swapAdjacency : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 0 else 1

theorem swapAdjacency_zero_or_one (i j : Fin 2) :
    swapAdjacency i j = 0 ∨ swapAdjacency i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [swapAdjacency]

theorem swapAdjacency_hermitian : swapAdjacencyᴴ = swapAdjacency := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapAdjacency, Matrix.conjTranspose_apply]

theorem swapAdjacency_isZeroOne : IsZeroOneHermitianAdjacency swapAdjacency :=
  ⟨swapAdjacency_zero_or_one, swapAdjacency_hermitian⟩

theorem swapAdjacency_maxDegreeLe : MaxDegreeLe swapAdjacency 3 := by
  intro i
  fin_cases i <;> norm_num [swapAdjacency]

theorem swapAdjacency_walkPropagator_unitary (t : ℝ) :
    (walkPropagator swapAdjacency t)ᴴ * walkPropagator swapAdjacency t = 1 ∧
      walkPropagator swapAdjacency t * (walkPropagator swapAdjacency t)ᴴ = 1 :=
  walkPropagator_unitary_of_adjacency swapAdjacency_isZeroOne t

end Qatlib.Papers.UniversalWalk08.MainResults.GraphExamples
