/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.HadamardAnn19.NativeReduction.Examples
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.QuboForms

def exampleTwo : Fin 2 → Fin 2 → Bool := ![![false,true],![true,true]]

theorem exampleTwo_frame : IsOrthogonalFrame exampleTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram,signMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_two,exampleTwo,spin,bit]

def exampleFour : Fin 4 → Fin 4 → Bool :=
  ![![true,true,false,false],![false,true,false,true],
    ![true,true,true,true],![true,false,false,true]]

theorem exampleFour_frame : IsOrthogonalFrame exampleFour := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram,signMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_succ,exampleFour,spin,bit]

theorem completed_frame_ground {M N : ℕ} (hM : 2 ≤ M)
    (q : Fin M → Fin N → Bool) (hq : IsOrthogonalFrame q) :
    IsGround (paperEnergy (4*(M:ℝ)^2)) (complete q) := by
  apply (source_ground_iff hM _).mpr
  refine ⟨complete_pair_valid q,?_⟩
  intro y
  change energy q ≤ energy y
  rw [(energy_zero_iff q).mpr hq]
  exact energy_nonneg y

theorem exampleTwo_ground : IsGround (paperEnergy 16) (complete exampleTwo) := by
  convert completed_frame_ground (by decide) exampleTwo exampleTwo_frame using 1
  norm_num

theorem exampleFour_ground : IsGround (paperEnergy 64) (complete exampleFour) := by
  convert completed_frame_ground (by decide) exampleFour exampleFour_frame using 1
  norm_num

end Qatlib.Papers.HadamardAnn19.NativeReduction.Examples
