/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NestedQWalk12.CoherentTrunc.Native
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.NestedQWalk12.CoherentTrunc.PhaseExample
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Foundations.MatrixGeometry.BranchUnitary

def amplitudes : Fin 2 → ℂ := ![4/5,3/5]

def conditional : Fin 2 → State (Fin 1) := fun _ _ => 1

def family (c : Fin 2) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal (fun _ => if c = 0 then 1 else -1)

def costs (c : Fin 2) : ℕ := c.val

theorem family_unitary (c : Fin 2) : family c ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (family c)ᴴ * family c = 1
  ext s t
  fin_cases c <;> fin_cases s <;> fin_cases t <;>
    norm_num [family, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one]

theorem input_normalized : Normalized (coherent amplitudes conditional) := by
  unfold Normalized
  norm_num [coherent, amplitudes, conditional, Fintype.sum_prod_type,
    Fin.sum_univ_one, Fin.sum_univ_two, norm_div]

theorem actual_tail : tailMass amplitudes costs 0 = (9 : ℝ)/25 := by
  norm_num [tailMass, amplitudes, costs, Fin.sum_univ_two, norm_div]

theorem actual_inner :
    Inner (controlled family *ᵥ coherent amplitudes conditional)
      (controlled (truncated family costs 0) *ᵥ coherent amplitudes conditional) = (7 : ℂ)/25 := by
  norm_num [Qatlib.Foundations.MatrixGeometry.LcuFrame.Inner,
    dotProduct, controlled, Matrix.mulVec, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
    coherent, amplitudes, conditional, family, truncated, costs, Matrix.diagonal_apply,
    map_ofNat]

theorem printed_step_fails :
    ‖Inner (controlled family *ᵥ coherent amplitudes conditional)
      (controlled (truncated family costs 0) *ᵥ coherent amplitudes conditional)‖ <
      1 - tailMass amplitudes costs 0 := by
  rw [actual_inner, actual_tail]
  norm_num [norm_div]

end Qatlib.Papers.NestedQWalk12.CoherentTrunc.PhaseExample
