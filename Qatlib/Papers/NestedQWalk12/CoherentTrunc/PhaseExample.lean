/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NestedQWalk12.CoherentTrunc.Native

/-!
# A phase example for coherent truncation

This module tests the overlap estimate discussed in [JefferyKothariMagniez2013] on a normalized
two-branch input. The amplitudes are 4/5 and 3/5, the branch unitaries are 1 and -1 on a
one-dimensional system, and truncation at cutoff zero replaces the second branch by the
identity.

`actual_tail` computes discarded mass 9/25, while `actual_inner` computes overlap 7/25. Thus
`printed_step_fails` shows that the overlap norm can be smaller than 1 minus the discarded mass.

## Main statements

* `family_unitary`: both scalar branches are unitary.
* `input_normalized`: the coherent input is normalized.
* `actual_inner`: the full and truncated outputs have inner product 7/25.
* `printed_step_fails`: the stronger overlap estimate fails for this example.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.NestedQWalk12.CoherentTrunc.PhaseExample
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Foundations.MatrixGeometry.BranchUnitary

/-- The two complex branch amplitudes 4/5 and 3/5. -/
def amplitudes : Fin 2 → ℂ := ![4/5,3/5]

/-- The constant conditional state with amplitude one on the one-dimensional system for each
branch. -/
def conditional : Fin 2 → State (Fin 1) := fun _ _ => 1

/-- The one-dimensional unitary family with scalar 1 on branch zero and scalar -1 on branch one. -/
def family (c : Fin 2) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal (fun _ => if c = 0 then 1 else -1)

/-- The query labels zero and one for the two branches. -/
def costs (c : Fin 2) : ℕ := c.val

/-- Each member of `family` is a unitary matrix. -/
theorem family_unitary (c : Fin 2) : family c ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (family c)ᴴ * family c = 1
  ext s t
  fin_cases c <;> fin_cases s <;> fin_cases t <;>
    norm_num [family, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one]

/-- The coherent input formed from `amplitudes` and `conditional` is normalized. -/
theorem input_normalized : Normalized (coherent amplitudes conditional) := by
  unfold Normalized
  norm_num [coherent, amplitudes, conditional, Fintype.sum_prod_type,
    Fin.sum_univ_one, Fin.sum_univ_two, norm_div]

/-- Truncating the example at cutoff zero discards branch mass 9/25 in the setting of
[JefferyKothariMagniez2013]. -/
theorem actual_tail : tailMass amplitudes costs 0 = (9 : ℝ)/25 := by
  norm_num [tailMass, amplitudes, costs, Fin.sum_univ_two, norm_div]

/-- The inner product of the full controlled output and its cutoff-zero truncation is exactly
7/25. -/
theorem actual_inner :
    Inner (controlled family *ᵥ coherent amplitudes conditional)
      (controlled (truncated family costs 0) *ᵥ coherent amplitudes conditional) = (7 : ℂ)/25 := by
  norm_num [Qatlib.Foundations.MatrixGeometry.LcuFrame.Inner,
    dotProduct, controlled, Matrix.mulVec, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
    coherent, amplitudes, conditional, family, truncated, costs, Matrix.diagonal_apply,
    map_ofNat]

/-- In this example, the output overlap norm is strictly less than 1 minus `tailMass`, providing
a counterexample to the stronger truncation estimate discussed in
[JefferyKothariMagniez2013]. -/
theorem printed_step_fails :
    ‖Inner (controlled family *ᵥ coherent amplitudes conditional)
      (controlled (truncated family costs 0) *ᵥ coherent amplitudes conditional)‖ <
      1 - tailMass amplitudes costs 0 := by
  rw [actual_inner, actual_tail]
  norm_num [norm_div]

end Qatlib.Papers.NestedQWalk12.CoherentTrunc.PhaseExample
