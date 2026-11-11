/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PauliFrame
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.Checkerboard

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Pauli States

The six literal Pauli eigenvectors of the null prior; true labels the positive eigenprojector.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The six literal Pauli eigenvectors of the null prior; true labels the positive eigenprojector. -/
def sixPauliState (a : Fin 3) (b : Bool) (i : Fin 2) : ℂ :=
  if a.val=2 then if decide (i.val=0)=b then 1 else 0 else
    if i.val=0 then 1/(Real.sqrt 2 : ℂ) else
      (if b then 1 else -1)*(if a.val=1 then Complex.I else 1)/(Real.sqrt 2 : ℂ)

/-- The two columns used on the two checkerboard colors retain one fixed Pauli frame. -/
def pauliCheckerBasis (a : Fin 3) (b : Bool) (color spin : Bool) : ℂ :=
  sixPauliState a (b ^^ color) (boolEquivFin2 spin)

/-- Every one of the six literal prior vectors is physically normalized. -/
theorem sixPauliState_mass (a : Fin 3) (b : Bool) :
    (∑ i : Fin 2, Complex.normSq (sixPauliState a b i)) = 1 := by
  have hroot : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    norm_num [Complex.normSq_ofReal, Real.mul_self_sqrt]
  fin_cases a <;> cases b <;>
    norm_num [sixPauliState, Fin.sum_univ_two, Complex.normSq_div, hroot]

/-- The two actual checkerboard spinors in each fixed six-state frame are unit vectors. -/
theorem pauliCheckerBasis_mass (a : Fin 3) (b color : Bool) :
    qubitMass (pauliCheckerBasis a b color) = 1 := by
  have h := sixPauliState_mass a (b ^^ color)
  simpa only [Fin.sum_univ_two, qubitMass, pauliCheckerBasis, boolEquivFin2,
    Equiv.coe_fn_mk, Bool.false_eq_true, ite_false, ite_true] using h

/-- Opposite outcomes of the same actual Pauli axis give orthogonal physical spinors. -/
theorem pauliCheckerBasis_orthogonal (a : Fin 3) (b color : Bool) :
    overlap (pauliCheckerBasis a b color) (pauliCheckerBasis a b (!color)) = 0 := by
  fin_cases a <;> cases b <;> cases color <;>
    simp [overlap, pauliCheckerBasis, sixPauliState, boolEquivFin2,
      ] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The six literal normalized vectors realize the actual canonical Pauli eigenprojectors entry by entry. -/
theorem sixPauliState_projector (a : Fin 3) (b : Bool) :
    Matrix.vecMulVec (sixPauliState a b) (star (sixPauliState a b)) = PauliProjector a b := by
  have hr : (Real.sqrt 2 : ℂ)^2 = 2 := sqrt2_sq
  have hroot : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  ext i j
  fin_cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    simp [sixPauliState, Matrix.vecMulVec_apply, Pi.star_apply, PauliProjector,
      pauliMatrix, pauliX, pauliY, pauliZ] <;>
      field_simp [hroot] <;> ring_nf <;> norm_num [hr]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
