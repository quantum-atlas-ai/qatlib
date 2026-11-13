/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# State-direction scaling for block preconditioning

This module defines `stateScaling`, its inverse candidate, and the lifted scaling used to
precondition a projected unitary encoding. The lifted matrix is represented as a two-term linear
combination of a reflection and the identity, implemented by `scalingPrepare`,
`preconditionedBranches`, and `preconditionedUnitary`. The module proves action on the
normalized state direction, inverse identities, and intertwining with an isometric output frame.

Linear combinations of unitaries and projected encodings provide the implementation framework
[GilyenSuLowWiebe2019].

## Main statements

* `stateScaling_direction`: Computes the scaling and inverse scaling on the normalized state
  direction.
* `stateScaling_inverse`: Proves both inverse identities for nonzero scale.
* `stateScaling_intertwining`: Relates lifted scaling to scaling on the output space.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.LinearCombination

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

variable {H O : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]

/-- The matrix `1 - (1 - s) • outerProduct b`, scaling the direction of normalized `b` by `s`
and fixing its orthogonal complement. -/
def stateScaling (s : ℝ) (b : QState O) : Matrix O O ℂ :=
  (1 : ℂ) • (1 : Matrix O O ℂ) - ((1 : ℂ) - (s : ℂ)) • outerProduct b

/-- The matrix `1 - (1 - s⁻¹) • outerProduct b`, inverse to `stateScaling s b` when `s ≠ 0` and
`b` is normalized. -/
def stateScalingInverse (s : ℝ) (b : QState O) : Matrix O O ℂ :=
  (1 : ℂ) • (1 : Matrix O O ℂ) - ((1 : ℂ) - (s : ℝ)⁻¹) • outerProduct b

/-- The lifted scaling written as a linear combination of the identity and the reflection about
the complement of `L * outerProduct b * Lᴴ`. -/
def liftedStateScaling (L : Matrix H O ℂ) (b : QState O) (s : ℝ) :
    Matrix H H ℂ :=
  ((1 - s) / 2 : ℂ) •
    ((1 : ℂ) • (1 : Matrix H H ℂ) - (2 : ℂ) • (L * outerProduct b * Lᴴ)) +
  ((1 + s) / 2 : ℂ) • (1 : Matrix H H ℂ)

/-- The real two-dimensional preparation matrix with first column given by the square roots of
`(1 - s) / 2` and `(1 + s) / 2`. -/
def scalingPrepare (s : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | false, false => (Real.sqrt ((1 - s) / 2) : ℂ)
    | true, false => (Real.sqrt ((1 + s) / 2) : ℂ)
    | false, true => -((Real.sqrt ((1 + s) / 2) : ℂ))
    | true, true => (Real.sqrt ((1 - s) / 2) : ℂ)

/-- The two coefficients `(1 - s) / 2` and `(1 + s) / 2` for the reflection and identity
branches. -/
def scalingWeights (s : ℝ) : Bool → ℝ :=
  fun j => match j with
  | false => (1 - s) / 2
  | true => (1 + s) / 2

/-- The two branches are the reflection `1 - 2 • (L * outerProduct b * Lᴴ)` followed by `U`, and
`U` itself. -/
def preconditionedBranches (L : Matrix H O ℂ) (b : QState O) (_s : ℝ)
    (U : Matrix H H ℂ) : Bool → Matrix H H ℂ :=
  fun j => match j with
  | false => ((1 : ℂ) • (1 : Matrix H H ℂ) - (2 : ℂ) • (L * outerProduct b * Lᴴ)) * U
  | true => U

/-- The linear-combination workspace matrix formed from the preconditioned branches and
`scalingPrepare s`. -/
def preconditionedUnitary (L : Matrix H O ℂ) (b : QState O) (s : ℝ)
    (U : Matrix H H ℂ) : Matrix (Bool × H) (Bool × H) ℂ :=
  LCUWorkspace (preconditionedBranches L b s U) (scalingPrepare s)

/-- On a normalized state `b`, the scaling matrix acts by `s` and its inverse candidate acts by
`s⁻¹`. -/
theorem stateScaling_direction (s : ℝ) (b : QState O) (hb : Normalized b) :
    stateScaling s b *ᵥ b = (s : ℂ) • b ∧
      stateScalingInverse s b *ᵥ b = ((s : ℝ)⁻¹ : ℂ) • b := by
  have hp : outerProduct b *ᵥ b = b := by
    rw [outerProduct_mulVec, inner_self_eq_one hb, one_smul]
  constructor <;>
    simp only [stateScaling, stateScalingInverse, one_smul, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, hp] <;>
    module

/-- For nonzero `s` and normalized `b`, the matrices `stateScaling s b` and `stateScalingInverse
s b` are two-sided inverses. -/
theorem stateScaling_inverse (s : ℝ) (b : QState O) (hs : s ≠ 0) (hb : Normalized b) :
    stateScaling s b * stateScalingInverse s b = 1 ∧
      stateScalingInverse s b * stateScaling s b = 1 := by
  have hp : outerProduct b * outerProduct b = outerProduct b :=
    (isOrthogonalProjector_outerProduct hb).1
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hcoef : (1 - (s : ℂ)) + (1 - (s : ℂ)⁻¹) -
      (1 - (s : ℂ)) * (1 - (s : ℂ)⁻¹) = 0 := by field_simp; ring
  constructor <;>
    calc
      _ = 1 - ((1 - (s : ℂ)) + (1 - (s : ℂ)⁻¹) -
          (1 - (s : ℂ)) * (1 - (s : ℂ)⁻¹)) • outerProduct b := by
        simp only [stateScaling, stateScalingInverse, one_smul, Complex.ofReal_inv,
          sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, Matrix.mul_smul,
          smul_smul, hp]
        module
      _ = 1 := by rw [hcoef]; simp

omit [Fintype H] [DecidableEq O] in

/-- The lifted scaling equals `1 - (1 - s) • (L * outerProduct b * Lᴴ)`. -/
theorem liftedStateScaling_eq (L : Matrix H O ℂ) (b : QState O) (s : ℝ) :
    liftedStateScaling L b s = 1 - (1 - (s : ℂ)) • (L * outerProduct b * Lᴴ) := by
  unfold liftedStateScaling
  simp only [one_smul, smul_sub, smul_smul]
  module

/-- For an isometric frame `L`, compressing the lifted scaling by `Lᴴ` equals applying the
output-space scaling after `Lᴴ`. -/
theorem stateScaling_intertwining (L : Matrix H O ℂ) (b : QState O) (s : ℝ)
    (hL : IsIsometry L) :
    Lᴴ * liftedStateScaling L b s = stateScaling s b * Lᴴ := by
  have hl : Lᴴ * L = 1 := hL
  have hp : Lᴴ * (L * outerProduct b * Lᴴ) = outerProduct b * Lᴴ := by
    simp only [← Matrix.mul_assoc, hl, Matrix.one_mul]
  rw [liftedStateScaling_eq]
  simp only [stateScaling, one_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hp]

end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
