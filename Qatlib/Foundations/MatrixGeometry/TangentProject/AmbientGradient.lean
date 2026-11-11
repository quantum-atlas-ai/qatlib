/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.IsApply
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic
import Mathlib.Tactic.CongrExclamation
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Ambient derivatives of matrix conjugation and gradients

Defines the conjugation map `stateMap ψ U = U * ψ * Uᴴ` and the commutator expression
`gradientExtension`. Explicit real continuous linear maps `stateDerivative` and
`gradientDerivative` are proved to be their Fréchet derivatives at every complex matrix. See
[HunzikerEtAl2003] for related background.

## Main statements

* `stateMap_hasFDerivAt`: The conjugation map has real Fréchet derivative `stateDerivative ψ U`
  at `U`.
* `gradientExtension_hasFDerivAt`: The ambient gradient expression has real Fréchet derivative
  `gradientDerivative O ψ U` at `U`.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixGeometry.TangentProject
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The matrix conjugation expression `U * ψ * Uᴴ`. -/
def stateMap (ψ U : Matrix n n ℂ) : Matrix n n ℂ := U * ψ * Uᴴ

/-- The ambient matrix expression `(O * stateMap ψ U - stateMap ψ U * O) * U`. -/
def gradientExtension (O ψ U : Matrix n n ℂ) : Matrix n n ℂ :=
  (O * stateMap ψ U - stateMap ψ U * O) * U

/-- The real continuous linear map sending a variation `V` to `V * ψ * Uᴴ + U * ψ * Vᴴ`. -/
def stateDerivative (ψ U : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (U * ψ)).comp
    (starL' ℝ).toContinuousLinearMap) +
  ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip Uᴴ).comp
    ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip ψ)

/-- Evaluating `stateDerivative ψ U` on `V` gives `V * ψ * Uᴴ + U * ψ * Vᴴ`. -/
theorem stateDerivative_apply (ψ U V : Matrix n n ℂ) :
    stateDerivative ψ U V = V * ψ * Uᴴ + U * ψ * Vᴴ := by
  change U * ψ * Vᴴ + V * ψ * Uᴴ = V * ψ * Uᴴ + U * ψ * Vᴴ
  exact add_comm _ _

/-- The conjugation map has real Fréchet derivative `stateDerivative ψ U` at `U`. -/
theorem stateMap_hasFDerivAt (ψ U : Matrix n n ℂ) :
    HasFDerivAt (stateMap ψ) (stateDerivative ψ U) U := by
  have hi := hasFDerivAt_id (𝕜 := ℝ) U
  have h := (hi.mul_const' ψ).fun_mul' hi.star
  convert! h using 1

/-- The real continuous linear map sending `V` to `[O, stateDerivative ψ U V] * U + [O, stateMap
ψ U] * V`, where brackets denote matrix commutators. -/
def gradientDerivative (O ψ U : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip U).comp
    (((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) O) -
      (ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip O).comp (stateDerivative ψ U)) +
  ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (O * stateMap ψ U - stateMap ψ U * O)

/-- The derivative expression for the ambient gradient is the sum of the commutator with the
state variation, multiplied by `U`, and the state commutator multiplied by `V`. -/
theorem gradientDerivative_apply (O ψ U V : Matrix n n ℂ) :
    gradientDerivative O ψ U V =
      (O * (V * ψ * Uᴴ + U * ψ * Vᴴ) - (V * ψ * Uᴴ + U * ψ * Vᴴ) * O) * U +
        (O * (U * ψ * Uᴴ) - (U * ψ * Uᴴ) * O) * V := by
  simp [gradientDerivative, stateDerivative_apply, stateMap]
  noncomm_ring

/-- The ambient gradient expression has real Fréchet derivative `gradientDerivative O ψ U` at
`U`. -/
theorem gradientExtension_hasFDerivAt (O ψ U : Matrix n n ℂ) :
    HasFDerivAt (gradientExtension O ψ) (gradientDerivative O ψ U) U := by
  have hs := stateMap_hasFDerivAt ψ U
  have h := ((hs.const_mul O).fun_sub (hs.mul_const' O)).fun_mul'
    (hasFDerivAt_id (𝕜 := ℝ) U)
  convert! h using 1
  ext V : 1
  simp only [gradientDerivative_apply]
  change (O * (V * ψ * Uᴴ + U * ψ * Vᴴ) - (V * ψ * Uᴴ + U * ψ * Vᴴ) * O) * U +
    (O * stateMap ψ U - stateMap ψ U * O) * V =
    (O * stateMap ψ U - stateMap ψ U * O) * V +
    (O * (stateDerivative ψ U V) - (stateDerivative ψ U V) * O) * U
  rw [stateDerivative_apply]
  exact add_comm _ _

/-- The real Fréchet derivative of `gradientExtension O ψ` applied to `V` equals `[O, V * ψ * Uᴴ
+ U * ψ * Vᴴ] * U + [O, U * ψ * Uᴴ] * V`, where brackets denote commutators. -/
theorem gradientExtension_fderiv_apply (O ψ U V : Matrix n n ℂ) :
    fderiv ℝ (gradientExtension O ψ) U V =
      (O * (V * ψ * Uᴴ + U * ψ * Vᴴ) - (V * ψ * Uᴴ + U * ψ * Vᴴ) * O) * U +
        (O * (U * ψ * Uᴴ) - (U * ψ * Uᴴ) * O) * V := by
  rw [(gradientExtension_hasFDerivAt O ψ U).fderiv]
  exact gradientDerivative_apply O ψ U V
