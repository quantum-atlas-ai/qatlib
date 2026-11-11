/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Defs

/-!
# Phase multiplication on complex L2

A measurable real function defines the unit-modulus multiplier `phase`. `phaseMap` realizes
multiplication by this function on complex `L²`, preserving addition, scalar multiplication, and
norm.

Negating the phase gives an inverse, yielding the complex linear isometry equivalence
`phaseEquiv`. These phase operations are building blocks for continuous-variable
differential-equation algorithms such as [ArrazolaEtAl2019].

## Main statements

* `phaseMap`: Phase multiplication on equivalence classes in L2.
* `phaseMap_repr`: Almost-everywhere formula for representatives.
* `phaseEquiv`: Invertible complex linear isometry.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Qatlib.Foundations.L2Dynamics.PhaseShears.Phase
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
/-- The space of square-integrable complex functions modulo almost-everywhere equality with
respect to `μ`. -/
abbrev H := Lp ℂ 2 μ

/-- The complex phase factor `exp(i * p x)`. -/
def phase (p : X → ℝ) (x : X) : ℂ := Complex.exp (Complex.I*(p x:ℂ))
omit [MeasurableSpace X] in

/-- The phase factor associated with a real-valued function has norm one. -/
theorem phase_norm (p : X→ℝ) (x : X) : ‖phase p x‖=1 := by
  simp [phase,Complex.norm_exp]

/-- Multiplication of an L2 representative by a measurable phase remains square-integrable. -/
theorem phase_mem (p : X→ℝ) (hp : Measurable p) (ψ : H μ) :
    MemLp (fun x=>phase p x*ψ x) 2 μ := by
  apply (Lp.memLp ψ).congr_norm
  · exact ((Complex.measurable_exp.comp (measurable_const.mul hp.complex_ofReal)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable ψ)
  · exact Filter.Eventually.of_forall fun x=>by rw [norm_mul,phase_norm,one_mul]

/-- Multiplication by a measurable unit-modulus phase, realized as an element of complex L2. -/
def phaseMap (p : X→ℝ) (hp : Measurable p) (ψ : H μ) : H μ :=
  (phase_mem μ p hp ψ).toLp _

/-- A representative of `phaseMap` agrees almost everywhere with pointwise phase multiplication. -/
theorem phaseMap_repr (p : X→ℝ) (hp : Measurable p) (ψ : H μ) :
    phaseMap μ p hp ψ =ᵐ[μ] fun x=>phase p x*ψ x :=
  (phase_mem μ p hp ψ).coeFn_toLp

/-- Phase multiplication preserves the L2 norm. -/
theorem phaseMap_norm (p : X→ℝ) (hp : Measurable p) (ψ : H μ) :
    ‖phaseMap μ p hp ψ‖=‖ψ‖ := by
  rw [phaseMap,Lp.norm_toLp,Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (phase_mem μ p hp ψ).aestronglyMeasurable (Lp.aestronglyMeasurable ψ)
      (Filter.Eventually.of_forall fun x=>by rw [norm_mul,phase_norm,one_mul])

/-- Phase multiplication is additive on L2. -/
theorem phaseMap_add (p : X→ℝ) (hp : Measurable p) (ψ φ : H μ) :
    phaseMap μ p hp (ψ+φ)=phaseMap μ p hp ψ+phaseMap μ p hp φ := by
  apply Lp.ext
  filter_upwards [phaseMap_repr μ p hp (ψ+φ),phaseMap_repr μ p hp ψ,phaseMap_repr μ p hp φ,Lp.coeFn_add ψ φ,Lp.coeFn_add (phaseMap μ p hp ψ) (phaseMap μ p hp φ)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1,h5,h2,h3,h4,mul_add]

/-- Phase multiplication commutes with complex scalar multiplication on L2. -/
theorem phaseMap_smul (p : X→ℝ) (hp : Measurable p) (c : ℂ) (ψ : H μ) :
    phaseMap μ p hp (c•ψ)=c•phaseMap μ p hp ψ := by
  apply Lp.ext
  filter_upwards [phaseMap_repr μ p hp (c•ψ),phaseMap_repr μ p hp ψ,Lp.coeFn_smul c ψ,Lp.coeFn_smul c (phaseMap μ p hp ψ)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply,smul_eq_mul] at h3 h4
  rw [h1,h4,h2,h3]
  ring

/-- Phase multiplication bundled as a complex linear isometry of L2. -/
def phaseLI (p : X→ℝ) (hp : Measurable p) : H μ →ₗᵢ[ℂ] H μ where
  toFun := phaseMap μ p hp
  map_add' := phaseMap_add μ p hp
  map_smul' := phaseMap_smul μ p hp
  norm_map' := phaseMap_norm μ p hp

/-- Multiplication by the negative phase undoes multiplication by the original phase. -/
theorem phaseMap_neg_left (p : X→ℝ) (hp : Measurable p) (ψ : H μ) :
    phaseMap μ (fun x=>-p x) hp.neg (phaseMap μ p hp ψ)=ψ := by
  apply Lp.ext
  filter_upwards [phaseMap_repr μ (fun x=>-p x) hp.neg (phaseMap μ p hp ψ),phaseMap_repr μ p hp ψ] with x h1 h2
  rw [h1,h2]
  dsimp only [phase]
  rw [← mul_assoc,← Complex.exp_add]
  simp

/-- Multiplication by the original phase undoes multiplication by the negative phase. -/
theorem phaseMap_neg_right (p : X→ℝ) (hp : Measurable p) (ψ : H μ) :
    phaseMap μ p hp (phaseMap μ (fun x=>-p x) hp.neg ψ)=ψ := by
  simpa only [neg_neg] using phaseMap_neg_left μ (fun x=>-p x) hp.neg ψ

/-- Phase multiplication as a complex linear isometry equivalence, with inverse given by the
negative phase. -/
def phaseEquiv (p : X→ℝ) (hp : Measurable p) : H μ ≃ₗᵢ[ℂ] H μ :=
  LinearIsometryEquiv.ofLinearIsometry (phaseLI μ p hp) (phaseLI μ (fun x=>-p x) hp.neg).toLinearMap
    (by apply LinearMap.ext;intro ψ;exact phaseMap_neg_right μ p hp ψ)
    (by apply LinearMap.ext;intro ψ;exact phaseMap_neg_left μ p hp ψ)
end Qatlib.Foundations.L2Dynamics.PhaseShears.Phase
