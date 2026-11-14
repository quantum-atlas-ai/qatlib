/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

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
