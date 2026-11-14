/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Finite spectral exponential damping

This module defines `imaginaryTimeState` as a finite exponentially weighted vector sum and
`gaugeFixedState` by subtracting a reference energy. It computes the derivative and factors out
the common reference-energy exponential.

A strict minimum-energy hypothesis yields convergence of the gauge-fixed curve to its
lowest-energy term. Nonzero coefficient and vector hypotheses then give normalized convergence,
providing finite damping estimates for the imaginary-time framework of [McArdleTew2020].

## Main statements

* `gaugeFixedState_tendsto`: convergence under a strict minimum-energy hypothesis.
* `imaginaryTimeState_normalizedLimit`: normalized convergence when the retained term is
  nonzero.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ImaginaryFlow.GroundLimit

open Filter
open scoped RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite sum of vectors weighted by `exp(-eig i * τ) * c i`. -/
def imaginaryTimeState {ι : Type*} [Fintype ι] (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E)
    (τ : ℝ) : E :=
  ∑ i, (Real.exp (-(eig i) * τ) * c i) • v i

/-- The finite damping sum with every assigned energy shifted by `eig i0`. -/
def gaugeFixedState {ι : Type*} [Fintype ι] (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E)
    (i0 : ι) (τ : ℝ) : E :=
  ∑ i, (Real.exp (-(eig i - eig i0) * τ) * c i) • v i

/-- The derivative of the finite imaginary-time sum is the negative sum of its terms multiplied
by their assigned energies. -/
lemma imaginaryTimeState_hasDerivAt {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E) (τ : ℝ) :
    HasDerivAt (imaginaryTimeState eig c v)
      (-(∑ i, (eig i * (Real.exp (-(eig i) * τ) * c i)) • v i)) τ := by
  unfold imaginaryTimeState
  have hterm : ∀ i : ι, HasDerivAt
      (fun s : ℝ => (Real.exp (-(eig i) * s) * c i) • v i)
      ((-(eig i) * Real.exp (-(eig i) * τ) * c i) • v i) τ := by
    intro i
    have hlin : HasDerivAt (fun s : ℝ => -(eig i) * s) (-(eig i)) τ := by
      simpa using (hasDerivAt_id τ).const_mul (-(eig i))
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(eig i) * s))
        (Real.exp (-(eig i) * τ) * (-(eig i))) τ :=
      (Real.hasDerivAt_exp (x := -(eig i) * τ)).comp τ hlin
    have hmul : HasDerivAt (fun s : ℝ => Real.exp (-(eig i) * s) * c i)
        (Real.exp (-(eig i) * τ) * (-(eig i)) * c i) τ := hexp.mul_const (c i)
    have hsm : HasDerivAt (fun s : ℝ => (Real.exp (-(eig i) * s) * c i) • v i)
        ((Real.exp (-(eig i) * τ) * (-(eig i)) * c i) • v i) τ := hmul.smul_const (v i)
    have hscalar : Real.exp (-(eig i) * τ) * (-(eig i)) * c i =
        -(eig i) * Real.exp (-(eig i) * τ) * c i := by ring
    rw [hscalar] at hsm
    exact hsm
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  have hderiv : (∑ i : ι, ((-(eig i) * Real.exp (-(eig i) * τ) * c i) • v i))
      = -(∑ i : ι, (eig i * (Real.exp (-(eig i) * τ) * c i)) • v i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (-(eig i) * Real.exp (-(eig i) * τ) * c i) =
      -(eig i * (Real.exp (-(eig i) * τ) * c i)) by ring]
    rw [neg_smul]
  rw [← hderiv]
  exact hsum

/-- If `i0` has strictly lower energy than every other index, the gauge-fixed damping curve
converges to `c i0 • v i0`. -/
theorem gaugeFixedState_tendsto {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E) (i0 : ι)
    (hgap : ∀ i, i ≠ i0 → eig i0 < eig i) :
    Tendsto (gaugeFixedState eig c v i0) atTop (𝓝 (c i0 • v i0)) := by
  classical
  unfold gaugeFixedState
  have hterm : ∀ i : ι, Tendsto
      (fun τ : ℝ => (Real.exp (-(eig i - eig i0) * τ) * c i) • v i) atTop
      (𝓝 ((if i = i0 then c i else 0) • v i)) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp
    · have ha : 0 < eig i - eig i0 := sub_pos.mpr (hgap i hi)
      have hinner : Tendsto (fun τ : ℝ => -(eig i - eig i0) * τ) atTop atBot := by
        have hneg : -(eig i - eig i0) < 0 := by linarith
        have h := (Filter.tendsto_const_mul_atBot_of_neg (f := id) (l := atTop) hneg).mpr
          tendsto_id
        simpa using h
      have hexp : Tendsto (fun τ : ℝ => Real.exp (-(eig i - eig i0) * τ)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hinner
      have hmul : Tendsto (fun τ : ℝ => Real.exp (-(eig i - eig i0) * τ) * c i) atTop
          (𝓝 (0 * c i)) := hexp.mul tendsto_const_nhds
      have hsmul := hmul.smul (tendsto_const_nhds (x := v i))
      simpa [hi, zero_mul] using hsmul
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hterm i)
  have hlim : (∑ i : ι, (if i = i0 then c i else 0) • v i) = c i0 • v i0 := by
    simp [ite_smul]
  simpa only [hlim] using hsum

/-- The imaginary-time sum equals the gauge-fixed sum multiplied by `exp(-eig i0 * τ)`. -/
lemma imaginaryTimeState_eq_exp_smul_gaugeFixed {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E) (i0 : ι) (τ : ℝ) :
    imaginaryTimeState eig c v τ =
      Real.exp (-(eig i0) * τ) • gaugeFixedState eig c v i0 τ := by
  unfold imaginaryTimeState gaugeFixedState
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  have hexp : Real.exp (-(eig i) * τ) =
      Real.exp (-(eig i0) * τ) * Real.exp (-(eig i - eig i0) * τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Normalization by inverse norm is unchanged by multiplication by a positive real scalar. -/
lemma inv_norm_smul_eq {r : ℝ} (hr : 0 < r) (u : E) :
    (‖r • u‖)⁻¹ • (r • u) = (‖u‖)⁻¹ • u := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm ‖u‖⁻¹ r, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- If `i0` has strictly lower energy than all other indices and its coefficient and vector are
nonzero, the normalized damping curve converges to the normalized `i0` term. -/
theorem imaginaryTimeState_normalizedLimit {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E) (i0 : ι)
    (hgap : ∀ i, i ≠ i0 → eig i0 < eig i) (hv0 : v i0 ≠ 0) (hc0 : c i0 ≠ 0) :
    Tendsto (fun τ : ℝ => (‖imaginaryTimeState eig c v τ‖)⁻¹ • imaginaryTimeState eig c v τ)
      atTop (𝓝 ((‖c i0 • v i0‖)⁻¹ • (c i0 • v i0))) := by
  have h := gaugeFixedState_tendsto eig c v i0 hgap
  have hL : c i0 • v i0 ≠ 0 := smul_ne_zero hc0 hv0
  have hnorm : Tendsto (fun τ : ℝ => ‖gaugeFixedState eig c v i0 τ‖) atTop
      (𝓝 ‖c i0 • v i0‖) := h.norm
  have hinv : Tendsto (fun τ : ℝ => (‖gaugeFixedState eig c v i0 τ‖)⁻¹) atTop
      (𝓝 (‖c i0 • v i0‖)⁻¹) := hnorm.inv₀ (norm_ne_zero_iff.mpr hL)
  have hscaled := hinv.smul h
  refine Tendsto.congr' ?_ hscaled
  filter_upwards with τ
  rw [imaginaryTimeState_eq_exp_smul_gaugeFixed, inv_norm_smul_eq (Real.exp_pos _)]

end Qatlib.Concepts.ImaginaryFlow.GroundLimit
