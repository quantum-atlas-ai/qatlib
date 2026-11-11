/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.LiftedDynamics.ResidualDynamics
import Qatlib.Concepts.KoopmanFlow.FlowAction

/-!
# Finite lifted closure and residual bounds

This module exposes interval-based results for a differentiable observable vector `g` along a
trajectory satisfying the original nonlinear dynamics. The residual `liftResidual` measures the
difference between the observable derivative and the proposed finite matrix evolution, as in the
lifted-dynamics framework of [ZhangEtAl2026].

The result `source_lifted_residual_identity` expresses the resulting propagation error as a
Duhamel integral. Exact closure removes that error, while dissipativity bounds its Euclidean
norm by the time integral of the residual norm.

## Main statements

* `source_lifted_residual_identity` gives the propagated residual integral on a nonnegative time
  interval.
* `source_exact_lifted_closure` identifies exact observable evolution with the matrix
  exponential under closure.
- `source_lifted_residual_bound` bounds lifted evolution error for a dissipative generator.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.KoopmanSim26.LiftedDynamics.Calculus

namespace Qatlib.Papers.KoopmanSim26.LiftedDynamics

/-- If `x' = f(x)` and `Dg` is the derivative of `g` along `x` on `[0, T]`, with nonnegative `T`
and continuous residual there, then `g(x(T)) - exp(T A) g(x(0))` is the integral of
`exp((T-s) A)` applied to the residual. This gives the finite lifted residual identity
associated with [ZhangEtAl2026]. -/
theorem source_lifted_residual_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hr : ContinuousOn (liftResidual A x f g Dg) (Set.Icc 0 T)) :
    g (x T)-NormedSpace.exp (T • A) *ᵥ g (x 0) =
      ∫ s in 0..T,NormedSpace.exp ((T-s) • A) *ᵥ liftResidual A x f g Dg s :=
  lifted_residual_duhamel_on_interval A x f g Dg T hT hx hg hr

/-- If `x' = f(x)`, `Dg` is the derivative of `g` along `x`, and `Dg(x(s))(f(x(s))) = A g(x(s))`
throughout `[0, T]`, then the lifted endpoint equals `exp(T A) g(x(0))` for nonnegative `T`.
This gives the exact finite-closure case of [ZhangEtAl2026]. -/
theorem source_exact_lifted_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hclose : ∀ s ∈ Set.Icc 0 T,Dg (x s) (f (x s))=A *ᵥ g (x s)) :
    g (x T)=NormedSpace.exp (T • A) *ᵥ g (x 0) :=
  exact_lifted_closure_on_interval A x f g Dg T hT hx hg hclose

/-- For dissipative `A`, assume `x' = f(x)`, that `Dg` is the derivative of `g` along `x`, and
that the residual is continuous on `[0, T]` with nonnegative `T`. The Euclidean lifted
propagation error is at most the integral of the residual norm, giving the residual control
associated with [ZhangEtAl2026]. -/
theorem source_lifted_residual_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : ((-A)+(-A).conjTranspose).PosSemidef)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hr : ContinuousOn (liftResidual A x f g Dg) (Set.Icc 0 T)) :
    ‖toEuclidean_fromVec (g (x T)-NormedSpace.exp (T • A) *ᵥ g (x 0))‖ ≤
      ∫ s in 0..T,‖toEuclidean_fromVec (liftResidual A x f g Dg s)‖ :=
  lifted_residual_norm_bound_on_interval A hA x f g Dg T hT hx hg hr

end Qatlib.Papers.KoopmanSim26.LiftedDynamics
