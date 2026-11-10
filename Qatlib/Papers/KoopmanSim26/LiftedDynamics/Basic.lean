/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.LiftedDynamics.ResidualDynamics
import Qatlib.Concepts.KoopmanFlow.FlowAction
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

theorem source_exact_lifted_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hclose : ∀ s ∈ Set.Icc 0 T,Dg (x s) (f (x s))=A *ᵥ g (x s)) :
    g (x T)=NormedSpace.exp (T • A) *ᵥ g (x 0) :=
  exact_lifted_closure_on_interval A x f g Dg T hT hx hg hclose

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
