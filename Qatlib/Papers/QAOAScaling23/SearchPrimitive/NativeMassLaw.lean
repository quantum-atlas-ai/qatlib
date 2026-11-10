/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.NativeEndpoint
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive

theorem mass_angle (Q : ℝ) (hQ0 : 0<Q) (hQ1 : Q<1) :
    ∃θ : ℝ,0<θ ∧θ<Real.pi/2 ∧Q=(Real.sin θ)^2 := by
  have hs0 : 0<Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs1 : Real.sqrt Q<1 := by nlinarith [Real.sq_sqrt hQ0.le]
  refine ⟨Real.arcsin (Real.sqrt Q),Real.arcsin_pos.mpr hs0,
    Real.arcsin_lt_pi_div_two.mpr hs1,?_⟩
  rw [Real.sin_arcsin (by linarith) hs1.le,Real.sq_sqrt hQ0.le]

theorem native_positive_mass_biased_law {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I→Bool) (hvalid : ∀y,valid y=true↔y∈S)
    (hQ0 : 0<MeasureProb (preparedAAState U seed) S)
    (hQ1 : MeasureProb (preparedAAState U seed) S≤1) (ms : List ℕ) (i : I) (hi : i∈S) :
    event (searchForSchedule U hU seed S valid (1::ms)) (fun tr=>tr.result=some i)=
      event (searchForSchedule U hU seed S valid (1::ms)) (fun tr=>tr.result.isSome)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
  rcases lt_or_eq_of_le hQ1 with hlt|heq
  · obtain ⟨θ,hθ0,hθ1,hmass⟩ := mass_angle _ hQ0 hlt
    exact Qatlib.Papers.QAOAScaling23.SearchPrimitive.native_search_biased_law U hU seed S valid hvalid θ hθ0 hθ1 hmass (1::ms) i hi
  · exact Qatlib.Papers.QAOAScaling23.SearchPrimitive.native_search_Q_one_biased_law U hU seed S valid hvalid heq ms i hi
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
