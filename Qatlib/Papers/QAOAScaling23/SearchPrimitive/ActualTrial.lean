/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix
set_option warningAsError false

set_option autoImplicit false
open scoped Classical

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open scoped ENNReal

namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive

theorem actual_marked_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (seed : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : MeasureProb (preparedAAState U seed) S = (Real.sin θ)^2)
    (i : I) (hi : i ∈ S) :
    (Run (preparedMark S) (preparedAACircuit U seed k) (Ket seed)) i =
      ((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ) *
        (preparedAAState U seed) i := by
  rw [prepared_aa_actual_rotation U seed S θ k hU hθ0 hθ1 hmass]
  simp [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, collapse_apply, hi]

theorem actual_marked_born {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (seed : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : MeasureProb (preparedAAState U seed) S = (Real.sin θ)^2)
    (i : I) (hi : i ∈ S) :
    BornProb (Run (preparedMark S) (preparedAACircuit U seed k) (Ket seed)) i =
      (Real.sin ((2*(k:ℝ)+1)*θ))^2 / MeasureProb (preparedAAState U seed) S *
        BornProb (preparedAAState U seed) i := by
  rw [BornProb, actual_marked_amplitude U seed S θ k hU hθ0 hθ1 hmass i hi,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, hmass]
  rfl

theorem event_point {X : Type} [Fintype X] [DecidableEq X] (p : PMF X) (x : X) :
    CostedLaw.event p (fun y=>y=x)=p x := by
  simp [CostedLaw.event,CostedLaw.expectation,tsum_fintype]

theorem trial_point {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) (i : I) :
    CostedLaw.event (preparedAATrial U hU seed S j) (fun tr=>tr.1.1=i)=
      ENNReal.ofReal (BornProb (Run (preparedMark S) (preparedAACircuit U seed j.val) (Ket seed)) i) := by
  unfold preparedAATrial
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  simp only [event_point]
  rfl

theorem trial_biased_law {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (θ : ℝ) (hθ0 : 0<θ) (hθ1 : θ<Real.pi/2)
    (hmass : MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    {m : ℕ} (j : Fin m) (i : I) (hi : i∈S) :
    CostedLaw.event (preparedAATrial U hU seed S j) (fun tr=>tr.1.1=i)=
      CostedLaw.event (preparedAATrial U hU seed S j) (fun tr=>tr.1.1∈S)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
  rw [trial_point,(prepared_aa_trial_actual_metadata U seed S hU j).2.2,
    prepared_aa_born_success U seed S θ j.val hU hθ0 hθ1 hmass,
    actual_marked_born U seed S θ j.val hU hθ0 hθ1 hmass i hi]
  rw [← ENNReal.ofReal_mul (by positivity : 0≤(Real.sin ((2*(j.val:ℝ)+1)*θ))^2)]
  congr 1
  ring
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
