/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.StatePrep.UnknownProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Papers.KoopmanSim26.StatePrep.Observables
open Qatlib.Papers.KoopmanSim26.StatePrep.LowerSchedule
open scoped Classical ENNReal
open Qatlib.Papers.KoopmanSim26.StatePrep.UnknownSchedule

namespace Qatlib.Papers.KoopmanSim26.StatePrep

theorem observable_preparation_cost {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) :
    let A := preparation b value G
    let hA := preparation_unitary b value G hG hvalue
    (∀ fuel, expectedCost (stages A hA (seed n m) (goodSet n m) 0 fuel) ≤
      ENNReal.ofReal (496*(Real.sqrt ((2:ℝ)^n)*G/Real.sqrt (targetNormSq b value)))) ∧
    Filter.Tendsto (fun fuel => (failure (stages A hA (seed n m) (goodSet n m) 0 fuel)).toReal)
      Filter.atTop (nhds 0) :=
  unknown_observables_source b value G hG hvalue hu

theorem balanced_observable_preparation {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (hη : 0 < η)
    (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    let A := preparation b value G
    let hA := preparation_unitary b value G hG hvalue
    (∀ fuel, expectedCost (stages A hA (seed n m) (goodSet n m) 0 fuel) ≤
      ENNReal.ofReal (496/(c*Real.sqrt η))) ∧
    Filter.Tendsto (fun fuel => (failure (stages A hA (seed n m) (goodSet n m) 0 fuel)).toReal)
      Filter.atTop (nhds 0) :=
  unknown_balanced_source b value G c η hG hc hη hvalue hu S hcard hbig

theorem observable_preparation_output {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0)
    (fuel off : ℕ) :
    stoppedDensity b value G hG hvalue off fuel =
      ((1-(failure (stages (preparation b value G) (preparation_unitary b value G hG hvalue)
        (seed n m) (goodSet n m) off fuel)).toReal : ℝ) : ℂ) • outerProduct (postselected b value G) :=
  unknown_stopped_density b value G hG hvalue hu fuel off

end Qatlib.Papers.KoopmanSim26.StatePrep
