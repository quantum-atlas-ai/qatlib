/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.StatePrep.UnknownProbability

/-!
# Observable preparation cost and output guarantees

This module exposes the final observable preparation guarantees for the input construction
associated with [ZhangEtAl2026]. For a nonzero target with values bounded by a positive scale,
`observable_preparation_cost` gives a uniform expected cost bound for the finite truncations of
the schedule that does not require the success probability as input, together with failure
probability tending to zero. `balanced_observable_preparation` replaces the norm dependent
factor by a bound determined by the fraction and size of sufficiently large observable
amplitudes.

The output statement `observable_preparation_output` identifies the accumulated successful
density for every finite fuel and starting offset. It is exactly the normalized complex target's
pure density multiplied by the probability of success, connecting the cost and termination
guarantees to the state actually produced.

## Main statements

* `observable_preparation_cost` bounds every finite expected cost by 496 sqrt(2^n) G divided by
  the target norm and proves vanishing failure.
* `balanced_observable_preparation` gives the expected cost bound 496/(c sqrt(eta)) under
  balanced amplitude assumptions.
* `observable_preparation_output` identifies the successful output density with the success
  probability times `outerProduct` of `postselected`.

## References

* [Zhang et al., 2026][ZhangEtAl2026], Quantum simulation of real-world nonlinear dynamics via
  Koopman method.
-/

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

/-- For positive G, observable values bounded by G, and a nonzero target, every finite
truncation of the schedule starting at offset zero has expected cost at most 496 sqrt(2^n) G
divided by the target norm, making the norm dependence of observable preparation in
[ZhangEtAl2026] explicit. Its failure probability tends to zero as the fuel tends to
infinity. -/
theorem observable_preparation_cost {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) :
    let A := preparation b value G
    let hA := preparation_unitary b value G hG hvalue
    (∀ fuel, expectedCost (stages A hA (seed n m) (goodSet n m) 0 fuel) ≤
      ENNReal.ofReal (496*(Real.sqrt ((2:ℝ)^n)*G/Real.sqrt (targetNormSq b value)))) ∧
    Filter.Tendsto (fun fuel => (failure (stages A hA (seed n m) (goodSet n m) 0 fuel)).toReal)
      Filter.atTop (nhds 0) :=
  unknown_observables_source b value G hG hvalue hu

/-- For positive G, c, and eta, observable values bounded by G with nonzero target and an eta
fraction of amplitude norms at least cG give every finite truncation starting at offset zero
expected cost at most 496/(c sqrt(eta)), under the balanced observable conditions of
[ZhangEtAl2026]. Its failure probability tends to zero as the fuel tends to infinity. -/
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

/-- For positive G, observable values bounded by G, and a nonzero target, the stopped successful
density at any fuel and starting offset is the outer product of `postselected` multiplied by
the success probability, which is one minus the failure probability. This preserves the
normalized complex observable target from the construction of [ZhangEtAl2026]. -/
theorem observable_preparation_output {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0)
    (fuel off : ℕ) :
    stoppedDensity b value G hG hvalue off fuel =
      ((1-(failure (stages (preparation b value G) (preparation_unitary b value G hG hvalue)
        (seed n m) (goodSet n m) off fuel)).toReal : ℝ) : ℂ) • outerProduct (postselected b value G) :=
  unknown_stopped_density b value G hG hvalue hu fuel off

end Qatlib.Papers.KoopmanSim26.StatePrep
