/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix

/-!
# Marked output law of actual amplification trials

The actual prepared amplification circuit scales every marked amplitude by the same sine ratio.
Consequently, each marked output probability factors as the total marked success probability
times its relative Born weight in the prepared state, and this factorization holds for
`preparedAATrial`.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `actual_marked_amplitude`: For marked `i` and marked mass `sin θ` squared with `0 < θ < π/2`,
  `k` amplification iterations scale the prepared amplitude at `i` by `sin ((2 * k + 1) * θ) /
  sin θ`.
* `trial_biased_law`: For marked `i` and marked mass `sin θ` squared with `0 < θ < π/2`, the
  trial output probability at `i` is the total marked-output probability times the prepared Born
  weight of `i` divided by the prepared marked mass.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

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

/-- For marked `i` and marked mass `sin θ` squared with `0 < θ < π/2`, `k` amplification
iterations scale the prepared amplitude at `i` by `sin ((2 * k + 1) * θ) / sin θ`. -/
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

/-- For marked `i` under the first-quadrant angle hypothesis, its Born probability after `k`
amplification iterations is its prepared Born probability times `sin ((2 * k + 1) * θ)`
squared divided by the prepared marked mass. -/
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

/-- The probability of the equality event at `x` in a finite probability mass function is its
point mass at `x`. -/
theorem event_point {X : Type} [Fintype X] [DecidableEq X] (p : PMF X) (x : X) :
    CostedLaw.event p (fun y=>y=x)=p x := by
  simp [CostedLaw.event,CostedLaw.expectation,tsum_fintype]

/-- The probability that a prepared trial returns candidate `i` equals the Born probability at
`i` of its actual amplification circuit. -/
theorem trial_point {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) (i : I) :
    CostedLaw.event (preparedAATrial U hU seed S j) (fun tr=>tr.1.1=i)=
      ENNReal.ofReal (BornProb (Run (preparedMark S) (preparedAACircuit U seed j.val) (Ket seed)) i) := by
  unfold preparedAATrial
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  simp only [event_point]
  rfl

/-- For marked `i` and marked mass `sin θ` squared with `0 < θ < π/2`, the trial output
probability at `i` is the total marked-output probability times the prepared Born weight of
`i` divided by the prepared marked mass. -/
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
