/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.MedianEstimate

/-!
# Median amplitude-estimation guarantees

This module states the concrete median-estimation proposition `EstimateSandwich` used in the
variable-time development of [Ambainis2012]. At each prescribed resolution `M ≥ 2`, an odd
number of fresh amplitude-estimation runs gives a normalized outcome law, the specified good-set
probability and error radius, zero output on positive-probability outcomes when the input mass
is zero, and an exact access count.

## Main statements

* `EstimateSandwich`: The median estimator's probability, accuracy, Born-law, and cost
  guarantees.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate

/-- The proposition that, for every unitary preparation, resolution `M ≥ 2`, and `0 < δ ≤ 1`,
some odd number `2 * r + 1` of fresh estimation runs gives the stated median accuracy with
probability at least `1 - δ` and exact cost `(2 * r + 1) * (6 * M - 3)`. It also requires
the circuit Born law and zero estimates on positive-probability outcomes when the marked
mass is zero. -/
def EstimateSandwich : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ),
    ∀ (hA : A∈Matrix.unitaryGroup I ℂ),∀ (j : I) (S : Finset I) (M : ℕ) (hM : 2 ≤ M)
      (δ : ℝ),0 < δ → δ ≤ 1 →
    ∃ r : ℕ,
      (∑ ω : Fin (2*r+1) → Fin M,(aeLaw M A j S hA hM).probOf ω=1) ∧
      (∀ ω : Fin (2*r+1) → Fin M,0 ≤ (aeLaw M A j S hA hM).probOf ω) ∧
      (1-δ ≤ ∑ ω∈vtMedianGood M r (MeasureProb (preparedAAState A j) S),(aeLaw M A j S hA hM).probOf ω) ∧
      (∀ ω∈vtMedianGood M r (MeasureProb (preparedAAState A j) S),
        |vtMedianEstimate M r ω-MeasureProb (preparedAAState A j) S| ≤ vtEstimateRadius (MeasureProb (preparedAAState A j) S) M) ∧
      (MeasureProb (preparedAAState A j) S=0 → ∀ ω,0 < (aeLaw M A j S hA hM).probOf ω → vtMedianEstimate M r ω=0) ∧
      (∀ ω : Fin (2*r+1) → Fin M,(aeLaw M A j S hA hM).probOf ω=
        MeasureProb (Run 1 (vtFreshAECircuit M A j S (2*r+1)) (vtFreshAEInput M hM j (2*r+1)))
          (Finset.univ.filter (fun p=>vtFreshLabel (2*r+1) p=ω))) ∧
      (QueryCount (vtFreshAECircuit M A j S (2*r+1))+GateCount (vtFreshAECircuit M A j S (2*r+1))=(2*r+1)*(6*M-3))
end Qatlib.Papers.VarTimeAmpAmp10.Estimate
