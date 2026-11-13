/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliAmplifiedNoiseConsumers

/-!
# Statement of Bernoulli zero-mode transport

`BernoulliErrorStreamZeroModeTransport` specifies the zero-frequency behavior of the conditional
amplified-QFT circuit for a planted progression and noise on its complement. At each
nonsaturated layer, both the individual and averaged Born probabilities equal `cos (2 * k * θ L)
^ 2`.

The proposition also records progression and complement cardinalities, unitary circuit costs,
binomial mixing, and the avoidance factor in the full disjoint-noise sum.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `BernoulliErrorStreamZeroModeTransport`: the zero-mode conditional and Bernoulli transport
  interface.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

/-- The proposition collecting the exact zero-mode Born probability `cos (2 * k * θ L) ^ 2`, its
fixed-cardinality means and Bernoulli mixtures, progression cardinalities, and circuit costs
under the stated angle and register assumptions. -/
def BernoulliErrorStreamZeroModeTransport : Prop :=
  ∀ (N k : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
    ∀ (s M P : ℕ) (θ : ℕ → ℝ),
      2 ≤ M → 0 < P → s + (M - 1) * P < N → M + 2 ≤ N →
      (∀ L : ℕ, L < N - M →
        0 < θ L ∧ θ L < Real.pi / 2 ∧
          (Real.sin (θ L)) ^ 2 = ((M + L : ℕ) : ℝ) / (N : ℝ)) →
      let A : Finset (ZMod N) := (Finset.range M).image (fun r : ℕ => (s + r * P : ZMod N))
      let C := Finset.univ \ A
      let w := conditionalAmplifiedQFTCircuit N k
      let mean : ℕ → ℝ := fun L => conditionalNoiseMean C L (fun S =>
        BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) 0)
      A.card = M ∧ C.card = N - M ∧
      IsUnitaryCircuit w ∧ QueryCount w = k ∧ GateCount w = 3 * k + 2 ∧
      (∀ L : ℕ, L ≤ C.card → ∀ S ∈ C.powersetCard L,
        Disjoint A S ∧ (A ∪ S).card = M + L) ∧
      (∀ L : ℕ, L < C.card → ∀ S ∈ C.powersetCard L,
        BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) 0 =
          (Real.cos (2 * (k : ℝ) * θ L)) ^ 2) ∧
      (∀ L : ℕ, L < C.card →
        mean L = (Real.cos (2 * (k : ℝ) * θ L)) ^ 2) ∧
      (∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L * (1 - p) ^ (C.card - L) *
          mean L =
        ∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L * (1 - p) ^ (C.card - L) *
          (Real.cos (2 * (k : ℝ) * θ L)) ^ 2) ∧
      (∑ S ∈ C.powerset, d.prob S *
          BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) 0) =
        (1 - p) ^ M * ∑ L ∈ Finset.range (C.card + 1), p ^ L * (1 - p) ^ (C.card - L) *
          ∑ S ∈ C.powersetCard L,
            BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) 0
end Qatlib.Concepts.AmpTransform.ErrorStream
