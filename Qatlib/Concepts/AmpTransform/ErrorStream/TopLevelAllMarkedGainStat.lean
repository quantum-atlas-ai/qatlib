/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliAmplifiedNoiseConsumers

/-!
# Specification of the all-marked boundary

`TopLevelAllMarkedGain` specifies amplified Fourier sampling when every label is marked. It
records circuit unitarity, concentration at zero, and the Bernoulli weight of the complementary
noise set in the setting of [Cornwell2014].

## Main statements

* `TopLevelAllMarkedGain`: Specifies circuit unitarity and concentration at zero for an entirely
  marked domain, together with the complement's Bernoulli weight and the corresponding weighted
  Born probabilities.

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

/-- Specifies circuit unitarity and concentration at zero for an entirely marked domain,
together with the complement's Bernoulli weight and the corresponding weighted Born
probabilities. -/
def TopLevelAllMarkedGain : Prop :=
  ∀ (N k : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
    ∀ (A : Finset (ZMod N)),
      let C := Finset.univ \ A
      let w := conditionalAmplifiedQFTCircuit N k
      IsUnitaryCircuit w ∧
      (∀ y : ZMod N,
        BornProb (Run (preparedMark (A ∪ C)) w (Ket 0)) y = if y = 0 then 1 else 0) ∧
      (d.prob C = p ^ C.card * (1 - p) ^ A.card) ∧
      (d.prob C * BornProb (Run (preparedMark (A ∪ C)) w (Ket 0)) 0 =
        p ^ C.card * (1 - p) ^ A.card) ∧
      (∀ y : ZMod N, y ≠ 0 →
        d.prob C * BornProb (Run (preparedMark (A ∪ C)) w (Ket 0)) y = 0)

end Qatlib.Concepts.AmpTransform.ErrorStream
