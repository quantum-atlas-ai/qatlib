/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliAmplifiedNoiseConsumers
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

def BernoulliErrorStreamFourCaseTransport : Prop :=
  ∀ (N k : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
    ∀ (s M P : ℕ) (y : ZMod N) (θ : ℕ → ℝ),
      2 ≤ M → 0 < P → s + (M - 1) * P < N → M + 2 ≤ N → y ≠ 0 →
      (∀ L : ℕ, L < N - M →
        0 < θ L ∧ θ L < Real.pi / 2 ∧
          (Real.sin (θ L)) ^ 2 = ((M + L : ℕ) : ℝ) / (N : ℝ)) →
      let A : Finset (ZMod N) := (Finset.range M).image (fun r : ℕ => (s + r * P : ZMod N))
      let C := Finset.univ \ A
      let w := conditionalAmplifiedQFTCircuit N k
      let a := distinctNoiseFourier A y
      let p₂ : ℕ → ℝ := fun L => (L : ℝ) * (L - 1) / ((C.card : ℝ) * (C.card - 1))
      let g : ℕ → ℝ := fun L => Real.sin ((2 * (k : ℝ) + 1) * θ L) / Real.sin (θ L) -
        Real.cos ((2 * (k : ℝ) + 1) * θ L) / Real.cos (θ L)
      let q : ℂ := ZMod.stdAddChar ((P : ZMod N) * y)
      let mean : ℕ → ℝ := fun L => conditionalNoiseMean C L (fun S =>
        BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y)
      A.card = M ∧ C.card = N - M ∧
      IsUnitaryCircuit w ∧ QueryCount w = k ∧ GateCount w = 3 * k + 2 ∧
      (∀ L : ℕ, L ≤ C.card → ∀ S ∈ C.powersetCard L,
        Disjoint A S ∧ (A ∪ S).card = M + L) ∧
      (∀ L : ℕ, L < C.card →
        mean L = (g L) ^ 2 / (N : ℝ) ^ 2 *
          ((1 - 2 * (L : ℝ) / (C.card : ℝ) + p₂ L) * Complex.normSq a +
            L - p₂ L * (C.card : ℝ))) ∧
      (∀ L : ℕ, L < C.card → (P : ZMod N) * y = 0 →
        mean L = (g L) ^ 2 / (N : ℝ) ^ 2 *
          ((1 - 2 * (L : ℝ) / (C.card : ℝ) + p₂ L) * (M : ℝ) ^ 2 +
            L - p₂ L * (C.card : ℝ))) ∧
      (∀ L : ℕ, L < C.card → (M : ZMod N) * ((P : ZMod N) * y) ≠ 0 →
        mean L = (g L) ^ 2 / (N : ℝ) ^ 2 *
          ((1 - 2 * (L : ℝ) / (C.card : ℝ) + p₂ L) *
            Complex.normSq ((1 - q ^ M) / (1 - q)) +
            L - p₂ L * (C.card : ℝ))) ∧
      (∀ L : ℕ, L < C.card → (P : ZMod N) * y ≠ 0 →
        (M : ZMod N) * ((P : ZMod N) * y) = 0 →
        mean L = (g L) ^ 2 / (N : ℝ) ^ 2 * (L - p₂ L * (C.card : ℝ))) ∧
      (∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L * (1 - p) ^ (C.card - L) *
          mean L =
        ∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L * (1 - p) ^ (C.card - L) *
          ((g L) ^ 2 / (N : ℝ) ^ 2 *
            ((1 - 2 * (L : ℝ) / (C.card : ℝ) + p₂ L) * Complex.normSq a +
              L - p₂ L * (C.card : ℝ)))) ∧
      (∑ S ∈ C.powerset, d.prob S *
          BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y) =
        (1 - p) ^ M * ∑ L ∈ Finset.range (C.card + 1), p ^ L * (1 - p) ^ (C.card - L) *
          ∑ S ∈ C.powersetCard L,
            BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y
end Qatlib.Concepts.AmpTransform.ErrorStream
