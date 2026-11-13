/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliAmplifiedNoise
import Qatlib.Concepts.AmpTransform.ErrorStream.ConditionalAmplifiedNoiseConsumers

/-!
# Bernoulli noise averages for amplified QFT circuits

This module transports fixed-cardinality signal-plus-noise Fourier moments to Born probabilities
of `conditionalAmplifiedQFTCircuit`. The formulas retain the signal-noise cross term, the
layer-dependent gain, and the avoidance factor for noise disjoint from the signal.

The results apply at nonzero frequency with a nonempty signal and a complement of size at least
two, subject to the stated layer-angle conditions. They also give circuit unitarity and exact
query and gate counts.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `bernoulli_noise_joint_moment_and_actual_qft`: Fourier moments together with actual-circuit
  means.
* `bernoulli_noise_actual_amplified_qft`: layerwise Born means and Bernoulli transport.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open scoped Classical BigOperators

/-- Under the stated complement-size, nonzero-frequency, and layer-angle assumptions, combine
the Bernoulli mixed Fourier moment with exact conditional amplified-QFT Born means, circuit
costs, and complement-layer transport. -/
theorem bernoulli_noise_joint_moment_and_actual_qft :
  ∀ (N k : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
      ∀ (A : Finset (ZMod N)) (y : ZMod N) (θ : ℕ → ℝ),
        let C := Finset.univ \ A
        2 ≤ C.card → 0 < A.card → y ≠ 0 →
        (∀ L : ℕ, L < C.card →
          0 < θ L ∧ θ L < Real.pi / 2 ∧
            (Real.sin (θ L)) ^ 2 = ((A.card + L : ℕ) : ℝ) / N) →
        let w := conditionalAmplifiedQFTCircuit N k
        let a := distinctNoiseFourier A y
        let c := distinctNoiseFourier C y
        let p₂ : ℕ → ℝ := fun L => (L : ℝ) * (L - 1) / ((C.card : ℝ) * (C.card - 1))
        ((∑ S ∈ C.powerset, d.prob S * ‖distinctNoiseFourier (A ∪ S) y‖^2) =
          (1-p)^A.card * (‖a‖^2+2*p*(a*star c).re+(C.card : ℝ)*p+
            p^2*(‖c‖^2-(C.card : ℝ)))) ∧
        (IsUnitaryCircuit w ∧ QueryCount w = k ∧ GateCount w = 3 * k + 2 ∧
        (∀ L : ℕ, L ≤ C.card → ∀ S ∈ C.powersetCard L,
          Disjoint A S ∧ (A ∪ S).card = A.card + L) ∧
        (∀ L : ℕ, L < C.card →
          conditionalNoiseMean C L (fun S =>
              BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y) =
            (conditionalAmplifiedGain k (θ L)) ^ 2 / (N : ℝ) ^ 2 *
              (‖a‖ ^ 2 + 2 * (L : ℝ) / C.card * (a * star c).re + L +
                p₂ L * (‖c‖ ^ 2 - (C.card : ℝ)))) ∧
        ((∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L *
            (1 - p) ^ (C.card - L) *
            conditionalNoiseMean C L (fun S =>
              BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y)) =
          ∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L *
            (1 - p) ^ (C.card - L) *
            ((conditionalAmplifiedGain k (θ L)) ^ 2 / (N : ℝ) ^ 2 *
              (‖a‖ ^ 2 + 2 * (L : ℝ) / C.card * (a * star c).re + L +
                p₂ L * (‖c‖ ^ 2 - (C.card : ℝ))))) ∧
        (∑ S ∈ C.powerset, d.prob S *
            BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y) =
          (1 - p) ^ A.card *
            ∑ L ∈ Finset.range (C.card + 1), p ^ L * (1 - p) ^ (C.card - L) *
              ∑ S ∈ C.powersetCard L,
                BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y) := by
  intro N k _ p hp hp1 d hd A y θ C hC hA hy hθ
  (try dsimp only)
  have hcard : C.card+A.card = N := by
    simpa only [Finset.card_univ, ZMod.card] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hlevel (L : ℕ) (hL : L < C.card) :=
    conditional_noise_actual_amplified_qft N L k A y (θ L) hC hL.le
      (by omega) (by omega) hy (hθ L hL).1 (hθ L hL).2.1 (hθ L hL).2.2
  have hzero := hlevel 0 (by omega)
  refine ⟨(bernoulli_mixed_second_moment N p hp hp1 d hd A y hC).2,
    hzero.1, hzero.2.1, hzero.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro L _hL S hS
    exact conditional_noise_record A S L hS
  · intro L hL
    exact (hlevel L hL).2.2.2.2
  · apply Finset.sum_congr rfl
    intro L hL
    apply congrArg ((C.card.choose L : ℝ)*p^L*(1-p)^(C.card-L) * ·)
    exact (hlevel L (Finset.mem_range.mp hL)).2.2.2.2
  · exact bernoulli_complement_transport N p d hd A _

/-- Under the stated assumptions, give the conditional amplified-QFT circuit costs and exact
nonzero-frequency layer means, their binomial mixture, and the unnormalized disjoint-noise
transport identity; see [Cornwell, Section 3.4.4][Cornwell2014]. -/
theorem bernoulli_noise_actual_amplified_qft :
  ∀ (N k : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
      ∀ (A : Finset (ZMod N)) (y : ZMod N) (θ : ℕ → ℝ),
        let C := Finset.univ \ A
        2 ≤ C.card → 0 < A.card → y ≠ 0 →
        (∀ L : ℕ, L < C.card →
          0 < θ L ∧ θ L < Real.pi / 2 ∧
            (Real.sin (θ L)) ^ 2 = ((A.card + L : ℕ) : ℝ) / N) →
        let w := conditionalAmplifiedQFTCircuit N k
        let a := distinctNoiseFourier A y
        let c := distinctNoiseFourier C y
        let p₂ : ℕ → ℝ := fun L => (L : ℝ) * (L - 1) / ((C.card : ℝ) * (C.card - 1))
        IsUnitaryCircuit w ∧ QueryCount w = k ∧ GateCount w = 3 * k + 2 ∧
        (∀ L : ℕ, L ≤ C.card → ∀ S ∈ C.powersetCard L,
          Disjoint A S ∧ (A ∪ S).card = A.card + L) ∧
        (∀ L : ℕ, L < C.card →
          conditionalNoiseMean C L (fun S =>
              BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y) =
            (conditionalAmplifiedGain k (θ L)) ^ 2 / (N : ℝ) ^ 2 *
              (‖a‖ ^ 2 + 2 * (L : ℝ) / C.card * (a * star c).re + L +
                p₂ L * (‖c‖ ^ 2 - (C.card : ℝ)))) ∧
        ((∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L *
            (1 - p) ^ (C.card - L) *
            conditionalNoiseMean C L (fun S =>
              BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y)) =
          ∑ L ∈ Finset.range C.card, (C.card.choose L : ℝ) * p ^ L *
            (1 - p) ^ (C.card - L) *
            ((conditionalAmplifiedGain k (θ L)) ^ 2 / (N : ℝ) ^ 2 *
              (‖a‖ ^ 2 + 2 * (L : ℝ) / C.card * (a * star c).re + L +
                p₂ L * (‖c‖ ^ 2 - (C.card : ℝ))))) ∧
        (∑ S ∈ C.powerset, d.prob S *
            BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y) =
          (1 - p) ^ A.card *
            ∑ L ∈ Finset.range (C.card + 1), p ^ L * (1 - p) ^ (C.card - L) *
              ∑ S ∈ C.powersetCard L,
                BornProb (Run (preparedMark (A ∪ S)) w (Ket 0)) y := by
  intro N k _ p hp hp1 d hd A y θ C hC hA hy hθ
  exact (bernoulli_noise_joint_moment_and_actual_qft N k p hp hp1 d hd A y θ
    hC hA hy hθ).2

end Qatlib.Concepts.AmpTransform.ErrorStream
