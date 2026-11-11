/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities

/-!
# Statement of the error-stream probability tables

`ErrorStreamFourCaseTables` states the exact output probabilities for three transforms applied
to a planted progression with disjoint noise: the amplified transform, phase baseline, and
quantum hidden-subgroup baseline. It records the zero-mode formulas and the nonzero-label
formulas in terms of the full marked Fourier sum.

The same statement evaluates that sum in the resonant, off-resonant geometric, and
vanishing-progression cases, under explicit progression, cardinality, oracle, and sparsity
assumptions.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `ErrorStreamFourCaseTables`: the probability-table interface.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

/-- The proposition specifying exact amplified, phase-baseline, and quantum hidden-subgroup
probabilities at zero and nonzero labels, together with the three progression Fourier
branches for disjoint fixed noise. -/
def ErrorStreamFourCaseTables : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (s M L P : ℕ) (G : Finset (Fin N)) (h : Fin N → Bool),
    2 ≤ M → 0 < P → s + (M - 1) * P < N → 2 * (M + L) ≤ N →
    G.card = L → Disjoint G (aqProgressionSet N s M P) →
    (∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) →
    let C := aqProgressionSet N s M P ∪ G
    let T := M + L
    let θ := aqAngle N T
    let k := aqRounds N T
    let F : Fin N → ℂ := fun y => ∑ x ∈ C, aqPhase N x.val y.val
    BornProb (aqState N hN T C) ⟨0, hN⟩ = Real.cos (2 * (k : ℝ) * θ) ^ 2 ∧
    BornProb (aqPhaseBaseline N hN C) ⟨0, hN⟩ = (1 - 2 * (T : ℝ) / (N : ℝ)) ^ 2 ∧
    MeasureProb (aqQHSBaseline N hN h) ({⟨0, hN⟩} ×ˢ Finset.univ) =
      1 - 2 * (T : ℝ) * ((N - T : ℕ) : ℝ) / (N : ℝ) ^ 2 ∧
    (∀ y : Fin N, y.val ≠ 0 →
      BornProb (aqState N hN T C) y =
        (Real.tan θ) ^ 2 * aqGain N T * Complex.normSq (F y) / (T : ℝ) ^ 2 ∧
      BornProb (aqPhaseBaseline N hN C) y = 4 * Complex.normSq (F y) / (N : ℝ) ^ 2 ∧
      MeasureProb (aqQHSBaseline N hN h) ({y} ×ˢ Finset.univ) =
        2 * Complex.normSq (F y) / (N : ℝ) ^ 2) ∧
    (∀ y : Fin N, (P * y.val) % N = 0 →
      F y = (M : ℂ) * aqPhase N s y.val + ∑ z ∈ G, aqPhase N z.val y.val) ∧
    (∀ y : Fin N, (P * y.val) % N ≠ 0 → (M * P * y.val) % N ≠ 0 →
      F y = aqPhase N s y.val *
          ((1 - (aqPhase N P y.val) ^ M) / (1 - aqPhase N P y.val)) +
        ∑ z ∈ G, aqPhase N z.val y.val) ∧
    (∀ y : Fin N, (P * y.val) % N ≠ 0 → (M * P * y.val) % N = 0 →
      F y = ∑ z ∈ G, aqPhase N z.val y.val)
end Qatlib.Concepts.AmpTransform.ErrorStream
