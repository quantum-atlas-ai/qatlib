/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamSuccessMass

/-!
# Specification of continued-fraction candidate recording

This module defines `aqCandidateRecord`, its query cost, and `aqSourceSuccessfulWindow`, then
states their combined recovery guarantee in `FullLayerCFDenoiseUniqueP`. The contract controls
the probability that the planted period appears among verified candidates in the noisy
amplified-transform setting of [Cornwell2014].

## Main statements

* `aqCandidateRecord`: The list of period candidates returned by `aqAttempt` on the input
  samples, retaining order and repetitions and discarding unsuccessful attempts.
* `aqSourceSuccessfulWindow`: The finite set of samples y whose ratio y/N is within 1/(2P²) of a
  reduced fraction a/P with a < P.
* `FullLayerCFDenoiseUniqueP`: The recovery contract giving positive successful-window mass,
  continued-fraction denominators, repeated planted-period inclusion, verified recorded
  candidates, and a query bound under the stated noisy-progression assumptions.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.FullLayerCF

/-- The list of period candidates returned by `aqAttempt` on the input samples, retaining order
and repetitions and discarding unsuccessful attempts. -/
def aqCandidateRecord {N : ℕ} (h : Fin N → Bool) (s M B : ℕ)
    (xs : List (Fin N)) : List ℕ :=
  xs.filterMap (fun y => (aqAttempt h s M B y).1)

/-- The total query cost of the candidate-record procedure, charging k amplification queries and
the attempt's verification queries for each sample. -/
def aqCandidateRecordQueries {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) : ℕ :=
  (xs.map (fun y => k + (aqAttempt h s M B y).2.1)).sum

/-- The finite set of samples y whose ratio y/N is within 1/(2P²) of a reduced fraction a/P with
a < P. -/
def aqSourceSuccessfulWindow (N P : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun y => ∃ a < P, Nat.Coprime a P ∧
    |(y.val : ℚ) / N - (a : ℚ) / P| ≤ 1 / (2 * (P : ℚ) ^ 2))

/-- The recovery contract giving positive successful-window mass, continued-fraction
denominators, repeated planted-period inclusion, verified recorded candidates, and a query
bound under the stated noisy-progression assumptions. -/
def FullLayerCFDenoiseUniqueP : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (s M L P B R v : ℕ) (G : Finset (Fin N)) (h : Fin N → Bool),
    2 ≤ M → 2 ≤ P → s + (M - 1) * P < N → M * P ≤ N → P ≤ B → 2 * B ^ 2 < N →
    G.card = L → Disjoint G (aqProgressionSet N s M P) →
    2 * (M + L) ≤ N → (L : ℝ) < 2 * (M : ℝ) / Real.pi → 0 < R → 0 < v →
    (∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) →
    let C := aqProgressionSet N s M P ∪ G
    let T := M + L
    let w : Fin N → ℝ := fun y => BornProb (aqState N hN T C) y
    let q := aqErrorSuccessLower N M L P
    let k := aqRounds N T
    (0 < q ∧ q ≤ 1) ∧
    q ≤ MeasureProb (aqState N hN T C) (aqSourceSuccessfulWindow N P) ∧
    (∀ y ∈ aqSourceSuccessfulWindow N P, ∃ a n : ℕ,
      a < P ∧ Nat.Coprime a P ∧
      (a : ℚ) / P = ((y.val : ℝ) / N).convergent n ∧
      (((y.val : ℝ) / N).convergent n).den = P) ∧
    (∑ ω : Fin R → Fin N, if P ∈ aqCandidateRecord h s M B (List.ofFn ω)
      then aqProductMass w ω else 0) ≥ 1 - (1 - q) ^ R ∧
    (∀ ω : Fin R → Fin N, ∀ p ∈ aqCandidateRecord h s M B (List.ofFn ω),
      (aqVerify h s M p).1 = true) ∧
    (∀ ω : Fin R → Fin N,
      aqCandidateRecordQueries h s M B k (List.ofFn ω) ≤ R * (k + 3 * v))

end Qatlib.Concepts.AmpTransform.FullLayerCF
