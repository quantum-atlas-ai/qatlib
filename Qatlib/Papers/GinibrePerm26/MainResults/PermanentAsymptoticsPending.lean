/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GinibrePerm26.MainResults.LinearOpticsComplexityModelsDefs
open Qatlib.Concepts.BosonFock.PermAnalysis
open Qatlib.Papers.GinibrePerm26.MainResults

/-! Unfinished asymptotic vocabulary: `IsBigOInProbability` currently quantifies
a scale M that is absent from its event. This is not standard O_P(a_n).
Retained in Dev for correction under the original persistent goal; existing
FQNs and mathematical definitions are preserved verbatim. -/

namespace Qatlib.Papers.GinibrePerm26.MainResults

set_option autoImplicit false

open MeasureTheory

/-! ## Corollary 1.2: logarithmic asymptotics in probability -/

/-- `X_n = O_P(a_n)`: for every `δ > 0` there is `M > 0` and `N` such that
`P(a_n < |X_n|) ≤ δ` for all `n ≥ N`. -/
def IsBigOInProbability (X : ℕ → Measure ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (X n) {x : ℝ | a n < |x|} ≤ ENNReal.ofReal δ

/-- Logarithmic asymptotics of the permanent (Corollary 1.2):
`log|per_𝕂 G_n| = ½ log(n!) + O_P(log n) = (n/2) log n − n/2 + O_P(log n)`.
On the null set `{per = 0}` Mathlib's `Real.log` is `0`. -/
def LogarithmicPermanentAsymptotics (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] : Prop :=
  IsBigOInProbability
    (fun n => Measure.map
      (fun G : Matrix (Fin n) (Fin n) S =>
        Real.log ‖rowOrderedPermanent S G‖ - (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ))
      (ginibreLaw S n))
    (fun n => Real.log n) ∧
  IsBigOInProbability
    (fun n => Measure.map
      (fun G : Matrix (Fin n) (Fin n) S =>
        Real.log ‖rowOrderedPermanent S G‖ - ((n : ℝ) / 2 * Real.log n - (n : ℝ) / 2))
      (ginibreLaw S n))
    (fun n => Real.log n)

end Qatlib.Papers.GinibrePerm26.MainResults
