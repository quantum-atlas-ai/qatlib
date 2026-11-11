/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.Theorem8RelativeContracts
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityMont

/-!
# Exact-sampling partition-function contract

States the exact-Gibbs-sampling version of Theorem 8 of [Montanaro2015] for the concrete product
of amplified relative estimators. The assumptions specify a monotone schedule starting at zero,
exact Gibbs measurement laws, the Chebyshev schedule inequality, and explicit pilot, layer, and
median parameters.

## Main statements

* `MontanaroTheorem8ExactSamplingSubgoal` requires the cardinality-scaled product of ratio
  medians to estimate the final partition function within relative error `ε` with failure
  probability at most `1 / 4`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PayoffMedian

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

/-- The proposition specifying the exact-sampling partition-function guarantee of Theorem 8 of
[Montanaro2015]. Exact Gibbs preparations, the schedule inequality, and the stated estimator
parameters imply the required relative-error failure bound of `1 / 4`. -/
def MontanaroTheorem8ExactSamplingSubgoal : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (H : Ω → ℕ) (ℓ : ℕ)
    (β : Fin (ℓ + 1) → ℝ) (As : Fin ℓ → Matrix Ω Ω ℂ) (js : Fin ℓ → Ω)
    (B ε : ℝ) (N k r : ℕ),
    0 < ℓ → β 0 = 0 → (∀ i : Fin ℓ, 0 ≤ β i.castSucc ∧ β i.castSucc ≤ β i.succ) →
    (hAs : ∀ i : Fin ℓ, As i ∈ Matrix.unitaryGroup Ω ℂ) →
    1 ≤ B → 0 < ε → ε < 1 →
    32 * B ≤ (N : ℝ) → 4 ≤ k →
    3 * Real.sqrt (B + 1) * (1 / 2 : ℝ) ^ k ≤ ε / (2 * (ℓ : ℝ)) →
    (143 / 144 : ℝ) ^ r ≤ 1 / (4 * (ℓ : ℝ)) →
    (∀ i : Fin (ℓ + 1), 0 < partitionFn H (β i)) →
    (∀ i : Fin ℓ, ∀ x : Ω,
      BornProb (ApplyGate (As i) (Ket (js i))) x
        = Real.exp (-(β i.castSucc * (H x : ℝ))) / partitionFn H (β i.castSucc)) →
    (∀ i : Fin ℓ, partitionFn H (2 * β i.succ - β i.castSucc)
        * partitionFn H (β i.castSucc) ≤ B * partitionFn H (β i.succ) ^ 2) →
    let Y := fun (i : Fin ℓ) (x : Ω) =>
      Real.exp (-((β i.succ - β i.castSucc) * (H x : ℝ)));
    let ps := fun (i : Fin ℓ) => theorem6FactorLaw (As i) (js i) (Y i) B N k r
      (hAs i) (fun x => (Real.exp_pos _).le);
    (independentSampleLaw ps).probEvent
      (fun ξ : Fin 1 → (Fin ℓ → (Fin (2 * r + 1) → ((Fin N → Ω) × LayerRecord k))) =>
        ε * partitionFn H (β (Fin.last ℓ))
          < |(Fintype.card Ω : ℝ) * ∏ i, theorem6FactorMedian (Y i) B N k r (ξ 0 i)
            - partitionFn H (β (Fin.last ℓ))|)
      ≤ 1 / 4

end Qatlib.Concepts.EstimatorLaws.TvStability
