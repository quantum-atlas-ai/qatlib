/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.LocalMeasurementLowerBoundSubgoalStat

/-!
# Legacy local moment contracts

This module records `LocalShotPauliMomentSubgoalLegacy` and
`LocalMeasurementLowerBoundSubgoalLegacy` as propositions. Their second-moment premise
quantifies over all complex operators without a Hermitian restriction. The first specifies
code-state shot moments, and the second specifies a sample lower bound for predictors depending
only on outcome records.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `LocalShotPauliMomentSubgoalLegacy`: states the legacy first- and second-moment implication.
* `LocalMeasurementLowerBoundSubgoalLegacy`: states the legacy prediction-to-sample-bound
  implication.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ClassShadows20.LowerBound
open Matrix
open scoped Classical BigOperators

/-- The legacy proposition asserting local code-state shot mean `w` and second moment at most
`w² * (1 + 9ε² / 3^k)` under the stated ensemble premises. Its second-moment premise ranges
over arbitrary complex operators. -/
def LocalShotPauliMomentSubgoalLegacy : Prop :=
  ∀ (n k : ℕ) (J : Type) [Fintype J] [DecidableEq J]
    (κ : FinDist J) (Uf : J → Operator 2)
    (hκU : ∀ j, 0 < κ.prob j → Uf j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hκ1 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2)
    (hκ2 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6)
    (w : ℝ) (hw : 0 ≤ w)
    (ψ : Fin n → Operator 2) (hψ : ∀ j, IsPureDensityOperator (ψ j))
    (a : Fin n → Option (Fin 3))
    (hk : 1 ≤ k) (hS : tensorPauliWeight a = k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : 3 * ε ≤ 1),
    (∑ uw : Fin n → J, (∏ j, κ.prob (uw j)) *
        localShotValue Uf w ψ uw (theorem6CodeState n ε a) = w)
    ∧ (∑ uw : Fin n → J, (∏ j, κ.prob (uw j)) *
        (localShotValue Uf w ψ uw (theorem6CodeState n ε a)) ^ 2 ≤
      w ^ 2 * (1 + 9 * ε ^ 2 / (3 ^ k : ℝ)))

/-- The legacy proposition asserting `9Nε² / 3^k ≥ (1 - δ) log M - 1` for uniformly successful
outcome-record predictors under the stated measurement and ensemble premises, including an
unrestricted complex second-moment identity. -/
def LocalMeasurementLowerBoundSubgoalLegacy : Prop :=
  ∀ (n k N M : ℕ) (O : Type) [Fintype O] [DecidableEq O]
    (J : Type) [Fintype J] [DecidableEq J]
    (κ : FinDist J) (Uf : J → Operator 2)
    (hκU : ∀ j, 0 < κ.prob j → Uf j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hκ1 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2)
    (hκ2 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6)
    (hk1pos : 1 ≤ k)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : 3 * ε ≤ 1)
    (w : Fin N → O → ℝ) (hw : ∀ j o, 0 ≤ w j o)
    (ψ : Fin N → O → Fin n → Operator 2)
    (hψ : ∀ j o q, IsPureDensityOperator (ψ j o q))
    (hwSum : ∀ j, (∑ o, (w j o * (2 ^ n : ℝ)) • tensorPauliProduct n (ψ j o)) = 1)
    (Pw : Fin M → Fin n → Option (Fin 3))
    (hScard : ∀ m, tensorPauliWeight (Pw m) = k)
    (hPinj : Function.Injective Pw)
    (g : (Fin N → O) → Fin M → ℝ)
    (hg : ∀ (x : Fin M) (uw : Fin n → J),
      1 - δ ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin N → O =>
            ∀ i, |g ω i - 3 * ε * (if i = x then (1 : ℝ) else 0)| ≤ ε),
        ∏ j, localShotValue Uf (w j (ω j)) (ψ j (ω j)) uw
          (theorem6CodeState n ε (Pw x))),
    9 * (N : ℝ) * ε ^ 2 / (3 ^ k : ℝ) ≥ (1 - δ) * Real.log (M : ℝ) - 1

end Qatlib.Papers.ClassShadows20.LowerBound
