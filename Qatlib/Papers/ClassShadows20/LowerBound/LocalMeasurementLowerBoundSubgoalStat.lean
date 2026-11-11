/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.LocalShotPauliMomentSubgoalStat

/-!
# Local measurement lower bound contract

`LocalMeasurementLowerBoundSubgoal` states a conditional sample lower bound for product
measurements of Pauli code states. It quantifies over finite qubit ensembles satisfying the
supplied unitary and moment conditions, normalized local measurements, distinct weight-`k`
signals, and predictors that may use the rotation setting.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `LocalMeasurementLowerBoundSubgoal`: specifies the bound `9Nε² / 3^k ≥ (1 - δ) log M - 1`
  under its prediction hypothesis.

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

/-- The proposition asserting the local measurement sample lower bound under the stated ensemble
moments, measurement completeness, distinct weight-`k` code words, and uniform prediction
guarantee. Predictors may depend on both the local rotation setting and the outcome record. -/
def LocalMeasurementLowerBoundSubgoal : Prop :=
  ∀ (n k N M : ℕ) (O : Type) [Fintype O] [DecidableEq O]
    (J : Type) [Fintype J] [DecidableEq J]
    (κ : FinDist J) (Uf : J → Operator 2)
    (hκU : ∀ j, 0 < κ.prob j → Uf j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hκ1 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2)
    (hκ2 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      A.IsHermitian → B.IsHermitian →
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
    (g : (Fin n → J) → (Fin N → O) → Fin M → ℝ)
    (hg : ∀ (x : Fin M) (uw : Fin n → J),
      1 - δ ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin N → O =>
            ∀ i, |g uw ω i - 3 * ε * (if i = x then (1 : ℝ) else 0)| ≤ ε),
        ∏ j, localShotValue Uf (w j (ω j)) (ψ j (ω j)) uw
          (theorem6CodeState n ε (Pw x))),
    9 * (N : ℝ) * ε ^ 2 / (3 ^ k : ℝ) ≥ (1 - δ) * Real.log (M : ℝ) - 1

end Qatlib.Papers.ClassShadows20.LowerBound
