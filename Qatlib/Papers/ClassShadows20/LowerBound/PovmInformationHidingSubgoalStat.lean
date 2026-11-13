/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Papers.ClassShadows20.LowerBound.PovmInformationHidingDefs

/-!
# POVM information hiding contract

`PovmInformationHidingSubgoal` states a finite entropy bound for a complete positive
semidefinite measurement applied to rotated projector code operators. Its hypotheses specify
projector traces, parameter ranges, unitarity on the ensemble support, and exact first and
Hermitian second rotation moments.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `PovmInformationHidingSubgoal`: specifies the entropy-gap upper bound `α²(d - r) / (r(d +
  1))`.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Matrix
open scoped ComplexOrder
open scoped Classical BigOperators

/-- The proposition asserting an outcome entropy gap at most `α² * (d - r) / (r * (d + 1))` for
the stated finite POVM and uniformly indexed projector codes. The implication assumes the
specified parameter ranges and exact first and Hermitian second rotation moments. -/
def PovmInformationHidingSubgoal : Prop :=
  ∀ (d r M : ℕ) (O : Type) [Fintype O] [DecidableEq O]
    (I : Type) [Fintype I] [DecidableEq I]
    (F : O → Operator d)
    (hFpsd : ∀ o, (F o).PosSemidef) (hFsum : (∑ o, F o) = 1)
    (P : Fin M → Operator d)
    (hP : ∀ x, (P x).IsHermitian ∧ P x * P x = P x ∧
      Matrix.trace (P x) = ((r : ℕ) : ℂ))
    (hd : 2 ≤ d) (hr : 0 < r) (hrd : r ≤ d) (hM : 0 < M)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (μ : FinDist I) (Uf : I → Operator d)
    (hμU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (s : ℝ) (hs : s = (1 - α ^ 2) / (d : ℝ) + α ^ 2 / (r : ℝ))
    (h1 : ∀ x : Fin M,
      (∑ i, μ.prob i • (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ)) =
        (1 / (d : ℝ)) • 1)
    (h2 : ∀ x : Fin M, ∀ A B : Operator d,
      A.IsHermitian → B.IsHermitian →
      (∑ i, μ.prob i *
          (Matrix.trace (A * (Uf i * lemma8CodeState d r α (P x) *
            (Uf i)ᴴ))).re *
          (Matrix.trace (B * (Uf i * lemma8CodeState d r α (P x) *
            (Uf i)ᴴ))).re) =
        ((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace A).re * (Matrix.trace B).re +
        ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
          (Matrix.trace (A * B)).re),
    (∑ o, Real.negMulLog
        ((1 / (M : ℝ)) * ∑ x, ∑ i,
          μ.prob i * (Matrix.trace (F o *
            (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re)) -
      (1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i * ∑ o, Real.negMulLog
        ((Matrix.trace (F o *
          (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re) ≤
      α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1))

end Qatlib.Papers.ClassShadows20.LowerBound
