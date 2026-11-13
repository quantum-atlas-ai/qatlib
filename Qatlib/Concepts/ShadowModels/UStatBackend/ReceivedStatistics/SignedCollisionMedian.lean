/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.RationalPairMedian
import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.SignedCollisionEstimator

/-!
# Rational signed collision medians

This module defines a rational signed residual collision kernel and relates it to the real
statistical kernel. Applying the rational pair-median backend gives a failure bound and an exact
pair-evaluation count for this nonlinear estimator, in the broader setting of
[HuangKuengPreskill2020].

## Main statements

* `kernel_cast`: agreement with the real residual collision kernel.
* `actual_failure`: concentration around the mean squared residual.
* `actual_pair_count`: the exact grouped pair-evaluation count.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian
open Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics
open Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator
open Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian
open scoped BigOperators Classical
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- The rational sign of a record bit, equal to negative one for true and positive one for
false. -/
def sign (b : Bool) : ℚ := if b then -1 else 1

/-- The rational signed residual collision kernel, scaled by the label count on matching labels
and zero on distinct labels. -/
def kernel (a b : ℚ) (u : S → ℚ) (x y : S × Bool) : ℚ :=
  if x.1=y.1 then (Fintype.card S : ℚ)*
    (a*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.sign x.2-b*u x.1)*(a*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.sign y.2-b*u y.1) else 0

omit [Nonempty S] in

/-- Casting the rational collision kernel to the reals gives `residualCollision` with cast
coefficients and reference values. -/
theorem kernel_cast (a b : ℚ) (u : S → ℚ) (x y : S × Bool) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u x y : ℝ) = Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision (a:ℝ) (b:ℝ) (fun z => (u z : ℝ)) x y := by
  by_cases hxy : x.1=y.1
  · simp only [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel,Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision,hxy,if_true]
    cases hx : x.2 <;> cases hy :
        y.2 <;> simp
        [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.sign,Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign]
  · simp [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel,Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision,hxy]

/-- The rational signed collision kernel is symmetric in its two records. -/
theorem kernel_symmetric (a b : ℚ) (u : S → ℚ) (x y : S × Bool) :
    Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u x y=Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u y x := by
  apply Rat.cast_injective (α:=ℝ)
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel_cast]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.collision_symmetric _ _ _ x y

/-- Under the stated variance budget and `n ≥ 2`, the rational collision median deviates from
the uniform mean squared residual by more than `eps` with probability at most `(8 / 9) ^ r`. -/
theorem actual_failure (m : S → ℝ) (hm : ∀ x, |m x|≤1)
    (a b : ℚ) (u : S → ℚ) (n r : ℕ) (hn : 2≤n) (eps : ℝ) (heps : 0<eps)
    (hbudget : Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u) n ≤ eps^2/3) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) n).probEvent
      (fun w : Fin (2*r+1) → Fin n → S × Bool =>
        eps < |((Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u) n r w).1 : ℝ)-Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean m (fun x => (u x : ℝ)) a b|) ≤
      (8/9 : ℝ)^r := by
  have hmean : Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm)
      (fun x y => (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u x y : ℝ))=Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean m (fun x => (u x : ℝ)) a b := by
    simp only [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel_cast]
    simpa only [Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,Finset.mul_sum,mul_assoc,Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean] using!
      Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residual_collision_unbiased m (fun x => (u x : ℝ)) a b hm
  simpa only [hmean] using! Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.failure_bound (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm)
    (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u) n r hn (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel_symmetric a b u) eps heps hbudget

omit [Nonempty S] in

/-- The rational collision median over `2 * r + 1` blocks uses exactly `(2 * r + 1) * n.choose
2` pair evaluations. -/
theorem actual_pair_count (a b : ℚ) (u : S → ℚ) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → S × Bool) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian.kernel a b u) n r w).2=(2*r+1)*n.choose 2 := Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.run_pair_count _ _ _ _

end Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionMedian
