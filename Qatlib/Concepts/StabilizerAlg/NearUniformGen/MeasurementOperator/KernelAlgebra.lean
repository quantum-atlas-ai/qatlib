/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Finite measurement-kernel algebra

`mixtureDist` averages conditional finite distributions against a branch law. `productKernel`
forms a conditionally independent pair of outputs at a shared branch, and its probability lemmas
identify the product and swap laws used for composite measurements. For background, see
[Kitaev1995].

## Main statements

* `mixtureDist_prob`: expands a mixture probability as a branch-weighted sum.
* `productKernel_swap`: identifies pair probabilities after swapping the two conditional
  kernels.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator

/-- The finite output distribution formed by averaging a conditional kernel against a finite
branch distribution. -/
def mixtureDist {Ω G : Type*} [Fintype Ω] [Fintype G]
    (P : FinDist Ω) (k : Ω → FinDist G) : FinDist G where
  prob y := ∑ V, P.prob V * (k V).prob y
  nonneg y := Finset.sum_nonneg fun V _ => mul_nonneg (P.nonneg V) ((k V).nonneg y)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
    exact P.sum_one

/-- A mixture probability is the sum of branch probabilities times conditional output
probabilities, as in [Kitaev, Lemma 8][Kitaev1995]. -/
theorem mixtureDist_prob {Ω G : Type*} [Fintype Ω] [Fintype G]
    (P : FinDist Ω) (k : Ω → FinDist G) (y : G) :
    (mixtureDist P k).prob y = ∑ V, P.prob V * (k V).prob y := rfl

/-- The conditional joint kernel obtained by independently sampling two finite output laws at
the same branch. -/
def productKernel {Ω G H : Type*} [Fintype G] [Fintype H]
    (k : Ω → FinDist G) (h : Ω → FinDist H) : Ω → FinDist (G × H) :=
  fun V => FinDist.independentPair (k V) (h V)

/-- At a fixed branch, the product-kernel probability of a pair is the product of its component
probabilities, as used in [Kitaev, Lemma 8][Kitaev1995]. -/
theorem productKernel_prob {Ω G H : Type*} [Fintype G] [Fintype H]
    (k : Ω → FinDist G) (h : Ω → FinDist H) (V : Ω) (g : G) (z : H) :
    (productKernel k h V).prob (g, z) = (k V).prob g * (h V).prob z := rfl

/-- Swapping two conditional kernels and the corresponding output coordinates preserves their
product probability, as used in [Kitaev, Lemma 8][Kitaev1995]. -/
theorem productKernel_swap {Ω G H : Type*} [Fintype G] [Fintype H]
    (k : Ω → FinDist G) (h : Ω → FinDist H) (V : Ω) (g : G) (z : H) :
    (productKernel k h V).prob (g, z) = (productKernel h k V).prob (z, g) := by
  exact mul_comm _ _

end Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator
