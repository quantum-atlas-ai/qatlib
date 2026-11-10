/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open MeasureTheory
open scoped BigOperators

def toPMF {X : Type*} [Fintype X] (p : FinDist X) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p.prob x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.sum_one]
    simp)

def ofPMF {X : Type*} [Fintype X] (p : PMF X) : FinDist X where
  prob x := (p x).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_one := by
    rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)]
    have h : ∑ x, p x = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [h, ENNReal.toReal_one]

def independent {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FinDist (X i)) : FinDist (∀ i, X i) where
  prob ω := ∏ i, (p i).prob (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => (p i).nonneg (ω i))
  sum_one := by
    simpa only [Fintype.piFinset_univ, (p _).sum_one, Finset.prod_const_one] using
      (Finset.prod_univ_sum (t := fun i => (Finset.univ : Finset (X i)))
        (f := fun i x => (p i).prob x)).symm

def eventMass {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop) [DecidablePred E] : ℝ :=
  ∑ x ∈ Finset.univ.filter E, p.prob x

def relabel {X : Type*} {Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (p : FinDist X) : FinDist Y where
  prob y := p.prob (e.symm y)
  nonneg _ := p.nonneg _
  sum_one := by simpa only [Equiv.sum_comp] using p.sum_one

def weightedSum {I : Type*} [Fintype I] {X : I → Type*}
    (w : I → ℝ) (f : ∀ i, X i → ℝ) (ω : ∀ i, X i) : ℝ := ∑ i, w i * f i (ω i)

end Qatlib.Concepts.ProbabilityCore.Concentration
