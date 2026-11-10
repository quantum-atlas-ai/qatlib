/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.KrausCompile.BornMoments
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open scoped BigOperators

def iidLaw {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (M : ℕ) : FinDist (Fin M → X) where
  prob := p.probOf
  nonneg ω := Finset.prod_nonneg (fun i _ => p.nonneg (ω i))
  sum_one := p.sum_probOf M

def iidPMF {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (M : ℕ) : PMF (Fin M → X) :=
  toPMF (iidLaw p M)

theorem iidPMF_mass {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (M : ℕ) (ω : Fin M → X) :
    (iidPMF p M ω).toReal = ∏ i, p.prob (ω i) := by
  exact ENNReal.toReal_ofReal ((iidLaw p M).nonneg ω)

theorem iid_average_mean {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (M : ℕ) (f : X → ℝ) (hM : 0 < M) :
    (iidLaw p M).expect (FinDist.avg f) = p.expect f := by
  exact p.expect_avg f hM

theorem iid_average_variance {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (M : ℕ) (f : X → ℝ) (hM : 0 < M) :
    (iidLaw p M).variance (FinDist.avg f) = p.variance f / M := by
  change (∑ ω, p.probOf ω *
    (FinDist.avg f ω - (iidLaw p M).expect (FinDist.avg f)) ^ 2) = _
  rw [iid_average_mean p M f hM]
  exact p.expect_avg_sub_sq f hM

end Qatlib.Concepts.KrausCompile.BornMoments
