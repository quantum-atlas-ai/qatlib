/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.GoodEvent
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
set_option warningAsError false

theorem expect_ge_on_good {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) [DecidablePred E] (f : X → ℝ)
    (hf0 : ∀x,0≤f x) (a b : ℝ) (ha : 0≤a)
    (hgood : ∀x,E x → a≤f x) (hE : b≤eventMass p E) : a*b≤p.expect f := by
  have hp : a*eventMass p E≤p.expect f := by
    simp only [eventMass,Finset.sum_filter,FinDist.expect,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : E x
    · rw [if_pos hx]
      simpa only [mul_comm a] using! mul_le_mul_of_nonneg_left (hgood x hx) (p.nonneg x)
    · rw [if_neg hx,mul_zero]
      exact mul_nonneg (p.nonneg x) (hf0 x)
  exact (mul_le_mul_of_nonneg_left hE ha).trans hp

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.GoodEvent
