/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open scoped BigOperators

variable {X : Type} [Fintype X]

theorem two_mul_min_eq (a b : ℝ) : 2 * min a b = a + b - |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem proposition2_error_eq_kolmogorov (p0 p1 : FinDist X) :
    classicalErrProb p0 p1 = 1 / 2 - classicalKolmogorov p0 p1 / 2 := by
  have hsum : (∑ x, min (p0.prob x) (p1.prob x)) =
      (2 - ∑ x, |p0.prob x - p1.prob x|) / 2 := by
    rw [show (∑ x, min (p0.prob x) (p1.prob x)) =
        ∑ x, (p0.prob x + p1.prob x - |p0.prob x - p1.prob x|) / 2 from
      Finset.sum_congr rfl fun x _ => by
        rw [← two_mul_min_eq]; ring]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      p0.sum_one, p1.sum_one]
    ring
  unfold classicalErrProb classicalKolmogorov
  rw [hsum, tv]
  ring

end Qatlib.Papers.CryptoDisting99.Equivalence
