/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs

/-!
# Classical discrimination error and Kolmogorov distance

The scalar identity `two_mul_min_eq` converts the sum of pointwise minima into an
absolute-difference expression. The resulting theorem `proposition2_error_eq_kolmogorov` proves
the classical error formula in Proposition 2 of [FuchsVanDeGraaf1999].

## Main statements

* `proposition2_error_eq_kolmogorov`: equal-prior error is one half minus half the Kolmogorov
  distance.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open scoped BigOperators

variable {X : Type} [Fintype X]

/-- Twice the minimum of two real numbers equals their sum minus the absolute value of their
difference. -/
theorem two_mul_min_eq (a b : ℝ) : 2 * min a b = a + b - |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The equal-prior classical error probability is one half minus half the classical Kolmogorov
distance. This is [Fuchs and van de Graaf, Proposition 2][FuchsVanDeGraaf1999]. -/
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
