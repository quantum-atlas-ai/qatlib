/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Conditioned statistics of proportional amplitudes

This module shows that a common nonzero amplitude factor cancels from normalized squared
amplitudes. The theorem `conditioned_statistics_of_proportional` supplies the algebraic step
relating walk output statistics to circuit statistics in [Childs2009].

## Main statements

* `conditioned_statistics_of_proportional`: Proportional amplitude families have identical
  conditioned distributions.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.AmplitudeStatistics

open scoped BigOperators

set_option autoImplicit false

/-- Amplitude families differing by a common nonzero complex factor have the same normalized
squared amplitudes, provided the reference total squared amplitude is nonzero [Childs2009]. -/
theorem conditioned_statistics_of_proportional {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hprop : ∀ s, a s = c * b s)
    (hb : ∑ s, Complex.normSq (b s) ≠ 0) :
    ∀ s, Complex.normSq (a s) / (∑ t, Complex.normSq (a t)) =
      Complex.normSq (b s) / (∑ t, Complex.normSq (b t)) := by
  intro s
  have hc' : Complex.normSq c ≠ 0 := fun h => hc (Complex.normSq_eq_zero.mp h)
  have hsum : (∑ t, Complex.normSq (a t)) =
      Complex.normSq c * (∑ t, Complex.normSq (b t)) := by
    simp only [hprop]
    rw [Finset.sum_congr rfl fun t _ => Complex.normSq_mul c (b t)]
    rw [← Finset.mul_sum]
  rw [hsum, hprop s, Complex.normSq_mul]
  field_simp [hb, hc']

end Qatlib.Papers.UniversalWalk08.MainResults.AmplitudeStatistics
