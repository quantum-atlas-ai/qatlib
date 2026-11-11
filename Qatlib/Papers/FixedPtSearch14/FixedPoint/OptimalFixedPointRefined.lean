/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointRefinedDefs
import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointExt

/-!
# Uniform access-word and consumer guarantees

This module packages uniform matrix realization and exact access counts for the fixed-point
search word of [YoderLowChuang2014]. `clause1_uniform_word` establishes realization for every
real good-mass parameter, and `clause2_uniform_access_ledger` records preparation, query, phase,
and phase-bit counts.

The consumer results identify the lifted LCU success probability with the public word's
probability, place its conditional output in the target span, and prove zero success at zero
good mass.

## Main statements

* `clause1_uniform_word`: uniform matrix realization.
* `clause2_uniform_access_ledger`: exact resource counts.
* `clause3_consumer_same_success`: equality of consumer and word success probabilities.
* `clause3_consumer_output_on_target_ray`: the conditional target direction.
* `clause3_zero_good_mass_fails_lcu`: the zero-mass endpoint.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option warningAsError false
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical
open Qatlib.Papers.FixedPtSearch14.FixedPoint
open Qatlib.Papers.FixedPtSearch14.FixedPoint

/-- The fixed-point access word realizes the public word simultaneously for every real good-mass
parameter. -/
theorem clause1_uniform_word (l : ℕ) (delta bits : ℕ) : UniformWord l delta bits := by
  intro lam
  exact accessWord_realizes_publicWord l delta lam bits

/-- The fixed-point access word has preparation, query, and phase counts `2 * l` and phase-bit
count `2 * l * bits`. -/
theorem clause2_uniform_access_ledger (l : ℕ) (delta bits : ℕ) :
    UniformAccessLedger l delta bits := by
  refine ⟨prepAccessCount_word l delta bits, queryAccessCount_word l delta bits, ?_, ?_⟩
  · exact phaseAccessCount_word l delta bits
  · exact phaseBitCount_word l delta bits

/-- The LCU consumer and the public word have identical success probabilities. -/
theorem clause3_consumer_same_success {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    lcuSuccessProb j₀ l delta lam = publicSuccessProb l delta lam :=
  lcu_success_prob_eq_word j₀ l delta lam

/-- The LCU conditional output lies in the complex span of its fiber target. -/
theorem clause3_consumer_output_on_target_ray {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    ∃ c : ℂ, lcuConditionalOutput j₀ l delta lam = c • fiberTarget j₀ :=
  lcu_conditional_output_on_target_ray j₀ l delta lam

/-- The LCU consumer success probability vanishes at zero good mass. -/
theorem clause3_zero_good_mass_fails_lcu {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta : ℝ) :
    lcuSuccessProb j₀ l delta 0 = 0 :=
  lcu_zero_good_mass_fails j₀ l delta

end Qatlib.Papers.FixedPtSearch14.FixedPoint
