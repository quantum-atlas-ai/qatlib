/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointRefinedDefs
import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointExt
set_option warningAsError false
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical
open Qatlib.Papers.FixedPtSearch14.FixedPoint
open Qatlib.Papers.FixedPtSearch14.FixedPoint

theorem clause1_uniform_word (l : ℕ) (delta bits : ℕ) : UniformWord l delta bits := by
  intro lam
  exact accessWord_realizes_publicWord l delta lam bits

theorem clause2_uniform_access_ledger (l : ℕ) (delta bits : ℕ) :
    UniformAccessLedger l delta bits := by
  refine ⟨prepAccessCount_word l delta bits, queryAccessCount_word l delta bits, ?_, ?_⟩
  · exact phaseAccessCount_word l delta bits
  · exact phaseBitCount_word l delta bits

theorem clause3_consumer_same_success {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    lcuSuccessProb j₀ l delta lam = publicSuccessProb l delta lam :=
  lcu_success_prob_eq_word j₀ l delta lam

theorem clause3_consumer_output_on_target_ray {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    ∃ c : ℂ, lcuConditionalOutput j₀ l delta lam = c • fiberTarget j₀ :=
  lcu_conditional_output_on_target_ray j₀ l delta lam

theorem clause3_zero_good_mass_fails_lcu {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta : ℝ) :
    lcuSuccessProb j₀ l delta 0 = 0 :=
  lcu_zero_good_mass_fails j₀ l delta

end Qatlib.Papers.FixedPtSearch14.FixedPoint
