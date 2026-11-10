/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchBoyer96.MainResults

open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.PureStateMath (MeasureProb)

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem success_probability_after_iterations (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) :
    MeasureProb (GroverState A j) A = (Real.sin ((2 * (j : ℝ) + 1) * θ)) ^ 2 :=
  measureProb_groverState hN A θ hθ hs hc j

theorem failure_after_floor_iterations (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (hθpos : 0 < θ)
    (hθhalf : θ ≤ Real.pi / 2) :
    1 - MeasureProb (GroverState A (groverIterations θ)) A ≤
      (A.card : ℝ) / (Fintype.card I : ℝ) := by
  rw [success_probability_after_iterations hN A θ hθ hs hc]
  have hsucc := groverIterations_success hθpos hθhalf
  linarith [hsucc, hθ]

theorem floor_iterations_query_budget {θ t N : ℝ} (hθ : 0 < θ) (hs : 0 < Real.sin θ)
    (ht : 0 < t) (hN : 0 < N) (hsin : Real.sin θ = Real.sqrt (t / N)) :
    (groverIterations θ : ℝ) ≤ Real.pi / 4 * Real.sqrt (N / t) := by
  have hle := groverIterations_le hθ hs
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsqrtt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hdiv : Real.sqrt (N / t) = Real.sqrt N / Real.sqrt t := Real.sqrt_div (le_of_lt hN) t
  have hsin' : Real.sin θ = Real.sqrt t / Real.sqrt N := by
    rw [hsin, Real.sqrt_div (le_of_lt ht)]
  have hswap : Real.pi / (4 * (Real.sqrt t / Real.sqrt N)) =
      Real.pi / 4 * (Real.sqrt N / Real.sqrt t) := by
    field_simp
  rw [hdiv, ← hswap]
  rw [hsin'] at hle
  exact hle

theorem almost_certain_success_within_budget (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hA : 0 < A.card)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : 0 < Real.sin θ) (hc : Real.cos θ ≠ 0) (hθpos : 0 < θ)
    (hθhalf : θ ≤ Real.pi / 2) :
    1 - MeasureProb (GroverState A (groverIterations θ)) A ≤
        (A.card : ℝ) / (Fintype.card I : ℝ) ∧
      (groverIterations θ : ℝ) ≤
        Real.pi / 4 * Real.sqrt ((Fintype.card I : ℝ) / (A.card : ℝ)) := by
  have hsne : Real.sin θ ≠ 0 := ne_of_gt hs
  refine ⟨failure_after_floor_iterations hN A θ hθ hsne hc hθpos hθhalf, ?_⟩
  have hcard : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hN
  have hAcard : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA
  refine floor_iterations_query_budget hθpos hs hAcard hcard ?_
  have hsqrt : Real.sqrt ((A.card : ℝ) / (Fintype.card I : ℝ)) = Real.sin θ := by
    rw [← hθ, Real.sqrt_sq (le_of_lt hs)]
  exact hsqrt.symm

end Qatlib.Papers.QSearchBoyer96.MainResults
