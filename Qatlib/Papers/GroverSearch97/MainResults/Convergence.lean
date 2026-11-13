/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Qatlib.Concepts.SearchStopping.GroverSuccess.Section2HalfIterationsSubgoalTigh

/-!
# A square root convergence bound for singleton search

For a finite search space with at least three elements, `section4_convergenceBound` produces an
integer Grover iteration count strictly below the square root of the search space cardinality.
The resulting singleton marked success probability is at least one half. See [Grover1997].

## Main statements

* `section4_convergenceBound`: On a finite search space with at least three elements, every
  singleton target reaches success probability at least `1/2` after some `M < sqrt (Fintype.card
  I)` Grover iterations.

## References

* [Grover, 1997][Grover1997]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.GroverSuccess

namespace Qatlib.Papers.GroverSearch97.MainResults.Convergence

/-- On a finite search space with at least three elements, every singleton target reaches
success probability at least `1/2` after some `M < sqrt (Fintype.card I)` Grover iterations. -/
theorem section4_convergenceBound (I : Type*) [Fintype I] [DecidableEq I]
    (hN : 3 ≤ Fintype.card I) (w : I) :
    ∃ M : ℕ, (M : ℝ) < Real.sqrt (Fintype.card I) ∧
      1 / 2 ≤ MeasureProb (GroverState ({w} : Finset I) M) ({w} : Finset I) := by
  have hpos : 0 < Fintype.card I := lt_of_lt_of_le (by norm_num) hN
  have hNpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hpos
  have hNge3 : (3 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card I : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsqrt_gt : (1.65 : ℝ) < Real.sqrt (Fintype.card I : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith [hNge3]
  let s : ℝ := 1 / Real.sqrt (Fintype.card I : ℝ)
  have hs_pos : 0 < s := by dsimp [s]; positivity
  have hs_lt_one : s < 1 := by
    dsimp [s]
    rw [div_lt_one hsqrt_pos]
    linarith
  let θ : ℝ := Real.arcsin s
  have hsinθ : Real.sin θ = s := by
    dsimp [θ]
    exact Real.sin_arcsin (by linarith) (le_of_lt hs_lt_one)
  have hθ0 : 0 < θ := by
    dsimp [θ]
    exact Real.arcsin_pos.mpr hs_pos
  have hθupper : θ < Real.pi / 2 := by
    dsimp [θ]
    exact Real.arcsin_lt_pi_div_two.mpr hs_lt_one
  have hsin2 : (Real.sin θ) ^ 2 = 1 / (Fintype.card I : ℝ) := by
    rw [hsinθ]
    dsimp [s]
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hNpos)]
  obtain ⟨M, hMbudget, hMsuccess⟩ :=
    section2HalfIterationsSubgoal I hpos ({w} : Finset I) θ hθ0 hθupper (by
      simpa using hsin2)
  refine ⟨M, ?_, hMsuccess⟩
  have h1 : 1 / θ < Real.sqrt (Fintype.card I : ℝ) := by
    rw [div_lt_iff₀ hθ0]
    have hθ_gt_s : s < θ := by
      rw [← hsinθ]
      exact Real.sin_lt hθ0
    have hmul := mul_lt_mul_of_pos_left hθ_gt_s hsqrt_pos
    have hval : Real.sqrt (Fintype.card I : ℝ) * s = 1 := by
      dsimp [s]
      field_simp
    rw [hval] at hmul
    exact hmul
  have hstep : Real.pi / (8 * θ) = Real.pi / 8 * (1 / θ) := by ring
  have hbudget_lt : Real.pi / (8 * θ) + 1 < Real.sqrt (Fintype.card I : ℝ) := by
    rw [hstep]
    have hinv_pos : 0 < 1 / θ := by positivity
    have hcoef : Real.pi / 8 < 3.15 / 8 := by linarith [Real.pi_lt_d2]
    have ha : Real.pi / 8 * (1 / θ) < 3.15 / 8 * (1 / θ) :=
      mul_lt_mul_of_pos_right hcoef hinv_pos
    have hb : 3.15 / 8 * (1 / θ) < 3.15 / 8 * Real.sqrt (Fintype.card I : ℝ) :=
      mul_lt_mul_of_pos_left h1 (by norm_num)
    have hnum : 3.15 / 8 * Real.sqrt (Fintype.card I : ℝ) + 1 <
        Real.sqrt (Fintype.card I : ℝ) := by
      have hcoef2 : (1 : ℝ) < 1.65 * (1 - 3.15 / 8) := by norm_num
      have hsq : (1 : ℝ) < Real.sqrt (Fintype.card I : ℝ) * (1 - 3.15 / 8) := by
        have := mul_lt_mul_of_pos_right hsqrt_gt (by norm_num : (0 : ℝ) < 1 - 3.15 / 8)
        linarith
      nlinarith [hsq]
    linarith [ha, hb, hnum]
  calc (M : ℝ) ≤ Real.pi / (8 * θ) + 1 := hMbudget
    _ < Real.sqrt (Fintype.card I) := hbudget_lt

end Qatlib.Papers.GroverSearch97.MainResults.Convergence
