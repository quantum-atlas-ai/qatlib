/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Szegedy walk detection bounds

This module formalizes the walk detection estimate associated with Theorem 4.3 of
[Ambainis2005]. For a symmetric chain with positive gap δ and marked fraction at least ε,
`theorem43_szegedy_walk` bounds a random iteration detection probability and the corresponding
program counts.

## Main statements

* `theorem43_szegedy_walk`: Gives mean detection probability at least 1/32 within an explicit
  inverse square root scale.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Classical
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Matrix

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- For the supplied unitary preparation of a symmetric chain with gap δ and marked fraction at
least ε, constructs a positive iteration range between 1000/√(δε) and 1002/√(δε), with
average detection probability at least 1/32 and the stated linear program count bounds. See
[Ambainis2005]. -/
theorem theorem43_szegedy_walk
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S)
    (hU : U ∈ unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    let L : ℕ := Nat.ceil (1000 / Real.sqrt (δ * ε)) + 1
    0 < L ∧
      (1000 / Real.sqrt (δ * ε) ≤ (L : ℝ)) ∧
      (L : ℝ) ≤ 1002 / Real.sqrt (δ * ε) ∧
      (1 / 32 : ℝ) ≤
        (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ) ∧
      (∀ k : Fin L,
        (detectionCounts (detectionProgram j (k.val + 1))).1 ≤ 4 * L + 1 ∧
        (detectionCounts (detectionProgram j (k.val + 1))).2.1 ≤ 4 * L + 1 ∧
        (detectionCounts (detectionProgram j (k.val + 1))).2.2 ≤ 4 * L + 2) := by
  (try dsimp only)
  set L : ℕ := Nat.ceil (1000 / Real.sqrt (δ * ε)) + 1 with hLdef
  have hδε : 0 < δ * ε := mul_pos hδ hε
  have hsqrtpos : 0 < Real.sqrt (δ * ε) := Real.sqrt_pos.mpr hδε
  have hp01 : markedFraction S ≤ 1 := (markedFraction_mem_Icc S).2
  have hε1 : ε ≤ 1 := le_trans hεp hp01
  have hsqrt1 : Real.sqrt (δ * ε) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact mul_le_one₀ hδ1 (le_of_lt hε) hε1
  have hLpos : 0 < L := by
    unfold L
    omega
  have hscale : 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) := by
    have hc : 1000 / Real.sqrt (δ * ε) ≤
        (Nat.ceil (1000 / Real.sqrt (δ * ε)) : ℝ) := Nat.le_ceil _
    have hlt : (Nat.ceil (1000 / Real.sqrt (δ * ε)) : ℝ) ≤ (L : ℝ) := by
      unfold L
      push_cast
      linarith
    linarith
  have hLle : (L : ℝ) ≤ 1002 / Real.sqrt (δ * ε) := by
    have hceil : (Nat.ceil (1000 / Real.sqrt (δ * ε)) : ℝ) <
        1000 / Real.sqrt (δ * ε) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2le : 2 ≤ 2 / Real.sqrt (δ * ε) := by
      rw [le_div_iff₀ hsqrtpos]
      nlinarith [hsqrt1]
    have hxle : 1000 / Real.sqrt (δ * ε) + 2 ≤ 1002 / Real.sqrt (δ * ε) := by
      have hsplit : 1002 / Real.sqrt (δ * ε) =
          1000 / Real.sqrt (δ * ε) + 2 / Real.sqrt (δ * ε) := by
        rw [← add_div]
        norm_num
      rw [hsplit]
      linarith
    have hLlt : (L : ℝ) < 1000 / Real.sqrt (δ * ε) + 2 := by
      unfold L
      push_cast
      linarith
    linarith
  have hmain := corrected_szegedy_actual_random_power_detection I P S δ ε L j U
    hδ hδ1 hgap hε hεp hLpos hscale hU hp
  exact ⟨hLpos, hscale, hLle, hmain.1, hmain.2⟩

end Qatlib.Papers.QSearchSurvey05.MainResults
