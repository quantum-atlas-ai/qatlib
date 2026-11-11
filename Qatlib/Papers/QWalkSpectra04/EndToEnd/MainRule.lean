/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalStopComparisonQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralDefs
import Qatlib.Concepts.WalkSearch.ProjectorCS

/-!
# Classical and quantum detection scale comparison

This module combines classical detection and corrected random-power quantum detection bounds for
a symmetric chain with gap parameter `δ` and marked fraction at least `ε`. It gives the success
threshold, integer-length estimate, and weighted cost inequalities expressing the square-root
detection scale of [Szegedy2004].

## Main statements

* `source_main_sqrt_de_rule`: combines success lower bounds with classical and quantum length
  scales.
* `source_main_sqrt_de_rule_priced`: bounds the corresponding weighted cost expressions.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.ClassicalStop
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Papers.QWalkSpectra04.EndToEnd.MainRule

/-- For a symmetric chain with `0 < δ ≤ 1`, marked fraction at least positive `ε`, and a
compatible unitary preparation, classical detection at lengths at least `1000 / (δ * ε)` and
the averaged corrected quantum detector both have success at least `1 / 32`. The quantum
averaging length is at most `1000 / √(δ * ε) + 1`, and its real scale does not exceed the
classical one; see [Szegedy2004]. -/
theorem source_main_sqrt_de_rule
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (∀ K : ℕ, 1000 / (δ * ε) ≤ (K : ℝ) → (1 / 32 : ℝ) ≤ classicalDetectSuccess P S K) ∧
    (1 / 32 : ℝ) ≤
      (∑ k : Fin (lemma3Length δ ε),
        detectionProbability U S j (k.val + 1)) / ((lemma3Length δ ε : ℝ)) ∧
    ((lemma3Length δ ε : ℝ) ≤ 1000 / Real.sqrt (δ * ε) + 1) ∧
    (1000 / Real.sqrt (δ * ε) ≤ 1000 / (δ * ε)) := by
  have hde : 0 < δ * ε := mul_pos hδ hε

  have hclass := (szegedyClassicalStopComparison I P S δ ε
    hδ hδ1 hgap hε hεp).2

  have hLb := lemma3Length_bounds δ ε hδ hε
  have hLpos : 0 < lemma3Length δ ε := hLb.1
  have hLge : 1000 / Real.sqrt (δ * ε) ≤ (lemma3Length δ ε : ℝ) := hLb.2.1
  have hLlt : (lemma3Length δ ε : ℝ) < 1000 / Real.sqrt (δ * ε) + 1 := hLb.2.2
  have hquant := (corrected_szegedy_actual_random_power_detection I P S δ ε
    (lemma3Length δ ε) j U hδ hδ1 hgap hε hεp hLpos hLge hU hp).1

  have hfrac_le_one : markedFraction S ≤ 1 := (markedFraction_mem_Icc S).2
  have hε1 : ε ≤ 1 := hεp.trans hfrac_le_one
  have hde1 : δ * ε ≤ 1 := by
    have h2 : δ * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hδ1 hε.le
    have h3 : (1 : ℝ) * ε ≤ 1 * 1 := mul_le_mul_of_nonneg_left hε1 (by norm_num)
    linarith
  have hsqrt_ge : δ * ε ≤ Real.sqrt (δ * ε) := by
    rw [Real.le_sqrt hde.le hde.le]
    calc (δ * ε) ^ 2 = (δ * ε) * (δ * ε) := pow_two (δ * ε)
      _ ≤ (δ * ε) * 1 := mul_le_mul_of_nonneg_left hde1 hde.le
      _ = δ * ε := mul_one _
  have hgain : 1000 / Real.sqrt (δ * ε) ≤ 1000 / (δ * ε) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hde) hde]
    exact mul_le_mul_of_nonneg_left hsqrt_ge (by norm_num)
  exact ⟨hclass, hquant, hLlt.le, hgain⟩

/-- For `0 < δ, ε ≤ 1` and nonnegative step weights, the rounded classical and quantum cost
expressions satisfy the stated affine bounds, and `1000 / √(δ * ε) ≤ 1000 / (δ * ε)`. See
[Szegedy2004]. -/
theorem source_main_sqrt_de_rule_priced
    (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (w0 w1 w2 : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) :
    w0 + (Nat.ceil (1000 / (δ * ε)) : ℝ) * w1 +
        ((Nat.ceil (1000 / (δ * ε)) : ℝ) + 1) * w2 ≤
      w0 + (1000 / (δ * ε) + 1) * w1 + (1000 / (δ * ε) + 2) * w2 ∧
    w0 + (lemma3Length δ ε : ℝ) * (w1 + w2) ≤
      w0 + (1000 / Real.sqrt (δ * ε) + 1) * (w1 + w2) ∧
    1000 / Real.sqrt (δ * ε) ≤ 1000 / (δ * ε) := by
  have hde : 0 < δ * ε := mul_pos hδ hε
  have hKpos : (0 : ℝ) < 1000 / (δ * ε) := div_pos (by norm_num) hde
  have hK : (Nat.ceil (1000 / (δ * ε)) : ℝ) ≤ 1000 / (δ * ε) + 1 :=
    (Nat.ceil_lt_add_one hKpos.le).le
  have hK1 : ((Nat.ceil (1000 / (δ * ε)) : ℝ) + 1) ≤ 1000 / (δ * ε) + 2 := by
    linarith
  have hLb := lemma3Length_bounds δ ε hδ hε
  have hLle : (lemma3Length δ ε : ℝ) ≤ 1000 / Real.sqrt (δ * ε) + 1 := hLb.2.2.le
  have hde1 : δ * ε ≤ 1 := by
    have h2' : δ * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hδ1 hε.le
    have h3 : (1 : ℝ) * ε ≤ 1 * 1 := mul_le_mul_of_nonneg_left hε1 (by norm_num)
    linarith
  have hsqrt_ge : δ * ε ≤ Real.sqrt (δ * ε) := by
    rw [Real.le_sqrt hde.le hde.le]
    calc (δ * ε) ^ 2 = (δ * ε) * (δ * ε) := pow_two (δ * ε)
      _ ≤ (δ * ε) * 1 := mul_le_mul_of_nonneg_left hde1 hde.le
      _ = δ * ε := mul_one _
  refine ⟨?_, ?_, ?_⟩
  · have hw1 := mul_le_mul_of_nonneg_right hK h1
    have hw2 := mul_le_mul_of_nonneg_right hK1 h2
    linarith
  · have hw := mul_le_mul_of_nonneg_right hLle (add_nonneg h1 h2)
    linarith
  · rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hde) hde]
    exact mul_le_mul_of_nonneg_left hsqrt_ge (by norm_num)

end Qatlib.Papers.QWalkSpectra04.EndToEnd.MainRule
