/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplification

/-!
# Stage weights for variable-time amplification

`VtStage` records the weights, angle, and odd call multiplier of an amplification stage.
`VtStageChain` packages the gain windows, trigonometric identities, and time recurrence used to
bound amplified weights and square-root gain ratios.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `VtStageChain.ampWindow`: lower bound on the amplified weight in terms of the ideal gain.
* `VtStageChain.ampFloor` and `VtStageChain.ampCap`: stage weight bounds.
* `VtStageChain.gainRatio_le_oddCalls`: comparison of gain and call count.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

open Matrix Qatlib
open scoped Classical BigOperators

/-- The absolute sine of `n * θ` is at most `n` times the absolute sine of `θ`. -/
theorem abs_sin_nsmul_le (n : ℕ) (θ : ℝ) :
    |Real.sin ((n : ℝ) * θ)| ≤ (n : ℝ) * |Real.sin θ| := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_mul, Real.sin_add]
      simp only [one_mul]
      calc |Real.sin ((n : ℝ) * θ) * Real.cos θ + Real.cos ((n : ℝ) * θ) * Real.sin θ|
          ≤ |Real.sin ((n : ℝ) * θ) * Real.cos θ| + |Real.cos ((n : ℝ) * θ) * Real.sin θ| :=
          abs_add_le _ _
        _ ≤ |Real.sin ((n : ℝ) * θ)| + |Real.sin θ| := by
          have h1 : |Real.sin ((n : ℝ) * θ) * Real.cos θ|
              = |Real.sin ((n : ℝ) * θ)| * |Real.cos θ| := abs_mul _ _
          have h2 : |Real.cos ((n : ℝ) * θ) * Real.sin θ|
              = |Real.cos ((n : ℝ) * θ)| * |Real.sin θ| := abs_mul _ _
          have hc1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one _
          have hc2 : |Real.cos ((n : ℝ) * θ)| ≤ 1 := Real.abs_cos_le_one _
          have m1 : 0 ≤ |Real.sin ((n : ℝ) * θ)| := abs_nonneg _
          have m2 : 0 ≤ |Real.sin θ| := abs_nonneg _
          rw [h1, h2]
          have e1 : |Real.sin ((n : ℝ) * θ)| * |Real.cos θ| ≤ |Real.sin ((n : ℝ) * θ)| * 1 :=
            mul_le_mul_of_nonneg_left hc1 m1
          have e2 : |Real.cos ((n : ℝ) * θ)| * |Real.sin θ| ≤ 1 * |Real.sin θ| :=
            mul_le_mul_of_nonneg_right hc2 m2
          linarith
        _ ≤ (n : ℝ) * |Real.sin θ| + |Real.sin θ| := by
          have := ih
          linarith
        _ = ((n : ℝ) + 1) * |Real.sin θ| := by ring

/-- The squared sine of `n * θ` is at most `n²` times the squared sine of `θ`. -/
theorem sin_sq_le_nsmul_sq (n : ℕ) (θ : ℝ) :
    Real.sin ((n : ℝ) * θ) ^ 2 ≤ (n : ℝ) ^ 2 * Real.sin θ ^ 2 := by
  have h := abs_sin_nsmul_le n θ
  have hsq : |Real.sin ((n : ℝ) * θ)| * |Real.sin ((n : ℝ) * θ)|
      ≤ ((n : ℝ) * |Real.sin θ|) * ((n : ℝ) * |Real.sin θ|) :=
    mul_self_le_mul_self (abs_nonneg _) h
  have hlhs : |Real.sin ((n : ℝ) * θ)| * |Real.sin ((n : ℝ) * θ)|
      = Real.sin ((n : ℝ) * θ) ^ 2 := by rw [← sq, sq_abs]
  have hrhs : ((n : ℝ) * |Real.sin θ|) * ((n : ℝ) * |Real.sin θ|)
      = (n : ℝ) ^ 2 * Real.sin θ ^ 2 := by
    calc ((n : ℝ) * |Real.sin θ|) * ((n : ℝ) * |Real.sin θ|)
        = (n : ℝ) * ((n : ℝ) * (|Real.sin θ| * |Real.sin θ|)) := by ring
      _ = (n : ℝ) * ((n : ℝ) * Real.sin θ ^ 2) := by rw [← sq, sq_abs]
      _ = (n : ℝ) ^ 2 * Real.sin θ ^ 2 := by ring
  rw [hlhs, hrhs] at hsq
  exact hsq

/-- For nonnegative `x`, the square root of `1 + x` is at most `1 + √x`. -/
theorem sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
  have hnonneg : 0 ≤ 1 + Real.sqrt x := by positivity
  have hrhs : 0 ≤ 1 + x := by linarith
  have hsq : 1 + x ≤ (1 + Real.sqrt x) ^ 2 := by
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have h2 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have h := (Real.sqrt_le_sqrt_iff (by positivity : 0 ≤ (1 + Real.sqrt x) ^ 2)).2 hsq
  rwa [Real.sqrt_sq hnonneg] at h

/-- A finite product of square roots of nonnegative real numbers equals the square root of their
product. -/
theorem prod_sqrt (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a ∈ s, Real.sqrt (f a)) = Real.sqrt (∏ a ∈ s, f a) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ b ∈ s, 0 ≤ f b := fun b hb => hf b (Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih hfs, Real.sqrt_mul hfa]

/-- Distinguishes a base stage from an amplified stage. -/
inductive VtStageKind

  | base

  | amplified

/-- Records a stage kind, base and amplified weights, an amplification angle, and the natural
parameter of an odd call multiplier. -/
structure VtStage where

  kind : VtStageKind

  baseWeight : ℝ

  ampWeight : ℝ

  oddMultiplier : ℕ

  angle : ℝ

/-- The natural call multiplier `2 * s.oddMultiplier + 1` of a stage. -/
def VtStage.oddCallsNat (s : VtStage) : ℕ := 2 * s.oddMultiplier + 1

/-- The real-valued odd call multiplier `2 * s.oddMultiplier + 1` of a stage. -/
def VtStage.oddCalls (s : VtStage) : ℝ := ((2 * s.oddMultiplier + 1 : ℕ) : ℝ)

/-- A sequence of stage data with gain bounds, amplification identities, a time recurrence, and
positivity and comparison conditions for success weights. -/
structure VtStageChain (m : ℕ) where

  stage : ℕ → VtStage

  stopMass : ℕ → ℝ

  stopMassNonneg : ∀ j, 0 ≤ stopMass j

  psucc : ℝ

  psuccUpTo : ℕ → ℝ

  time : ℕ → ℝ

  gainFloor : ∀ j, 1 ≤ j → j ≤ m →
    1 / (9 * (m : ℝ) * (1 - 1 / (3 * (m : ℝ)))) ≤
      (stage j).oddCalls ^ 2 * (stage j).baseWeight

  gainCap : ∀ j, 1 ≤ j → j ≤ m →
    (stage j).oddCalls ^ 2 * (stage j).baseWeight ≤ 1 / (m : ℝ)

  angleWindow : ∀ j, 1 ≤ j → j ≤ m →
    0 ≤ (stage j).angle ∧ (stage j).angle ≤ Real.pi / 2 ∧
      (stage j).oddCalls * (stage j).angle ≤ Real.pi / 2

  ampIdentity : ∀ j, 1 ≤ j → j ≤ m →
    (stage j).ampWeight = Real.sin ((stage j).oddCalls * (stage j).angle) ^ 2 ∧
      (stage j).baseWeight = Real.sin (stage j).angle ^ 2

  timeRec : ∀ i, 1 ≤ i → i ≤ m →
    time i = (stage i).oddCalls * (time (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))

  timeZero : 0 ≤ time 0

  psuccUpToPos : ∀ i, 1 ≤ i → i ≤ m → 0 < psuccUpTo i

  psuccUpTo_le : ∀ i, 1 ≤ i → i ≤ m → psuccUpTo i ≤ psucc

  psuccPos : 0 < psucc

/-- For `m ≥ 1`, the amplification loss factor `1 - 1 / (3 * m)` is positive. -/
theorem one_sub_inv_three_mul_pos (m : ℕ) (hm : 1 ≤ m) : 0 < 1 - 1 / (3 * (m : ℝ)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmm : (0 : ℝ) < m := by linarith
  have h3m : 0 < 3 * (m : ℝ) := by positivity
  have heq : (1 : ℝ) - 1 / (3 * (m : ℝ)) = (3 * (m : ℝ) - 1) / (3 * (m : ℝ)) := by field_simp
  rw [heq]
  exact div_pos (by linarith) (by positivity)

/-- Every stage with index between `1` and `m` has positive base weight. -/
theorem VtStageChain.baseWeight_pos {m : ℕ} (chain : VtStageChain m) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ m) : 0 < (chain.stage j).baseWeight := by
  have hf := chain.gainFloor j h1 h2
  have h1m : 1 ≤ m := Nat.le_trans h1 h2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast h1m
  have hmm : (0 : ℝ) < m := by linarith
  have hα := one_sub_inv_three_mul_pos m h1m
  have hden : 0 < 9 * (m : ℝ) * (1 - 1 / (3 * (m : ℝ))) :=
    mul_pos (mul_pos (by norm_num) hmm) hα
  have hnum : 0 < 1 / (9 * (m : ℝ) * (1 - 1 / (3 * (m : ℝ)))) := by positivity
  have hmul : 0 < (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight :=
    lt_of_lt_of_le hnum hf
  have hsqpos : 0 < (chain.stage j).oddCalls ^ 2 := by
    have : 0 < (chain.stage j).oddCalls := by
      unfold VtStage.oddCalls
      positivity
    positivity
  exact (mul_pos_iff_of_pos_left hsqpos).1 hmul

/-- For `m ≥ 1`, the amplified weight is at least the ideal odd-multiplier gain times `1 - 1 /
(3 * m)`. -/
theorem VtStageChain.ampWindow {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ m) :
    (1 - 1 / (3 * (m : ℝ))) * (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight
      ≤ (chain.stage j).ampWeight := by
  have hw := chain.angleWindow j h1 h2
  have hid := chain.ampIdentity j h1 h2
  have hn : (2 * (chain.stage j).oddMultiplier + 1 : ℕ) = 2 * (chain.stage j).oddMultiplier + 1 :=
      rfl
  have hsq := clause88_tight_sin_sq (2 * (chain.stage j).oddMultiplier + 1) (chain.stage j).angle
    hw.1 hw.2.1 hw.2.2
  have hid' : Real.sin ((chain.stage j).oddCalls * (chain.stage j).angle) ^ 2
      = (chain.stage j).ampWeight := hid.1.symm
  have hbase : Real.sin (chain.stage j).angle ^ 2 = (chain.stage j).baseWeight := hid.2.symm
  have hloss : (1 - (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight / 3)
      * ((chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight)
        ≤ (chain.stage j).ampWeight := by
    have hcast : ((2 * (chain.stage j).oddMultiplier + 1 : ℕ) : ℝ)
        = (chain.stage j).oddCalls := rfl
    rw [hcast] at hsq
    rw [← hid']
    have hgain : (chain.stage j).oddCalls ^ 2 * Real.sin (chain.stage j).angle ^ 2
        = (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight := by rw [hbase]
    rw [hgain] at hsq
    exact hsq
  have hcap := chain.gainCap j h1 h2
  have hnonneg : 0 ≤ (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight :=
    mul_nonneg (sq_nonneg _) (le_of_lt (chain.baseWeight_pos h1 h2))
  have hα := one_sub_inv_three_mul_pos m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega))
  have hcap' : (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight / 3
      ≤ 1 / (3 * (m : ℝ)) := by
    calc (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight / 3
        ≤ (1 / (m : ℝ)) / 3 := div_le_div_of_nonneg_right hcap (by norm_num)
      _ = 1 / (3 * (m : ℝ)) := by field_simp
  have hα' : 1 - 1 / (3 * (m : ℝ))
      ≤ 1 - (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight / 3 := by linarith
  calc (1 - 1 / (3 * (m : ℝ))) * (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight
      ≤ (1 - (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight / 3)
          * ((chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight) := by
        have hcore : (1 - 1 / (3 * (m : ℝ))) * (chain.stage j).oddCalls ^ 2
            ≤ (1 - (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight / 3)
              * (chain.stage j).oddCalls ^ 2 :=
          mul_le_mul_of_nonneg_right hα' (by positivity)
        have hfull := mul_le_mul_of_nonneg_right hcore
          (le_of_lt (chain.baseWeight_pos h1 h2))
        convert! hfull using 1
        all_goals ring
    _ ≤ (chain.stage j).ampWeight := hloss

/-- The amplified weight is at most the squared odd call multiplier times the base weight. -/
theorem VtStageChain.amp_le_gain {m : ℕ} (chain : VtStageChain m) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ m) :
    (chain.stage j).ampWeight ≤ (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight := by
  have hid := chain.ampIdentity j h1 h2
  have hgain := sin_sq_le_nsmul_sq (2 * (chain.stage j).oddMultiplier + 1) (chain.stage j).angle
  have hbase : Real.sin (chain.stage j).angle ^ 2 = (chain.stage j).baseWeight := hid.2.symm
  have hcast : ((2 * (chain.stage j).oddMultiplier + 1 : ℕ) : ℝ)
      = (chain.stage j).oddCalls := rfl
  calc (chain.stage j).ampWeight = Real.sin ((chain.stage j).oddCalls * (chain.stage j).angle) ^ 2 := hid.1
    _ ≤ (chain.stage j).oddCalls ^ 2 * Real.sin (chain.stage j).angle ^ 2 := by
      rw [hcast] at hgain
      exact hgain
    _ = (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight := by rw [hbase]

/-- For `m ≥ 1`, each stage with index between `1` and `m` has amplified weight at least `1 / (9
* m)`. -/
theorem VtStageChain.ampFloor {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ m) : 1 / (9 * (m : ℝ)) ≤ (chain.stage j).ampWeight := by
  have hf := chain.gainFloor j h1 h2
  have hw := chain.ampWindow hm h1 h2
  have hα := one_sub_inv_three_mul_pos m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmm : (0 : ℝ) < m := by linarith
  have hden : 0 < 9 * (m : ℝ) * (1 - 1 / (3 * (m : ℝ))) :=
    mul_pos (mul_pos (by norm_num) hmm) hα
  have hnum : 0 < 1 / (9 * (m : ℝ) * (1 - 1 / (3 * (m : ℝ)))) := by positivity
  have hdiv : (1 / (9 * (m : ℝ))) / (1 - 1 / (3 * (m : ℝ)))
      = 1 / (9 * (m : ℝ) * (1 - 1 / (3 * (m : ℝ)))) := by field_simp
  have hq : (1 / (9 * (m : ℝ))) / (1 - 1 / (3 * (m : ℝ)))
      ≤ (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight := by
    rw [hdiv]
    exact hf
  have hmul := (div_le_iff₀ hα).1 hq
  have hkey : 1 / (9 * (m : ℝ)) ≤ (1 - 1 / (3 * (m : ℝ))) * (chain.stage j).oddCalls ^ 2
      * (chain.stage j).baseWeight := by
    convert! hmul using 1
    all_goals ring
  linarith

/-- Each stage with index between `1` and `m` has amplified weight at most `1 / m`. -/
theorem VtStageChain.ampCap {m : ℕ} (chain : VtStageChain m) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ m) : (chain.stage j).ampWeight ≤ 1 / (m : ℝ) := by
  have hgain := chain.amp_le_gain h1 h2
  have hcap := chain.gainCap j h1 h2
  linarith

/-- The square-root gain ratio of a stage is at most its odd call multiplier. -/
theorem VtStageChain.gainRatio_le_oddCalls {m : ℕ} (chain : VtStageChain m) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ m) :
    gainRatio (chain.stage j).ampWeight (chain.stage j).baseWeight
      ≤ (chain.stage j).oddCalls := by
  have hbase : 0 < (chain.stage j).baseWeight := chain.baseWeight_pos h1 h2
  have hgain := chain.amp_le_gain h1 h2
  have hodd : 0 ≤ (chain.stage j).oddCalls := by
    unfold VtStage.oddCalls
    positivity
  have hnn : 0 ≤ (chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight :=
    mul_nonneg (sq_nonneg _) (le_of_lt hbase)
  have hroot : Real.sqrt ((chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight)
      = (chain.stage j).oddCalls * Real.sqrt (chain.stage j).baseWeight := by
    rw [Real.sqrt_mul' ((chain.stage j).oddCalls ^ 2) (le_of_lt hbase)]
    rw [Real.sqrt_sq (by linarith)]
  have h1 : Real.sqrt (chain.stage j).ampWeight
      ≤ Real.sqrt ((chain.stage j).oddCalls ^ 2 * (chain.stage j).baseWeight) :=
    (Real.sqrt_le_sqrt_iff hnn).2 hgain
  rw [hroot] at h1
  unfold gainRatio
  rw [div_le_iff₀ (Real.sqrt_pos.2 hbase)]
  exact h1

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem
