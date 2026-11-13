/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundStat
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundAux

/-!
# Average stopping-time tail estimate

This module proves `AverageStopTailBound` by telescoping stopping increments and estimating a
dyadically weighted sum of square roots of running masses. The result supplies a tail estimate
used in variable-time amplification.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `averageStopTailBound_answer`: proof of the stopping-tail contract.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

noncomputable section
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical BigOperators

/-- Complete, supported growing-history runs satisfy the tail identity and the weighted
running-mass bound in `AverageStopTailBound`, supporting the estimates associated with
[Ambainis2012]. -/
theorem averageStopTailBound_answer : AverageStopTailBound := by
  intro C _ _ stages history hl j₀ _hj hs hstop
  have hm : reachedStoppedMass stages history (Ket j₀) stages.length = 1 := by
    have he := growing_running_mass_complement stages history hl j₀ hs stages.length le_rfl
    rw [hstop] at he
    linarith
  have htail (i : ℕ) (hi : i ≤ stages.length) :
      MeasureProb (vtState stages i (Ket j₀)) (runningSet C) =
        ∑ j ∈ Finset.range stages.length, if i ≤ j then reachedPstop stages history (Ket j₀) j else 0 := by
    rw [growing_running_mass_complement stages history hl j₀ hs i hi]
    simp only [reachedPstop]
    rw [finite_stop_tail_telescopes _ _ i hi, hm]
  refine ⟨htail, ?_⟩
  let f (i : ℕ) := (2 : ℝ)^i *
    Real.sqrt (MeasureProb (vtState stages i (Ket j₀)) (runningSet C))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range stages.length) (fun _ => (1 : ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  change (∑ i ∈ Finset.range stages.length, (f i)^2) ≤
    ∑ j ∈ Finset.range stages.length, reachedPstop stages history (Ket j₀) j*(stopTime j)^2
  have he : (∑ i ∈ Finset.range stages.length, (f i)^2) =
      ∑ i ∈ Finset.range stages.length, ((2 : ℝ)^i)^2 *
        (∑ j ∈ Finset.range stages.length, if i ≤ j then reachedPstop stages history (Ket j₀) j else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt (measureProb_nonneg _ _), htail i (Finset.mem_range.mp hi).le]
  rw [he]
  exact stopping_tail_weighted_sum _ _ (fun j hj => reached_pstop_nonneg stages history hl _ j hj)

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
