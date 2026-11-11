/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Acceptance weights and posterior budgets

This module bounds acceptance for a finite joint law on records and a Boolean outcome.
`acceptance` controls total accepted mass and bad accepted mass; `posterior_budget` normalizes
the accepted weights and bounds their bad record contribution. These elementary conditioning
estimates support the instrument framework of [Watrous2018].

## Main statements

* `acceptance`: acceptance at least `1 - ζ - δ` and bad accepted mass at most `ζ`.
* `posterior_budget`: a normalized posterior with bad mass at most `ζ / (1 - ζ - δ)`.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordWeights
open scoped Classical BigOperators

variable {R : Type} [Fintype R] [DecidableEq R]

/-- For a normalized nonnegative joint law, total bad record mass at most `ζ` and good record
rejection fraction at most `δ` imply accepted mass at least `1 - ζ - δ` and bad accepted
mass at most `ζ`. -/
theorem acceptance (q : R × Bool → ℝ) (hq : ∀ z, 0 ≤ q z) (hs : ∑ z, q z=1)
    (good : Finset R) (ζ δ : ℝ) (hδ : 0 ≤ δ)
    (hbad : (∑ r : R, if r ∈ good then 0 else q (r,true)+q (r,false)) ≤ ζ)
    (hfail : ∀ r ∈ good, q (r,false) ≤ δ*(q (r,true)+q (r,false))) :
    1-ζ-δ ≤ ∑ r : R, q (r,true) ∧
      (∑ r : R, if r ∈ good then 0 else q (r,true)) ≤ ζ := by
  have hf : (∑ r : R, q (r,false)) ≤
      (∑ r : R, if r ∈ good then 0 else q (r,true)+q (r,false))+
        δ*(∑ r : R, (q (r,true)+q (r,false))) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : r ∈ good
    · simpa only [if_pos hr,zero_add] using hfail r hr
    · rw [if_neg hr]
      have hn := mul_nonneg hδ (add_nonneg (hq (r,true)) (hq (r,false)))
      linarith [hq (r,true)]
  have hp : (∑ r : R, q (r,true))+(∑ r : R, q (r,false))=1 := by
    simpa only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib] using hs
  have hrow : (∑ r : R, (q (r,true)+q (r,false)))=1 := by
    rw [Finset.sum_add_distrib,hp]
  rw [hrow,mul_one] at hf
  refine ⟨by linarith,?_⟩
  apply le_trans _ hbad
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : r ∈ good <;> simp [hr]
  linarith [hq (r,false)]

/-- When `ζ` and `δ` are nonnegative with `ζ + δ < 1`, the accepted mass is positive, the
accepted posterior sums to one, and its bad record mass is at most `ζ / (1 - ζ - δ)` under
the stated mass bounds. -/
theorem posterior_budget (q : R × Bool → ℝ) (hq : ∀ z, 0 ≤ q z) (hs : ∑ z, q z=1)
    (good : Finset R) (ζ δ : ℝ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ) (hsmall : ζ+δ < 1)
    (hbad : (∑ r : R, if r ∈ good then 0 else q (r,true)+q (r,false)) ≤ ζ)
    (hfail : ∀ r ∈ good, q (r,false) ≤ δ*(q (r,true)+q (r,false))) :
    let S := ∑ r : R, q (r,true)
    0 < S ∧ (∑ r : R, q (r,true)/S)=1 ∧
      (∑ r : R, if r ∈ good then 0 else q (r,true)/S) ≤ ζ/(1-ζ-δ) := by
  dsimp only
  obtain ⟨hS,hB⟩ :=
      Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordWeights.acceptance q hq hs good ζ δ hδ hbad hfail
  have hl : 0 < 1-ζ-δ := by linarith
  have hp : 0 < ∑ r : R, q (r,true) := hl.trans_le hS
  refine ⟨hp,?_,?_⟩
  · rw [← Finset.sum_div,div_self hp.ne']
  · have he : (∑ r : R, if r ∈ good then 0 else q (r,true)/(∑ r : R, q (r,true)))=
        (∑ r : R, if r ∈ good then 0 else q (r,true))/(∑ r : R, q (r,true)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
    rw [he]
    exact (div_le_div_of_nonneg_right hB hp.le).trans
      (div_le_div_of_nonneg_left hζ hl hS)

end Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordWeights
