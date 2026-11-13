/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Qatlib.Papers.PartitionFunc08.MainResults.Model.NumericBounds

/-!
# Relative accuracy and product estimates

The event `relAccEvent` and predicate `IsRelAccurate` express multiplicative accuracy and its
probability bound. The structure `SchemeCost` records resource counts, and the product lemmas
show that relative errors of size `ε / (2 * ℓ)` combine into relative error `ε` for positive
factors. These estimates form part of the partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `IsRelAccurate`: The condition that the relative-accuracy event for `Q` has real measure at
  least `p`.
* `prod_rel_acc`: For a nonempty product of positive factors and `0 < ε ≤ 1`, factorwise
  relative errors at most `ε / (2 * ℓ)` give relative error at most `ε` for the product.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Qatlib.Papers.PartitionFunc08.MainResults

/-- The event that `Q` lies between `(1 - ε) * α` and `(1 + ε) * α`. -/
def relAccEvent {Ω : Type*} (α ε : ℝ) (Q : Ω → ℝ) : Set Ω :=
  {ω | (1 - ε) * α ≤ Q ω ∧ Q ω ≤ (1 + ε) * α}

/-- The condition that the relative-accuracy event for `Q` has real measure at least `p`. -/
def IsRelAccurate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (α ε p : ℝ) (Q : Ω → ℝ) : Prop :=
  p ≤ μ.real (relAccEvent α ε Q)

/-- Real-valued resource data recording walk calls and samples for an estimation scheme. -/
structure SchemeCost where

  walkCalls : ℝ

  samples : ℝ

/-- For a nonempty product of positive factors and `0 < ε ≤ 1`, factorwise relative errors at
most `ε / (2 * ℓ)` give a product upper bound of `(1 + ε)` times the target product. -/
theorem prod_upper_rel {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {α Q : Fin ℓ → ℝ} (hα : ∀ i, 0 < α i)
    (hQ : ∀ i, (1 - ε / (2 * (ℓ : ℝ))) * α i ≤ Q i ∧
      Q i ≤ (1 + ε / (2 * (ℓ : ℝ))) * α i) :
    ∏ i, Q i ≤ (1 + ε) * ∏ i, α i := by
  have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hη0 : 0 ≤ ε / (2 * (ℓ : ℝ)) := by positivity
  have hη1 : ε / (2 * (ℓ : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpos : 0 < 1 - ε / (2 * (ℓ : ℝ)) := by linarith
  have hQnonneg : ∀ i ∈ (Finset.univ : Finset (Fin ℓ)), 0 ≤ Q i := by
    intro i _
    have h1 := (hQ i).1
    have h2 := hα i
    nlinarith
  have hprod : 0 ≤ ∏ i, α i := Finset.prod_nonneg (fun i _ => (hα i).le)
  calc ∏ i, Q i
      ≤ ∏ i, (1 + ε / (2 * (ℓ : ℝ))) * α i := by
        refine Finset.prod_le_prod₀ hQnonneg ?_
        intro i _; exact (hQ i).2
    _ = (1 + ε / (2 * (ℓ : ℝ))) ^ ℓ * ∏ i, α i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (1 + ε) * ∏ i, α i := by
        have hpow : (1 + ε / (2 * (ℓ : ℝ))) ^ ℓ ≤ 1 + ε := by
          have h1 := pow_one_add_le_exp (x := ε / (2 * (ℓ : ℝ))) hη0 ℓ
          have h2 : (↑ℓ : ℝ) * (ε / (2 * (ℓ : ℝ))) = ε / 2 := by
            have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
            have h2lne : (2 : ℝ) * (ℓ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hℓpos)
            rw [← mul_div_assoc, div_eq_iff h2lne]
            ring
          rw [h2] at h1
          have h3 : Real.exp (ε / 2) ≤ 1 + ε := by
            have h := exp_le_one_add_two_mul (x := ε / 2) (by linarith) (by linarith)
            linarith
          linarith
        exact mul_le_mul_of_nonneg_right hpow hprod

/-- For a nonempty product of positive factors and `0 < ε ≤ 1`, factorwise relative errors at
most `ε / (2 * ℓ)` give a product lower bound of `(1 - ε)` times the target product. -/
theorem prod_lower_rel {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {α Q : Fin ℓ → ℝ} (hα : ∀ i, 0 < α i)
    (hQ : ∀ i, (1 - ε / (2 * (ℓ : ℝ))) * α i ≤ Q i ∧
      Q i ≤ (1 + ε / (2 * (ℓ : ℝ))) * α i) :
    (1 - ε) * ∏ i, α i ≤ ∏ i, Q i := by
  have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hx1 : ε / (2 * (ℓ : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hη0 : 0 ≤ ε / (2 * (ℓ : ℝ)) := by positivity
  have hbern : 1 - ε ≤ (1 - ε / (2 * (ℓ : ℝ))) ^ ℓ := by
    have h := one_sub_mul_le_pow (x := ε / (2 * (ℓ : ℝ))) hx1 ℓ
    have h2 : (↑ℓ : ℝ) * (ε / (2 * (ℓ : ℝ))) = ε / 2 := by
      have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
      have h2lne : (2 : ℝ) * (ℓ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hℓpos)
      rw [← mul_div_assoc, div_eq_iff h2lne]
      ring
    rw [h2] at h
    linarith
  have hprod : 0 ≤ ∏ i, α i := Finset.prod_nonneg (fun i _ => (hα i).le)
  calc (1 - ε) * ∏ i, α i
      ≤ (1 - ε / (2 * (ℓ : ℝ))) ^ ℓ * ∏ i, α i :=
        mul_le_mul_of_nonneg_right hbern hprod
    _ = ∏ i, (1 - ε / (2 * (ℓ : ℝ))) * α i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, Q i := by
        refine Finset.prod_le_prod₀ ?_ ?_
        · intro i _
          have := hα i
          nlinarith
        · intro i _; exact (hQ i).1

/-- For a nonempty product of positive factors and `0 < ε ≤ 1`, factorwise relative errors at
most `ε / (2 * ℓ)` give relative error at most `ε` for the product. -/
theorem prod_rel_acc {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {α Q : Fin ℓ → ℝ} (hα : ∀ i, 0 < α i)
    (hQ : ∀ i, (1 - ε / (2 * (ℓ : ℝ))) * α i ≤ Q i ∧
      Q i ≤ (1 + ε / (2 * (ℓ : ℝ))) * α i) :
    (1 - ε) * ∏ i, α i ≤ ∏ i, Q i ∧
      ∏ i, Q i ≤ (1 + ε) * ∏ i, α i :=
  ⟨prod_lower_rel hℓ hε0 hε1 hα hQ, prod_upper_rel hℓ hε0 hε1 hα hQ⟩

end Qatlib.Papers.PartitionFunc08.MainResults
