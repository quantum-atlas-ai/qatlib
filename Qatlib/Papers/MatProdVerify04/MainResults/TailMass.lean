/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-!
# Tail bounds for revealing samples

`lemma15_tail_mass` bounds the upper tail of a finite random variable taking values in the unit
interval. Finite averaging and rescaling then give `lemma7_full`, which bounds the probability
that a sample reveals at least an eighth of the marked mass. The paper context is
[BuhrmanSpalek2006].

## Main statements

* `lemma15_tail_mass`: tail mass from a lower expectation bound.
* `lemma7_full`: revealing sample bound obtained by finite averaging.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

/-- If `f ≤ 1` pointwise, its expectation is at most `β + (1 - β) * eventMass p (fun x => β ≤ f
x)`. -/
theorem expect_le_tail_of_unit {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) {β : ℝ}
    (hf1 : ∀ x, f x ≤ 1) :
    p.expect f ≤ β + (1 - β) * eventMass p (fun x => β ≤ f x) := by
  classical
  have hsplit : p.expect f
      = (∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x * f x)
        + (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * f x) := by
    rw [FinDist.expect, ← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x => β ≤ f x) (f := fun x => p.prob x * f x)]
  have h1 : (∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x * f x)
      ≤ eventMass p (fun x => β ≤ f x) := by
    have hstep : (∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x * f x)
        ≤ ∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x * 1 := by
      refine Finset.sum_le_sum (fun x _ => ?_)
      exact mul_le_mul_of_nonneg_left (hf1 x) (p.nonneg x)
    have hone : (∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x * 1)
        = eventMass p (fun x => β ≤ f x) :=
      Finset.sum_congr rfl (fun x _ => mul_one _)
    exact hstep.trans hone.le
  have h2 : (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * f x)
      ≤ β * (1 - eventMass p (fun x => β ≤ f x)) := by
    have hstep : (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * f x)
        ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * β := by
      refine Finset.sum_le_sum (fun x hx => ?_)
      exact mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp (Finset.mem_filter.mp hx).2))
        (p.nonneg x)
    have hconst : (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * β)
        = β * (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    have hcompl : (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x)
        = 1 - eventMass p (fun x => β ≤ f x) := by
      have htot := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun x => β ≤ f x) (f := fun x => p.prob x)
      have huniv : (∑ x ∈ Finset.univ, p.prob x) = 1 := p.sum_one
      have hMeq : eventMass p (fun x => β ≤ f x)
          = ∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x := rfl
      linarith
    calc (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * f x)
        ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * β := hstep
      _ = β * (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x) := hconst
      _ = β * (1 - eventMass p (fun x => β ≤ f x)) := by rw [hcompl]
  calc p.expect f
      = (∑ x ∈ Finset.univ.filter (fun x => β ≤ f x), p.prob x * f x)
        + (∑ x ∈ Finset.univ.filter (fun x => ¬ β ≤ f x), p.prob x * f x) := hsplit
    _ ≤ eventMass p (fun x => β ≤ f x)
        + β * (1 - eventMass p (fun x => β ≤ f x)) := add_le_add h1 h2
    _ = β + (1 - β) * eventMass p (fun x => β ≤ f x) := by ring

/-- If `f` takes values in `[0, 1]`, its expectation is at least `α`, and `0 < β < min 1 α`,
then the mass of `β ≤ f` is strictly greater than `α - β`. See [BuhrmanSpalek2006]. -/
theorem lemma15_tail_mass {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) {α β : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hexp : α ≤ p.expect f) (hβ0 : 0 < β) (hβ1 : β < 1) (hβα : β < α) :
    α - β < eventMass p (fun x => β ≤ f x) := by
  classical
  have hlo : 0 ≤ p.expect f := by
    rw [FinDist.expect]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf0 x))
  have hkey := expect_le_tail_of_unit p f (β := β) hf1
  have hpos : 0 < 1 - β := by linarith
  have hposab : 0 < α - β := by linarith
  have hle : α - β ≤ (1 - β) * eventMass p (fun x => β ≤ f x) := by linarith
  have hMge : (α - β) / (1 - β) ≤ eventMass p (fun x => β ≤ f x) := by
    rw [div_le_iff₀ hpos]
    linarith
  have hprod : 0 < (α - β) * β := mul_pos hposab hβ0
  have hstrict : α - β < (α - β) / (1 - β) := by
    rw [lt_div_iff₀ hpos]
    nlinarith
  linarith

/-- If `ζ` takes values in `[0, ε]` for positive `ε` and has expectation at least `ε / 4`, then
`ζ ≥ ε / 8` with probability strictly greater than `1 / 8`. See [BuhrmanSpalek2006]. -/
theorem lemma7_revealing_sample_mass {P : Type*} [Fintype P] [DecidableEq P]
    (law : FinDist P) (ζ : P → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hζ0 : ∀ v, 0 ≤ ζ v) (hζε : ∀ v, ζ v ≤ ε)
    (hexp : ε / 4 ≤ law.expect ζ) :
    (1 : ℝ) / 8 < eventMass law (fun v => ε / 8 ≤ ζ v) := by
  classical
  have hdiv : law.expect (fun v => ζ v / ε) = law.expect ζ / ε := by
    rw [FinDist.expect, FinDist.expect, Finset.sum_div]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hexp' : (1 : ℝ) / 4 ≤ law.expect (fun v => ζ v / ε) := by
    rw [hdiv, le_div_iff₀ hε]
    linarith
  have h0 : ∀ v, 0 ≤ ζ v / ε := fun v => div_nonneg (hζ0 v) hε.le
  have h1 : ∀ v, ζ v / ε ≤ 1 := fun v => (div_le_one hε).mpr (hζε v)
  have hmain := lemma15_tail_mass law (fun v => ζ v / ε) h0 h1 hexp'
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  have hiff : ∀ v, ((1 : ℝ) / 8 ≤ ζ v / ε) ↔ (ε / 8 ≤ ζ v) := by
    intro v
    rw [le_div_iff₀ hε]
    constructor <;> intro h <;> linarith
  have hevent : eventMass law (fun v => (1 : ℝ) / 8 ≤ ζ v / ε)
      = eventMass law (fun v => ε / 8 ≤ ζ v) := by
    show (∑ x ∈ Finset.univ.filter (fun v => (1 : ℝ) / 8 ≤ ζ v / ε), law.prob x)
        = ∑ x ∈ Finset.univ.filter (fun v => ε / 8 ≤ ζ v), law.prob x
    exact Finset.sum_congr (Finset.filter_congr (fun x _ => hiff x)) (fun _ _ => rfl)
  rw [hevent] at hmain
  linarith

/-- Expresses event mass as the expectation of the event's real indicator. -/
theorem eventMass_ite {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop)
    [DecidablePred E] :
    eventMass p E = ∑ x, p.prob x * (if E x then (1 : ℝ) else 0) := by
  classical
  unfold eventMass
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun x _ => by by_cases h : E x <;> simp [h])

/-- If every marked index is revealed with probability at least one quarter, then the expected
revealed mass is at least one quarter of the marked mass. See [BuhrmanSpalek2006]. -/
theorem lemma7_zeta_average {P J : Type*} [Fintype P] [DecidableEq P]
    [Fintype J] [DecidableEq J]
    (lawP : FinDist P) (lawJ : FinDist J)
    (reveal : P → J → Prop) [DecidableRel reveal]
    (marked : J → Prop) [DecidablePred marked]
    (hpair : ∀ j, marked j → (1 / 4 : ℝ) ≤ eventMass lawP (fun v => reveal v j)) :
    (1 / 4 : ℝ) * eventMass lawJ marked
      ≤ lawP.expect (fun v => ∑ j, lawJ.prob j * (if reveal v j then (1 : ℝ) else 0)) := by
  classical
  have hrewrite : lawP.expect (fun v => ∑ j, lawJ.prob j * (if reveal v j then (1 : ℝ) else 0))
      = ∑ j, lawJ.prob j * eventMass lawP (fun v => reveal v j) := by
    rw [FinDist.expect]
    calc ∑ v, lawP.prob v * ∑ j, lawJ.prob j * (if reveal v j then (1 : ℝ) else 0)
        = ∑ v, ∑ j, lawP.prob v * (lawJ.prob j * (if reveal v j then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl (fun v _ => ?_)
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ v, lawP.prob v * (lawJ.prob j * (if reveal v j then (1 : ℝ) else 0)) :=
            Finset.sum_comm
      _ = ∑ j, lawJ.prob j * ∑ v, lawP.prob v * (if reveal v j then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = ∑ j, lawJ.prob j * eventMass lawP (fun v => reveal v j) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [eventMass_ite]
  rw [hrewrite]
  have hnonneg : ∀ j, 0 ≤ eventMass lawP (fun v => reveal v j) :=
    fun j => Finset.sum_nonneg (fun v _ => lawP.nonneg v)
  have hstep : ∑ j, lawJ.prob j * (if marked j then (1 / 4 : ℝ) else 0)
      ≤ ∑ j, lawJ.prob j * eventMass lawP (fun v => reveal v j) := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases h : marked j
    · rw [if_pos h]
      exact mul_le_mul_of_nonneg_left (hpair j h) (lawJ.nonneg j)
    · rw [if_neg h, mul_zero]
      exact mul_nonneg (lawJ.nonneg j) (hnonneg j)
  have hleft : (1 / 4 : ℝ) * eventMass lawJ marked
      = ∑ j, lawJ.prob j * (if marked j then (1 / 4 : ℝ) else 0) := by
    unfold eventMass
    rw [Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun j _ => by by_cases h : marked j <;> simp [h, mul_comm])
  rw [hleft]
  exact hstep

/-- If revealing implies being marked and each marked index is revealed with probability at
least one quarter, then a sample reveals at least `ε / 8` mass with probability strictly
greater than `1 / 8`, where `ε > 0` is the marked mass. See [BuhrmanSpalek2006]. -/
theorem lemma7_full {P J : Type*} [Fintype P] [DecidableEq P]
    [Fintype J] [DecidableEq J]
    (lawP : FinDist P) (lawJ : FinDist J)
    (reveal : P → J → Prop) [DecidableRel reveal]
    (marked : J → Prop) [DecidablePred marked]
    (hrevmark : ∀ v j, reveal v j → marked j)
    {ε : ℝ} (hε : 0 < ε) (hεdef : ε = eventMass lawJ marked)
    (hpair : ∀ j, marked j → (1 / 4 : ℝ) ≤ eventMass lawP (fun v => reveal v j)) :
    (1 : ℝ) / 8 < eventMass lawP
      (fun v => ε / 8 ≤ ∑ j, lawJ.prob j * (if reveal v j then (1 : ℝ) else 0)) := by
  classical
  set ζ : P → ℝ := fun v => ∑ j, lawJ.prob j * (if reveal v j then (1 : ℝ) else 0) with hζ
  have hζ0 : ∀ v, 0 ≤ ζ v :=
    fun v => Finset.sum_nonneg (fun j _ => mul_nonneg (lawJ.nonneg j) (by split <;> norm_num))
  have hζε : ∀ v, ζ v ≤ ε := by
    intro v
    rw [hεdef]
    have hle : ζ v ≤ ∑ j, lawJ.prob j * (if marked j then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hpt : (if reveal v j then (1 : ℝ) else 0) ≤ (if marked j then (1 : ℝ) else 0) := by
        by_cases hr : reveal v j
        · rw [if_pos hr, if_pos (hrevmark v j hr)]
        · rw [if_neg hr]
          by_cases hm : marked j <;> simp [hm]
      exact mul_le_mul_of_nonneg_left hpt (lawJ.nonneg j)
    have heq : ∑ j, lawJ.prob j * (if marked j then (1 : ℝ) else 0)
        = eventMass lawJ marked := by
      unfold eventMass
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun j _ => by by_cases h : marked j <;> simp [h])
    rw [heq] at hle
    exact hle
  have havg := lemma7_zeta_average lawP lawJ reveal marked hpair
  have hexp : ε / 4 ≤ lawP.expect ζ := by
    rw [hεdef]
    have havg' : (1 / 4 : ℝ) * eventMass lawJ marked ≤ lawP.expect ζ := by
      rwa [hζ]
    linarith
  have hdiv : lawP.expect (fun v => ζ v / ε) = lawP.expect ζ / ε := by
    rw [FinDist.expect, FinDist.expect, Finset.sum_div]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hexp' : (1 : ℝ) / 4 ≤ lawP.expect (fun v => ζ v / ε) := by
    rw [hdiv, le_div_iff₀ hε]
    linarith
  have h0 : ∀ v, 0 ≤ ζ v / ε := fun v => div_nonneg (hζ0 v) hε.le
  have h1 : ∀ v, ζ v / ε ≤ 1 := fun v => (div_le_one hε).mpr (hζε v)
  have hmain := lemma15_tail_mass lawP (fun v => ζ v / ε) h0 h1 hexp'
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  have hiff : ∀ v, ((1 : ℝ) / 8 ≤ ζ v / ε) ↔ (ε / 8 ≤ ζ v) := by
    intro v
    rw [le_div_iff₀ hε]
    constructor <;> intro h <;> linarith
  have hevent : eventMass lawP (fun v => (1 : ℝ) / 8 ≤ ζ v / ε)
      = eventMass lawP (fun v => ε / 8 ≤ ζ v) := by
    show (∑ x ∈ Finset.univ.filter (fun v => (1 : ℝ) / 8 ≤ ζ v / ε), lawP.prob x)
        = ∑ x ∈ Finset.univ.filter (fun v => ε / 8 ≤ ζ v), lawP.prob x
    exact Finset.sum_congr (Finset.filter_congr (fun x _ => hiff x)) (fun _ _ => rfl)
  rw [hevent] at hmain
  linarith

end Qatlib.Papers.MatProdVerify04.MainResults
