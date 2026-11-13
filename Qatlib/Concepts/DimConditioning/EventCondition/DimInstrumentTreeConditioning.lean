/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DimInstruments.DimTreeExec.DimInstrumentTreeExecution

/-!
# Event conditioning for dimension changing instrument trees

This module proves positivity, probability bounds, and zero mass semantics for record events of
a dimension changing instrument program. `g1` collects the unnormalized event properties, while
`g2` characterizes when the optional conditional state exists.

`g3` reconstructs the event output both from mass weighted leaf conditionals and from the event
conditional state. These results formalize finite instrument conditioning in the framework
described in [Watrous2018].

## Main statements

* `g1`: positive event output with mass in the unit interval and an exact zero criterion.
* `g2`: existence of a density conditional exactly at positive mass.
* `g3`: reconstruction of the unnormalized event output.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.DimConditioning.EventCondition
open Qatlib.Concepts.DimInstruments.DimTreeExec
open scoped BigOperators ComplexOrder

/-- Filtering a list cannot increase the sum of a function that is nonnegative on the original
list. -/
lemma sum_filter_re_le {α : Type} (l : List α) (p : α → Bool) (f : α → ℝ)
    (hf : ∀ a ∈ l, 0 ≤ f a) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 0 ≤ f a := hf a (by simp)
    have hl : ∀ b ∈ l, 0 ≤ f b := fun b hb => hf b (List.mem_cons_of_mem a hb)
    cases hp : p a
    · have hneg : ¬ p a = true := by simp [hp]
      simp only [List.filter_cons_of_neg hneg, List.map_cons, List.sum_cons]
      exact le_trans (ih hl) (le_add_of_nonneg_left ha)
    · simp only [List.filter_cons_of_pos hp, List.map_cons, List.sum_cons]
      exact add_le_add_right (ih hl) (f a)

/-- The event output is the sum of the leaf outputs whose actual records satisfy the event
predicate. -/
lemma eventMap_apply {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    (rho : Operator D) :
    eventMap P event rho =
      (((leaves P).filter (fun t => event t.record)).map (fun t => t.map rho)).sum := by
  simpa [eventMap, Function.comp_def] using
    (sum_map_apply (((leaves P).filter (fun t => event t.record)).map Leaf.map) rho)

/-- A finite list sum of positive semidefinite operators is positive semidefinite. -/
lemma list_sum_posSemidef {n : ℕ} (l : List (Operator n))
    (h : ∀ A ∈ l, A.PosSemidef) : l.sum.PosSemidef := by
  induction l with
  | nil =>
    simp
    exact Matrix.PosSemidef.zero
  | cons A l ih =>
    simp only [List.sum_cons]
    exact (h A (by simp)).add (ih fun B hB => h B (List.mem_cons_of_mem A hB))

/-- The event map sends a positive semidefinite input to a positive semidefinite output. -/
lemma eventMap_posSemidef {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : rho.PosSemidef) :
    (eventMap P event rho).PosSemidef := by
  rw [eventMap_apply]
  refine list_sum_posSemidef _ ?_
  intro A hA
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hA
  exact (leaves_cp P t (List.mem_filter.mp ht).1).positive hρ

/-- For positive semidefinite input, the trace of the event output is the complex cast of its
real event mass. -/
lemma trace_eventMap_eq {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : rho.PosSemidef) :
    Matrix.trace (eventMap P event rho) = ((eventMass P event rho : ℝ) : ℂ) := by
  have him : (Matrix.trace (eventMap P event rho)).im = 0 :=
    (RCLike.nonneg_iff.mp (eventMap_posSemidef P event hρ).trace_nonneg).2
  exact Complex.ext rfl (by rw [him, Complex.ofReal_im])

/-- The event mass is nonnegative on positive semidefinite input. -/
lemma eventMass_nonneg {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : rho.PosSemidef) :
    0 ≤ eventMass P event rho :=
  (RCLike.nonneg_iff.mp (eventMap_posSemidef P event hρ).trace_nonneg).1

/-- The real part of a finite list sum of complex numbers equals the sum of their real parts. -/
lemma re_list_sum (l : List ℂ) : l.sum.re = (l.map Complex.re).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Complex.add_re]

/-- The event mass is the sum of the real traces of the selected leaf outputs. -/
lemma eventMass_eq_leafSum {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    (rho : Operator D) :
    eventMass P event rho =
      (((leaves P).filter (fun t => event t.record)).map
        (fun t => (Matrix.trace (t.map rho)).re)).sum := by
  rw [eventMass, eventMap_apply, trace_list_sum, re_list_sum]
  simp [List.map_map, Function.comp_def]

/-- The real trace of the input equals the sum of the real traces of all leaf outputs. -/
lemma forget_re_eq_leafSum {D E : ℕ} (P : Program D E) (rho : Operator D) :
    (Matrix.trace rho).re =
      (((leaves P).map (fun t => (Matrix.trace (t.map rho)).re)).sum) := by
  have hsum : ((leaves P).map (fun t => Leaf.map t rho)).sum = forget P rho := by
    simpa [forget, Function.comp_def] using (sum_map_apply ((leaves P).map Leaf.map) rho).symm
  calc
    (Matrix.trace rho).re = (Matrix.trace (forget P rho)).re := by
      rw [forget_trace P rho]
    _ = (Matrix.trace (((leaves P).map (fun t => Leaf.map t rho)).sum)).re := by
      rw [hsum]
    _ = (((leaves P).map (fun t => Leaf.map t rho)).map Matrix.trace).sum.re := by
      rw [trace_list_sum]
    _ = (((leaves P).map (fun t => (Matrix.trace (Leaf.map t rho)).re)).sum) := by
      rw [re_list_sum]
      simp [List.map_map, Function.comp_def]

/-- The mass of a record event is at most one for a density operator input. -/
lemma eventMass_le_one {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : IsDensityOperator rho) :
    eventMass P event rho ≤ 1 := by
  have htot := forget_re_eq_leafSum P rho
  rw [hρ.2, Complex.one_re] at htot
  rw [eventMass_eq_leafSum, htot]
  exact sum_filter_re_le (leaves P) (fun t => event t.record)
    (fun t => (Matrix.trace (t.map rho)).re) fun t ht =>
      (RCLike.nonneg_iff.mp ((leaves_cp P t ht).positive hρ.1).trace_nonneg).1

/-- For positive semidefinite input, the event mass is zero exactly when the event output is the
zero operator. -/
lemma eventMass_eq_zero_iff {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : rho.PosSemidef) :
    eventMass P event rho = 0 ↔ eventMap P event rho = 0 := by
  constructor
  · intro hz
    apply (Matrix.PosSemidef.trace_eq_zero_iff (eventMap_posSemidef P event hρ)).mp
    rw [trace_eventMap_eq P event hρ, hz]
    rfl
  · intro hz
    rw [eventMass, hz]
    simp

/-- A positive semidefinite operator is recovered by multiplying its positive trace
normalization by its real trace, with a zero contribution when the real trace is zero. -/
lemma leaf_reconstruct {E : ℕ} {A : Operator E} (hA : A.PosSemidef) :
    (let p := (Matrix.trace A).re
      if 0 < p then ((p : ℝ) : ℂ) • (((p : ℝ) : ℂ)⁻¹ • A) else 0) = A := by
  simp only
  have hp : 0 ≤ (Matrix.trace A).re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have him : (Matrix.trace A).im = 0 := (RCLike.nonneg_iff.mp hA.trace_nonneg).2
  by_cases h0 : 0 < (Matrix.trace A).re
  · simp only [h0, ↓reduceIte]
    have hne : (((Matrix.trace A).re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  · simp only [h0, ↓reduceIte]
    have hz : (Matrix.trace A).re = 0 := le_antisymm (not_lt.mp h0) hp
    exact ((Matrix.PosSemidef.trace_eq_zero_iff hA).mp (Complex.ext hz him)).symm

/-- Mass weighted leaf conditional outputs reconstruct the unnormalized event output for
positive semidefinite input. -/
lemma weighted_eq_eventMap {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : rho.PosSemidef) :
    weightedConditionals P event rho = eventMap P event rho := by
  unfold weightedConditionals
  rw [eventMap_apply]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have hmem : t ∈ leaves P := (List.mem_filter.mp ht).1
  simpa using leaf_reconstruct ((leaves_cp P t hmem).positive hρ)

/-- Dividing the event output by its positive event mass yields a density operator for density
input. -/
lemma conditional_density {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    {rho : Operator D} (hρ : IsDensityOperator rho) (h : 0 < eventMass P event rho) :
    IsDensityOperator (((eventMass P event rho : ℝ) : ℂ)⁻¹ • eventMap P event rho) := by
  have hpos := eventMap_posSemidef P event hρ.1
  have hinv : (0 : ℂ) ≤ (((eventMass P event rho : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr h.le)
  have hne : ((eventMass P event rho : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h
  refine ⟨Matrix.PosSemidef.smul hpos hinv, ?_⟩
  rw [Matrix.trace_smul, trace_eventMap_eq P event hρ.1, smul_eq_mul, inv_mul_cancel₀ hne]

/-- For density input, the event output is positive semidefinite, its mass lies in `[0, 1]`, and
zero mass is equivalent to zero output. -/
theorem g1 :
    ∀ (D E : ℕ) (P : Program D E) (event : List (ℕ × ℕ) → Bool)
      (rho : Operator D), IsDensityOperator rho →
      (eventMap P event rho).PosSemidef ∧
      0 ≤ eventMass P event rho ∧ eventMass P event rho ≤ 1 ∧
      (eventMass P event rho = 0 ↔ eventMap P event rho = 0) := by
  intro D E P event rho hρ
  exact ⟨eventMap_posSemidef P event hρ.1, eventMass_nonneg P event hρ.1,
    eventMass_le_one P event hρ, eventMass_eq_zero_iff P event hρ.1⟩

/-- For density input, an event conditional density operator exists exactly when the event mass
is positive, and the optional conditional is `none` exactly when that mass is zero. -/
theorem g2 :
    ∀ (D E : ℕ) (P : Program D E) (event : List (ℕ × ℕ) → Bool)
      (rho : Operator D), IsDensityOperator rho →
      ((∃ sigma, conditional P event rho = some sigma ∧ IsDensityOperator sigma) ↔
        0 < eventMass P event rho) ∧
      (conditional P event rho = none ↔ eventMass P event rho = 0) := by
  intro D E P event rho hρ
  have h0 := eventMass_nonneg P event hρ.1
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨sigma, hsome, _⟩
      by_contra hle
      have hnone : conditional P event rho = none := by
        simp [conditional, not_lt.mp hle]
      rw [hnone] at hsome
      cases hsome
    · intro hpos
      refine ⟨_, ?_, conditional_density P event hρ hpos⟩
      simp [conditional, hpos]
  · constructor
    · intro hnone
      by_contra hpos
      have hlt : 0 < eventMass P event rho := lt_of_le_of_ne' h0 (by simpa using hpos)
      have hsome : conditional P event rho = some
          (((eventMass P event rho : ℝ) : ℂ)⁻¹ • eventMap P event rho) := by
        simp [conditional, hlt]
      rw [hnone] at hsome
      cases hsome
    · intro hz
      simp [conditional, hz]

/-- For density input, weighted leaf conditionals reconstruct the event output, and every
returned event conditional reconstructs the same output after multiplication by the event
mass. -/
theorem g3 :
    ∀ (D E : ℕ) (P : Program D E) (event : List (ℕ × ℕ) → Bool)
      (rho : Operator D), IsDensityOperator rho →
      weightedConditionals P event rho = eventMap P event rho ∧
      (∀ sigma, conditional P event rho = some sigma →
        ((eventMass P event rho : ℝ) : ℂ) • sigma = eventMap P event rho) := by
  intro D E P event rho hρ
  refine ⟨weighted_eq_eventMap P event hρ.1, ?_⟩
  intro sigma hsome
  by_cases hpos : 0 < eventMass P event rho
  · have hsigma : sigma = ((eventMass P event rho : ℝ) : ℂ)⁻¹ • eventMap P event rho := by
      simp only [conditional, hpos, ite_true] at hsome
      cases hsome
      rfl
    have hne : ((eventMass P event rho : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
    rw [hsigma, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · have hnone : conditional P event rho = none := by
      simp [conditional, not_lt.mp hpos]
    rw [hnone] at hsome
    cases hsome

end Qatlib.Concepts.DimConditioning.EventCondition
