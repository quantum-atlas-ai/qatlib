/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Bernoulli identification by finite likelihood testing

Fixed source: arXiv:2105.02859v3, Lemma 5, printed page 14,
Eqs. (61)–(62). The PDF SHA-256 is
`facab6a75ee1db4ee164ecad10ba2b9e9eca8562c7e686d8f8c07ee17fc322af`.

The source proves a Hoeffding sample bound proportional to
`(b-a)⁻² log(1/δ)`. The inherited statement below requests the stronger,
variance-sensitive bound `(a+b)(b-a)⁻² log(1/δ)`. We preserve that statement
and prove it with the universal constant four by a likelihood test.

The test consumes the actual finite record of independent Bernoulli samples.
Each error probability is bounded by the Hellinger affinity of the two
record laws; product factorization and an elementary square-root estimate
give the required exponential tail. There are no assumed concentration
bounds, unconstrained resource fields, or assumed correctness properties.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

namespace Qatlib.Papers.GrandUnif21.MainResults.BernoulliIdentification

/-- Hellinger affinity controls each error probability of the likelihood test. -/
theorem likelihood_success {X : Type*} [Fintype X] (p q : FinDist X) :
    ∃ test : X → Bool,
      1 - ∑ x, Real.sqrt (p.prob x * q.prob x) ≤ eventMass p (fun x => test x = false) ∧
      1 - ∑ x, Real.sqrt (p.prob x * q.prob x) ≤ eventMass q (fun x => test x = true) := by
  classical
  let test : X → Bool := fun x => decide (p.prob x ≤ q.prob x)
  refine ⟨test, ?_, ?_⟩
  · have hpoint (x : X) : p.prob x ≤
        (if test x = false then p.prob x else 0) + Real.sqrt (p.prob x * q.prob x) := by
      by_cases h : p.prob x ≤ q.prob x
      · simp only [test, decide_eq_true h, Bool.true_eq_false, ↓reduceIte, zero_add]
        apply Real.le_sqrt_of_sq_le
        nlinarith [mul_le_mul_of_nonneg_left h (p.nonneg x)]
      · simp only [test, decide_eq_false h, ↓reduceIte]
        linarith [Real.sqrt_nonneg (p.prob x * q.prob x)]
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
    rw [p.sum_one, Finset.sum_add_distrib] at hsum
    unfold eventMass
    rw [Finset.sum_filter]
    linarith
  · have hpoint (x : X) : q.prob x ≤
        (if test x = true then q.prob x else 0) + Real.sqrt (p.prob x * q.prob x) := by
      by_cases h : p.prob x ≤ q.prob x
      · simp only [test, decide_eq_true h, ↓reduceIte]
        linarith [Real.sqrt_nonneg (p.prob x * q.prob x)]
      · simp only [test, decide_eq_false h, Bool.false_eq_true, ↓reduceIte, zero_add]
        apply Real.le_sqrt_of_sq_le
        nlinarith [mul_le_mul_of_nonneg_right (le_of_not_ge h) (q.nonneg x)]
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
    rw [q.sum_one, Finset.sum_add_distrib] at hsum
    unfold eventMass
    rw [Finset.sum_filter]
    linarith

/-- Affinity factors across the independent coordinates of a finite observation record. -/
theorem affinity_product {X : Type*} [Fintype X] (p q : FinDist X) (n : ℕ) :
    (∑ ω : Fin n → X, Real.sqrt
        ((independent (fun _ : Fin n => p)).prob ω *
         (independent (fun _ : Fin n => q)).prob ω)) =
      (∑ x, Real.sqrt (p.prob x * q.prob x)) ^ n := by
  classical
  simp only [independent, ← Finset.prod_mul_distrib]
  simp_rw [Real.sqrt_prod _ (fun i _ => mul_nonneg (p.nonneg _) (q.nonneg _))]
  have h := Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset X))
    (f := fun _ x => Real.sqrt (p.prob x * q.prob x))
  simpa only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h.symm

/-- The Bernoulli affinity has a variance-sensitive exponential bound. -/
theorem bernoulli_affinity_bound (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) :
    Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤
      Real.exp (-((b - a) ^ 2 / (4 * (b + a)))) := by
  have hb0 : 0 ≤ b := ha0.trans hab.le
  have ha1 : a ≤ 1 := hab.le.trans hb1
  have hs : 0 < b + a := by linarith
  have hsa := Real.sq_sqrt ha0
  have hsb := Real.sq_sqrt hb0
  have hsca := Real.sq_sqrt (sub_nonneg.mpr ha1)
  have hscb := Real.sq_sqrt (sub_nonneg.mpr hb1)
  have hsum : (Real.sqrt b + Real.sqrt a) ^ 2 ≤ 2 * (b + a) := by
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a)]
  have hid : b - a = (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) := by
    nlinarith
  have hgap : (b - a) ^ 2 ≤ 2 * (b + a) * (Real.sqrt b - Real.sqrt a) ^ 2 := by
    calc
      (b - a) ^ 2 = (Real.sqrt b - Real.sqrt a) ^ 2 *
          (Real.sqrt b + Real.sqrt a) ^ 2 := by rw [hid]; ring
      _ ≤ (Real.sqrt b - Real.sqrt a) ^ 2 * (2 * (b + a)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  have hhell : (Real.sqrt b - Real.sqrt a) ^ 2 ≤
      2 * (1 - (Real.sqrt a * Real.sqrt b + Real.sqrt (1 - a) * Real.sqrt (1 - b))) := by
    nlinarith [sq_nonneg (Real.sqrt (1 - a) - Real.sqrt (1 - b))]
  have hrate : (b - a) ^ 2 / (4 * (b + a)) ≤
      1 - (Real.sqrt a * Real.sqrt b + Real.sqrt (1 - a) * Real.sqrt (1 - b)) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (b + a))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhell (by positivity : 0 ≤ 2 * (b + a))]
  rw [Real.sqrt_mul ha0, Real.sqrt_mul (sub_nonneg.mpr ha1)]
  have hexp := Real.add_one_le_exp (-((b - a) ^ 2 / (4 * (b + a))))
  linarith


end Qatlib.Papers.GrandUnif21.MainResults.BernoulliIdentification
