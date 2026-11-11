/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.ApproximateMomentRule
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! A computable exact-rational moment check and its real Banach consumer.
This verifies finite table data; success of any numerical producer and the
Python/Lean serialization connection are separate. -/
set_option autoImplicit false
namespace Qatlib.Foundations.OpCalculus.ContourCalc
open MeasureTheory
open scoped BigOperators

/-- Construction for rational Reference Moment in the rational moment certificate model. -/
def rationalReferenceMoment (k : ℕ) : ℚ := if Even k then 2/(k+1) else 0

/-- Construction for rational Moment Defect in the rational moment certificate model. -/
def rationalMomentDefect (Q : ℕ) (node weight : Fin Q → ℚ) (k : ℕ) : ℚ :=
  rationalReferenceMoment k - ∑ q, weight q * (node q)^k

/-- The finite arithmetic predicate used by the checker; there is no real
root or integral oracle in this computation. -/
def rationalMomentCheck (Q K : ℕ) (node weight : Fin Q → ℚ) (η : ℚ) : Bool :=
  decide (∀ k : Fin (K+1), |rationalMomentDefect Q node weight k| ≤ η)

/-- Construction for rational Positive Moment Check in the rational moment certificate model. -/
def rationalPositiveMomentCheck (Q K : ℕ) (node weight : Fin Q → ℚ) (η : ℚ) : Bool :=
  decide (0 < Q ∧ 0 ≤ η ∧ (∀ q, -1 ≤ node q ∧ node q ≤ 1) ∧
    ∀ q, 0 < weight q) && rationalMomentCheck Q K node weight η

/-- The identity or estimate `rationalMomentCheck_sound` holds with the displayed separation, geometry and norm hypotheses. -/
theorem rationalMomentCheck_sound (Q K : ℕ) (node weight : Fin Q → ℚ) (η : ℚ)
    (hc : rationalMomentCheck Q K node weight η = true) :
    ∀ k : Fin (K+1), |rationalMomentDefect Q node weight k| ≤ η := by
  exact of_decide_eq_true hc

noncomputable section

/-- The checker's rational reference values are the actual real moments. -/
theorem reference_moment_cast (k : ℕ) :
    (∫ t in (-1 : ℝ)..1, t^k) = (rationalReferenceMoment k : ℝ) := by
  rw [integral_pow]
  by_cases hk : Even k
  · have hp : (-1 : ℝ)^(k+1) = -1 := by rw [pow_succ, hk.neg_one_pow]; norm_num
    simp [rationalReferenceMoment, hk, hp, one_add_one_eq_two]
  · have ho : Odd k := Nat.not_even_iff_odd.mp hk
    have hp : (-1 : ℝ)^(k+1) = 1 := by rw [pow_succ, ho.neg_one_pow]; norm_num
    simp [rationalReferenceMoment, hk, hp]

/-- The identity or estimate `rational_moment_real_bound` holds with the displayed separation, geometry and norm hypotheses. -/
theorem rational_moment_real_bound
    (Q K : ℕ) (node weight : Fin Q → ℚ) (η : ℚ)
    (hc : rationalMomentCheck Q K node weight η = true) (k : Fin (K+1)) :
    |(∫ t in (-1 : ℝ)..1, t^(k : ℕ)) -
      ∑ q, (weight q : ℝ) * (node q : ℝ)^(k : ℕ)| ≤ (η : ℝ) := by
  rw [reference_moment_cast]
  have h := rationalMomentCheck_sound Q K node weight η hc k
  exact_mod_cast h

/-- Actual rational input data and a successful finite check give the vector
polynomial error in every real Banach space, including matrix operator norm. -/
theorem rational_moment_vector_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q K : ℕ) (node weight : Fin Q → ℚ) (η : ℚ)
    (hc : rationalMomentCheck Q K node weight η = true) (c : Fin (K+1) → E) :
    ‖(∫ t in (-1 : ℝ)..1, finiteVectorPolynomial K c t) -
      ∑ q, (weight q : ℝ) • finiteVectorPolynomial K c (node q : ℝ)‖ ≤
      (η : ℝ) * ∑ k, ‖c k‖ :=
  finite_vector_moment_error Q K (-1) 1 (fun q => (node q : ℝ))
    (fun q => (weight q : ℝ)) c η (rational_moment_real_bound Q K node weight η hc)

/-- The identity or estimate `rational_positive_rule_error` holds with the displayed separation, geometry and norm hypotheses. -/
theorem rational_positive_rule_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q K : ℕ) (node weight : Fin Q → ℚ) (η : ℚ)
    (hc : rationalPositiveMomentCheck Q K node weight η = true)
    (c : Fin (K+1) → E) (f : ℝ → E) (e C : ℝ)
    (hf : IntervalIntegrable f volume (-1) 1) (hC : ∑ k, ‖c k‖ ≤ C)
    (happrox : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖f t-finiteVectorPolynomial K c t‖ ≤ e) :
    ‖(∫ t in (-1 : ℝ)..1, f t) -
      ∑ q, (weight q : ℝ) • f (node q : ℝ)‖ ≤
      (2 + ∑ q, (weight q : ℝ)) * e + C * (η : ℝ) := by
  have hparts : decide (0 < Q ∧ 0 ≤ η ∧ (∀ q, -1 ≤ node q ∧ node q ≤ 1) ∧
      ∀ q, 0 < weight q) = true ∧ rationalMomentCheck Q K node weight η = true := by
    simpa only [rationalPositiveMomentCheck, Bool.and_eq_true] using hc
  have hdata : 0 < Q ∧ 0 ≤ η ∧ (∀ q, -1 ≤ node q ∧ node q ≤ 1) ∧
      ∀ q, 0 < weight q := of_decide_eq_true hparts.1
  have hn (q : Fin Q) : (node q : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · exact_mod_cast (hdata.2.2.1 q).1
    · exact_mod_cast (hdata.2.2.1 q).2
  have hw (q : Fin Q) : 0 ≤ (weight q : ℝ) := by
    exact_mod_cast (hdata.2.2.2 q).le
  have hη : (0 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hdata.2.1
  have he := positive_moment_rule_error Q K (-1) 1 (fun q => (node q : ℝ))
    (fun q => (weight q : ℝ)) c f e η C (by norm_num) hn hw hf hη
    (rational_moment_real_bound Q K node weight η hparts.2) hC happrox
  norm_num only [sub_neg_eq_add, one_add_one_eq_two] at he
  exact he

end
end Qatlib.Foundations.OpCalculus.ContourCalc
