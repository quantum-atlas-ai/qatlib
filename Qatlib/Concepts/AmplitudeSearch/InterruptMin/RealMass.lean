/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Probability laws from real-valued masses

This module constructs probability mass functions from nonnegative real masses summing to one.
It relates real weighted sums to extended nonnegative expectations and transports output and
cost maps to `CostedLaw`.

These conversion lemmas supply the probability interface for the randomized search analysis of
[BoyerEtAl1998].

## Main statements

* `pmfOfRealMass`: The probability mass function obtained by embedding nonnegative real masses
  whose sum is one.
* `expectation_pmfOfRealMass`: A real payoff sum weighted by `mass` represents expectation under
  `pmfOfRealMass`.
* `ofRealMass_expectedCost`: A real weighted cost sum represents the expected cost of the law
  constructed by `ofRealMass`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped ENNReal BigOperators Classical

variable {α β : Type*}

/-- The probability mass function obtained by embedding nonnegative real masses whose sum is
one. -/
noncomputable def pmfOfRealMass (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) : PMF α :=
  ⟨fun a => ENNReal.ofReal (mass a), ENNReal.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable, hs.tsum_eq, ENNReal.ofReal_one])⟩

/-- The constructed probability law assigns mass `ENNReal.ofReal (mass a)` to `a`. -/
@[simp] theorem pmfOfRealMass_apply (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (a : α) :
    pmfOfRealMass mass hn hs a = ENNReal.ofReal (mass a) := rfl

/-- Taking the real value of a constructed probability mass recovers the original mass. -/
@[simp] theorem pmfOfRealMass_toReal (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (a : α) :
    (pmfOfRealMass mass hn hs a).toReal = mass a := ENNReal.toReal_ofReal (hn a)

namespace CostedLaw

/-- A real weighted sum of a nonnegative payoff represents its extended nonnegative expectation. -/
theorem expectation_ofReal (p : PMF α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (q : ℝ) (hq : HasSum (fun a => (p a).toReal * f a) q) :
    expectation p (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal q := by
  unfold expectation
  calc
    _ = ∑' a, ENNReal.ofReal ((p a).toReal * f a) := by
      apply tsum_congr
      intro a
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (p.apply_ne_top a)]
    _ = ENNReal.ofReal (∑' a, (p a).toReal * f a) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun a => mul_nonneg ENNReal.toReal_nonneg (hf a)) hq.summable).symm
    _ = ENNReal.ofReal q := congrArg ENNReal.ofReal hq.tsum_eq

/-- On a finite type, the expectation of an embedded nonnegative real payoff is the embedding of
its finite weighted sum. -/
theorem expectation_ofReal_fintype [Fintype α] (p : PMF α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    expectation p (fun a => ENNReal.ofReal (f a)) =
      ENNReal.ofReal (∑ a, (p a).toReal * f a) :=
  expectation_ofReal p f hf _ (hasSum_fintype _)

/-- A real payoff sum weighted by `mass` represents expectation under `pmfOfRealMass`. -/
theorem expectation_pmfOfRealMass (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (q : ℝ) (hq : HasSum (fun a => mass a * f a) q) :
    expectation (pmfOfRealMass mass hn hs) (fun a => ENNReal.ofReal (f a)) =
      ENNReal.ofReal q := by
  apply expectation_ofReal _ f hf q
  simpa only [pmfOfRealMass_toReal] using hq

/-- The event probability under `pmfOfRealMass` is the embedded sum of real masses satisfying
the event. -/
theorem event_pmfOfRealMass (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (E : α → Prop) :
    event (pmfOfRealMass mass hn hs) E =
      ENNReal.ofReal (∑' a, if E a then mass a else 0) := by
  classical
  have hnn : ∀ a, 0 ≤ if E a then mass a else 0 := by
    intro a
    split_ifs
    · exact hn a
    · exact le_rfl
  have hsum : Summable (fun a => if E a then mass a else 0) :=
    hs.summable.of_nonneg_of_le hnn (fun a => by split_ifs <;> simp [hn a])
  unfold event expectation
  calc
    _ = ∑' a, ENNReal.ofReal (if E a then mass a else 0) := by
      apply tsum_congr
      intro a
      by_cases h : E a <;> simp [h]
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm

/-- The costed output law obtained by mapping a normalized real mass law to its output and
natural-valued cost. -/
noncomputable def ofRealMass (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (output : α → β) (cost : α → ℕ) : CostedLaw β :=
  (pmfOfRealMass mass hn hs).map (fun a => (output a, cost a))

/-- An event of the costed output law is the embedded sum of source masses whose mapped output
and cost satisfy the event. -/
theorem ofRealMass_event (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (output : α → β) (cost : α → ℕ) (E : β × ℕ → Prop) :
    event (ofRealMass mass hn hs output cost) E =
      ENNReal.ofReal (∑' a, if E (output a, cost a) then mass a else 0) := by
  classical
  change expectation ((pmfOfRealMass mass hn hs).map _) _ = _
  rw [expectation_map]
  exact event_pmfOfRealMass mass hn hs (fun a => E (output a, cost a))

/-- A real weighted cost sum represents the expected cost of the law constructed by
`ofRealMass`. -/
theorem ofRealMass_expectedCost (mass : α → ℝ) (hn : ∀ a, 0 ≤ mass a)
    (hs : HasSum mass 1) (output : α → β) (cost : α → ℕ)
    (q : ℝ) (hq : HasSum (fun a => mass a * (cost a : ℝ)) q) :
    expectedCost (ofRealMass mass hn hs output cost) = ENNReal.ofReal q := by
  unfold expectedCost ofRealMass
  rw [expectation_map]
  convert expectation_pmfOfRealMass mass hn hs (fun a => (cost a : ℝ))
    (fun a => Nat.cast_nonneg (cost a)) q hq using 1
  simp

end CostedLaw
end Qatlib.Concepts.AmplitudeSearch.InterruptMin
