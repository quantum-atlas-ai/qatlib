/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability laws with accumulated costs

This module defines `CostedLaw`, a probability mass function on an output and a natural-number
cost. The operations `ret`, `charge`, and `bind` describe deterministic return, fixed charging,
and sequential composition, with associativity and identity laws.

Extended nonnegative expectations give `expectedCost`, event probabilities, and budget-overflow
estimates. These definitions provide elementary probability and cost accounting for randomized
quantum-algorithm pipelines, such as the Monte Carlo setting of [Montanaro2015].

## Main statements

* `expectedCost_bind`: addition of expected costs under sequential composition.
* `overflow_mul_le_expectedCost`: an expected-cost bound for budget overflow.
* `success_le_within_add_overflow`: separation of success within budget from overflow.
* `BoundedBy.bind`: addition of supportwise bounds under composition.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

/-- A probability mass function on outputs paired with natural-number costs. -/
abbrev CostedLaw (α : Type*) := PMF (α × ℕ)

namespace CostedLaw

section
open scoped ENNReal Classical
variable {α β γ : Type*}

/-- The deterministic costed law returning the specified output with zero cost. -/
noncomputable def ret (a : α) : CostedLaw α := PMF.pure (a, 0)

/-- Adds a fixed natural-number charge to every outcome's cost. -/
noncomputable def charge (n : ℕ) (p : CostedLaw α) : CostedLaw α :=
  p.map (fun x => (x.1, n + x.2))

/-- Sequentially composes a costed law with an output-dependent costed law, adding their costs. -/
noncomputable def bind (p : CostedLaw α) (f : α → CostedLaw β) : CostedLaw β :=
  PMF.bind p (fun x => charge x.2 (f x.1))

/-- Adding zero charge leaves a costed law unchanged. -/
@[simp] theorem charge_zero (p : CostedLaw α) : charge 0 p = p := by
  simpa only [charge, Nat.zero_add, Prod.eta] using! PMF.map_id p

/-- Charging a deterministic zero-cost return gives the point mass at that output and the
specified cost. -/
@[simp] theorem charge_ret (n : ℕ) (a : α) : charge n (ret a) = PMF.pure (a, n) := by
  simp [charge, ret, PMF.pure_map]

/-- Two successive fixed charges combine into their sum. -/
@[simp] theorem charge_charge (m n : ℕ) (p : CostedLaw α) :
    charge m (charge n p) = charge (m + n) p := by
  simp only [charge, PMF.map_comp, Function.comp_def, Nat.add_assoc]

/-- Binding a deterministic zero-cost return to a continuation gives that continuation at the
returned value. -/
@[simp] theorem ret_bind (a : α) (f : α → CostedLaw β) : bind (ret a) f = f a := by
  simp [bind, ret, PMF.pure_bind]

/-- Binding a costed law to the zero-cost return operation leaves it unchanged. -/
@[simp] theorem bind_ret (p : CostedLaw α) : bind p ret = p := by
  simpa only [bind, charge_ret, Prod.eta] using PMF.bind_pure p

/-- A fixed charge on the first computation can be moved to the sequentially composed law. -/
theorem charge_bind (n : ℕ) (p : CostedLaw α) (f : α → CostedLaw β) :
    bind (charge n p) f = charge n (bind p f) := by
  simp only [bind, charge, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    Nat.add_assoc]

/-- Sequential composition of costed laws is associative. -/
theorem bind_assoc (p : CostedLaw α) (f : α → CostedLaw β) (g : β → CostedLaw γ) :
    bind (bind p f) g = bind p (fun a => bind (f a) g) := by
  simp only [bind, PMF.bind_bind]
  congr 1
  funext x
  exact charge_bind x.2 (f x.1) g

/-- The expectation of an extended nonnegative function under a probability mass function,
defined by a weighted infinite sum. -/
noncomputable def expectation (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

/-- Expectation under a point mass evaluates the function at its support point. -/
@[simp] theorem expectation_pure (a : α) (f : α → ℝ≥0∞) :
    expectation (PMF.pure a) f = f a := by
  classical
  simp [expectation, PMF.pure_apply]

/-- Expectation under a bound probability law equals the expectation of the conditional
expectations. -/
theorem expectation_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    expectation (PMF.bind p q) f = expectation p (fun a => expectation (q a) f) := by
  simp only [expectation, PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left,
    mul_assoc]
  exact ENNReal.tsum_comm

/-- Expectation under a mapped law equals expectation of the function composed with the mapping. -/
@[simp] theorem expectation_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expectation (p.map g) f = expectation p (fun a => f (g a)) := by
  simp [PMF.map, expectation_bind, Function.comp_def]

/-- The expectation of a constant under a probability mass function is that constant. -/
@[simp] theorem expectation_const (p : PMF α) (c : ℝ≥0∞) :
    expectation p (fun _ => c) = c := by
  simp [expectation, ENNReal.tsum_mul_right]

/-- Expectation is additive for extended nonnegative functions. -/
theorem expectation_add (p : PMF α) (f g : α → ℝ≥0∞) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp only [expectation, mul_add, ENNReal.tsum_add]

/-- The extended nonnegative expectation of the natural-number cost recorded by a costed law. -/
noncomputable def expectedCost (p : CostedLaw α) : ℝ≥0∞ := expectation p (fun x => x.2)

/-- A deterministic zero-cost return has expected cost zero. -/
@[simp] theorem expectedCost_ret (a : α) : expectedCost (ret a) = 0 := by
  simp [expectedCost, ret]

/-- A fixed charge increases expected cost by that charge. -/
@[simp] theorem expectedCost_charge (n : ℕ) (p : CostedLaw α) :
    expectedCost (charge n p) = n + expectedCost p := by
  simp [expectedCost, charge, Nat.cast_add, expectation_add]

/-- The expected cost of sequential composition is the first expected cost plus the expected
continuation cost. -/
theorem expectedCost_bind (p : CostedLaw α) (f : α → CostedLaw β) :
    expectedCost (bind p f) =
      expectedCost p + expectation p (fun x => expectedCost (f x.1)) := by
  simp [expectedCost, bind, expectation_bind, charge, Nat.cast_add, expectation_add]

/-- The probability of a predicate under a probability mass function, expressed as an extended
nonnegative expectation of its indicator. -/
noncomputable def event (p : PMF α) (E : α → Prop) : ℝ≥0∞ :=
  expectation p (fun x => if E x then 1 else 0)

/-- The probability that the output satisfies the given predicate and its cost is at most the
budget. -/
noncomputable def within (p : CostedLaw α) (budget : ℕ) (E : α → Prop) : ℝ≥0∞ :=
  event p (fun x => E x.1 ∧ x.2 ≤ budget)

/-- The probability that the recorded cost strictly exceeds the budget. -/
noncomputable def overflow (p : CostedLaw α) (budget : ℕ) : ℝ≥0∞ :=
  event p (fun x => budget < x.2)

/-- The probability of exceeding a natural-number budget, multiplied by `budget + 1`, is at most
the expected cost. -/
theorem overflow_mul_le_expectedCost (p : CostedLaw α) (budget : ℕ) :
    (budget + 1 : ℝ≥0∞) * overflow p budget ≤ expectedCost p := by
  classical
  simp only [overflow, event, expectation, expectedCost, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases h : budget < x.2
  · simp only [ite_eq_left h, mul_one]
    rw [mul_comm (budget + 1 : ℝ≥0∞)]
    apply mul_le_mul_right
    exact_mod_cast Nat.succ_le_of_lt h
  · simp [h]

/-- The success probability is at most the probability of success within budget plus the
overflow probability. -/
theorem success_le_within_add_overflow (p : CostedLaw α) (budget : ℕ) (E : α → Prop) :
    event p (fun x => E x.1) ≤ within p budget E + overflow p budget := by
  classical
  simp only [event, within, overflow, expectation, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases he : E x.1 <;> by_cases hb : x.2 ≤ budget <;>
    simp [he, hb, Nat.not_lt_of_ge, Nat.lt_of_not_ge]

/-- Every outcome in the support of the costed law has cost at most the specified bound. -/
noncomputable def BoundedBy (p : CostedLaw α) (bound : ℕ) : Prop :=
  ∀ x ∈ p.support, x.2 ≤ bound

/-- A deterministic zero-cost return is bounded by every natural-number bound. -/
@[simp] theorem boundedBy_ret (a : α) (bound : ℕ) : BoundedBy (ret a) bound := by
  intro x hx
  have hx' : x = (a, 0) := by simpa [ret, PMF.mem_support_pure_iff] using hx
  subst x
  exact Nat.zero_le _

/-- Adding a fixed charge increases a supportwise cost bound by that charge. -/
theorem BoundedBy.charge {p : CostedLaw α} {bound : ℕ} (h : BoundedBy p bound) (n : ℕ) :
    BoundedBy (charge n p) (n + bound) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact Nat.add_le_add_left (h y hy) n

/-- Sequential composition adds a supportwise cost bound for the first law to a uniform bound
for its continuations. -/
theorem BoundedBy.bind {p : CostedLaw α} {f : α → CostedLaw β} {m n : ℕ}
    (hp : BoundedBy p m) (hf : ∀ a, BoundedBy (f a) n) :
    BoundedBy (bind p f) (m + n) := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  exact (BoundedBy.charge (hf x.1) x.2 y hy).trans (Nat.add_le_add_right (hp x hx) n)

/-- A supportwise cost bound also bounds the expected cost. -/
theorem BoundedBy.expectedCost_le {p : CostedLaw α} {bound : ℕ} (h : BoundedBy p bound) :
    expectedCost p ≤ (bound : ℝ≥0∞) := by
  rw [← expectation_const p (bound : ℝ≥0∞)]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · apply mul_le_mul_right
    change (x.2 : ℝ≥0∞) ≤ (bound : ℝ≥0∞)
    exact_mod_cast h x ((PMF.mem_support_iff p x).mpr hx)

end
end CostedLaw
end Qatlib.Concepts.LinearLearning.ConcisePipeline
