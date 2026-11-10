/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

abbrev CostedLaw (α : Type*) := PMF (α × ℕ)

namespace CostedLaw

section
open scoped ENNReal Classical
variable {α β γ : Type*}

noncomputable def ret (a : α) : CostedLaw α := PMF.pure (a, 0)

noncomputable def charge (n : ℕ) (p : CostedLaw α) : CostedLaw α :=
  p.map (fun x => (x.1, n + x.2))

noncomputable def bind (p : CostedLaw α) (f : α → CostedLaw β) : CostedLaw β :=
  PMF.bind p (fun x => charge x.2 (f x.1))

@[simp] theorem charge_zero (p : CostedLaw α) : charge 0 p = p := by
  simpa only [charge, Nat.zero_add, Prod.eta] using! PMF.map_id p

@[simp] theorem charge_ret (n : ℕ) (a : α) : charge n (ret a) = PMF.pure (a, n) := by
  simp [charge, ret, PMF.pure_map]

@[simp] theorem charge_charge (m n : ℕ) (p : CostedLaw α) :
    charge m (charge n p) = charge (m + n) p := by
  simp only [charge, PMF.map_comp, Function.comp_def, Nat.add_assoc]

@[simp] theorem ret_bind (a : α) (f : α → CostedLaw β) : bind (ret a) f = f a := by
  simp [bind, ret, PMF.pure_bind]

@[simp] theorem bind_ret (p : CostedLaw α) : bind p ret = p := by
  simpa only [bind, charge_ret, Prod.eta] using PMF.bind_pure p

theorem charge_bind (n : ℕ) (p : CostedLaw α) (f : α → CostedLaw β) :
    bind (charge n p) f = charge n (bind p f) := by
  simp only [bind, charge, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    Nat.add_assoc]

theorem bind_assoc (p : CostedLaw α) (f : α → CostedLaw β) (g : β → CostedLaw γ) :
    bind (bind p f) g = bind p (fun a => bind (f a) g) := by
  simp only [bind, PMF.bind_bind]
  congr 1
  funext x
  exact charge_bind x.2 (f x.1) g

noncomputable def expectation (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

@[simp] theorem expectation_pure (a : α) (f : α → ℝ≥0∞) :
    expectation (PMF.pure a) f = f a := by
  classical
  simp [expectation, PMF.pure_apply]

theorem expectation_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    expectation (PMF.bind p q) f = expectation p (fun a => expectation (q a) f) := by
  simp only [expectation, PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left,
    mul_assoc]
  exact ENNReal.tsum_comm

@[simp] theorem expectation_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expectation (p.map g) f = expectation p (fun a => f (g a)) := by
  simp [PMF.map, expectation_bind, Function.comp_def]

@[simp] theorem expectation_const (p : PMF α) (c : ℝ≥0∞) :
    expectation p (fun _ => c) = c := by
  simp [expectation, ENNReal.tsum_mul_right]

theorem expectation_add (p : PMF α) (f g : α → ℝ≥0∞) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp only [expectation, mul_add, ENNReal.tsum_add]

noncomputable def expectedCost (p : CostedLaw α) : ℝ≥0∞ := expectation p (fun x => x.2)

@[simp] theorem expectedCost_ret (a : α) : expectedCost (ret a) = 0 := by
  simp [expectedCost, ret]

@[simp] theorem expectedCost_charge (n : ℕ) (p : CostedLaw α) :
    expectedCost (charge n p) = n + expectedCost p := by
  simp [expectedCost, charge, Nat.cast_add, expectation_add]

theorem expectedCost_bind (p : CostedLaw α) (f : α → CostedLaw β) :
    expectedCost (bind p f) =
      expectedCost p + expectation p (fun x => expectedCost (f x.1)) := by
  simp [expectedCost, bind, expectation_bind, charge, Nat.cast_add, expectation_add]

noncomputable def event (p : PMF α) (E : α → Prop) : ℝ≥0∞ :=
  expectation p (fun x => if E x then 1 else 0)

noncomputable def within (p : CostedLaw α) (budget : ℕ) (E : α → Prop) : ℝ≥0∞ :=
  event p (fun x => E x.1 ∧ x.2 ≤ budget)

noncomputable def overflow (p : CostedLaw α) (budget : ℕ) : ℝ≥0∞ :=
  event p (fun x => budget < x.2)

theorem overflow_mul_le_expectedCost (p : CostedLaw α) (budget : ℕ) :
    (budget + 1 : ℝ≥0∞) * overflow p budget ≤ expectedCost p := by
  classical
  simp only [overflow, event, expectation, expectedCost, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases h : budget < x.2
  · simp only [if_pos h, mul_one]
    rw [mul_comm (budget + 1 : ℝ≥0∞)]
    apply mul_le_mul_right
    exact_mod_cast Nat.succ_le_of_lt h
  · simp [h]

theorem success_le_within_add_overflow (p : CostedLaw α) (budget : ℕ) (E : α → Prop) :
    event p (fun x => E x.1) ≤ within p budget E + overflow p budget := by
  classical
  simp only [event, within, overflow, expectation, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases he : E x.1 <;> by_cases hb : x.2 ≤ budget <;>
    simp [he, hb, Nat.not_lt_of_ge, Nat.lt_of_not_ge]

noncomputable def BoundedBy (p : CostedLaw α) (bound : ℕ) : Prop :=
  ∀ x ∈ p.support, x.2 ≤ bound

@[simp] theorem boundedBy_ret (a : α) (bound : ℕ) : BoundedBy (ret a) bound := by
  intro x hx
  have hx' : x = (a, 0) := by simpa [ret, PMF.mem_support_pure_iff] using hx
  subst x
  exact Nat.zero_le _

theorem BoundedBy.charge {p : CostedLaw α} {bound : ℕ} (h : BoundedBy p bound) (n : ℕ) :
    BoundedBy (charge n p) (n + bound) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact Nat.add_le_add_left (h y hy) n

theorem BoundedBy.bind {p : CostedLaw α} {f : α → CostedLaw β} {m n : ℕ}
    (hp : BoundedBy p m) (hf : ∀ a, BoundedBy (f a) n) :
    BoundedBy (bind p f) (m + n) := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  exact (BoundedBy.charge (hf x.1) x.2 y hy).trans (Nat.add_le_add_right (hp x hx) n)

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
