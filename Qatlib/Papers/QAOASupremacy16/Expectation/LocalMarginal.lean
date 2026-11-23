/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Local marginals and the classical expectation of a clause sum

Section 2.2 of [FarhiHarrow2016] notes that for fixed angles the expectation
`⟨γ, β|C|γ, β⟩` of Eq. (9) can be computed classically in time polynomial in the number of
clauses and the number of bits in the setting discussed there. A finite identity relevant to
that calculation decomposes an average over all registers into fibers of the restriction map to
a clause's support: the global average of a local clause is the sum over local assignments of
the marginal mass of that assignment times the clause value.

This module formalizes that decomposition for finite Boolean registers and arbitrary real weights.
The main theorem `expectation_localCost_eq_sum_marginals` rewrites the weighted average of a sum
of local clauses as a sum, over clauses, of local expectations computed from the marginal
distributions on their supports. For genuine probability weights the marginals are nonnegative,
sum to one, and the expected cost is bounded uniformly by the number of clauses.

The weights are supplied independently of a QAOA circuit. Computing those marginals from the
circuit, bounding the size of its relevant neighborhoods, and establishing a running time
remain outside the formalized identity.

## Main statements

* `Qatlib.Papers.QAOASupremacy16.Expectation.sum_marginal_eq_one`
  shows that the marginals of a probability weight sum to one.
* `Qatlib.Papers.QAOASupremacy16.Expectation.expectation_localCost_eq_sum_marginals`
  decomposes the expected cost into local expectations.
* `Qatlib.Papers.QAOASupremacy16.Expectation.exists_uniform_expectedCost_bound`
  gives a positive uniform bound outside `∀ p`.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAOASupremacy16.Expectation

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {n : ℕ}

/-- Restriction of a register to the coordinates in `s`. -/
def restrict (s : Finset (Fin n)) (z : Reg n) : s → Bool :=
  fun i => z i.1

/-- The marginal mass of the local assignment `w` on the coordinate set `s`: the total weight of
the registers whose restriction to `s` is `w`. -/
noncomputable def marginal (p : Reg n → ℝ) (s : Finset (Fin n)) (w : s → Bool) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z => restrict s z = w), p z

/-- Decomposition of a weighted composition into fibers: the weighted average of `q ∘ g` equals
the sum of the fiber masses times the values of `q`. -/
theorem sum_mul_comp_fiberwise {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (q : β → ℝ) (g : α → β) :
    ∑ x, p x * q (g x)
      = ∑ y, (∑ x ∈ Finset.univ.filter (fun x => g x = y), p x) * q y := by
  classical
  calc ∑ x, p x * q (g x)
      = ∑ x, ∑ y, if g x = y then p x * q y else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ y, ∑ x, if g x = y then p x * q y else 0 := Finset.sum_comm
    _ = ∑ y, (∑ x ∈ Finset.univ.filter (fun x => g x = y), p x) * q y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_filter, Finset.sum_mul]

/-- The expectation of a clause that depends only on the coordinates in `s` is the sum over local
assignments of the marginal mass times the clause value. -/
theorem expectation_local_clause (p : Reg n → ℝ) (s : Finset (Fin n))
    (c : (s → Bool) → ℝ) :
    ∑ z, p z * c (restrict s z)
      = ∑ w : s → Bool, marginal p s w * c w :=
  sum_mul_comp_fiberwise p c (restrict s)

variable {α : Type*} [Fintype α]

/-- The cost of a sum of local clauses, where the support of clause `a` is
`support a` and its local value is the indicator of `clause a`. -/
noncomputable def localCost (support : α → Finset (Fin n))
    (clause : ∀ a : α, (support a → Bool) → Bool) (z : Reg n) : ℝ :=
  ∑ a, if clause a (restrict (support a) z) = true then 1 else 0

/-- The global expectation of a sum of local clauses is the sum, over clauses, of the local
expectations computed from the marginals on the clause supports. -/
theorem expectation_localCost_eq_sum_marginals (p : Reg n → ℝ)
    (support : α → Finset (Fin n))
    (clause : ∀ a : α, (support a → Bool) → Bool) :
    ∑ z, p z * localCost support clause z
      = ∑ a, ∑ w : support a → Bool,
          marginal p (support a) w *
            (if clause a w = true then 1 else 0) := by
  unfold localCost
  calc ∑ z, p z * ∑ a, (if clause a (restrict (support a) z) = true then 1 else 0)
      = ∑ z, ∑ a, p z * (if clause a (restrict (support a) z) = true then 1 else 0) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a, ∑ z, p z * (if clause a (restrict (support a) z) = true then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ a, ∑ w : support a → Bool,
          marginal p (support a) w * (if clause a w = true then 1 else 0) :=
        Finset.sum_congr rfl fun a _ =>
          expectation_local_clause p (support a)
            (fun w => if clause a w = true then 1 else 0)

/-- Marginal masses of nonnegative weights are nonnegative. -/
theorem marginal_nonneg (p : Reg n → ℝ) (hp : ∀ z, 0 ≤ p z) (s : Finset (Fin n))
    (w : s → Bool) : 0 ≤ marginal p s w :=
  Finset.sum_nonneg fun z _ => hp z

/-- The marginals of a probability weight sum to one. -/
theorem sum_marginal_eq_one (p : Reg n → ℝ) (h1 : ∑ z, p z = 1) (s : Finset (Fin n)) :
    ∑ w : s → Bool, marginal p s w = 1 := by
  classical
  unfold marginal
  rw [Finset.sum_fiberwise]
  exact h1

/-- A local cost is nonnegative. -/
theorem localCost_nonneg (support : α → Finset (Fin n))
    (clause : ∀ a : α, (support a → Bool) → Bool) (z : Reg n) :
    0 ≤ localCost support clause z :=
  Finset.sum_nonneg fun a _ => by split <;> norm_num

/-- A local cost is at most the number of clauses. -/
theorem localCost_le_card (support : α → Finset (Fin n))
    (clause : ∀ a : α, (support a → Bool) → Bool) (z : Reg n) :
    localCost support clause z ≤ (Fintype.card α : ℝ) := by
  unfold localCost
  calc (∑ a, if clause a (restrict (support a) z) = true then (1 : ℝ) else 0)
      ≤ ∑ _a : α, (1 : ℝ) :=
        Finset.sum_le_sum fun a _ => by split <;> norm_num
    _ = (Fintype.card α : ℝ) := by simp

/-- A probability-weighted local cost is at most the number of clauses. -/
theorem expectedCost_le_card (p : Reg n → ℝ) (hp : ∀ z, 0 ≤ p z)
    (h1 : ∑ z, p z = 1) (support : α → Finset (Fin n))
    (clause : ∀ a : α, (support a → Bool) → Bool) :
    ∑ z, p z * localCost support clause z ≤ (Fintype.card α : ℝ) := by
  calc ∑ z, p z * localCost support clause z
      ≤ ∑ z, p z * (Fintype.card α : ℝ) :=
        Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (localCost_le_card support clause z) (hp z)
    _ = (Fintype.card α : ℝ) := by
        rw [← Finset.sum_mul, h1, one_mul]

/-- The expected cost of any probability weight is bounded by one positive uniform constant,
placed outside the quantifier over the weight. -/
theorem exists_uniform_expectedCost_bound [Nonempty α]
    (support : α → Finset (Fin n))
    (clause : ∀ a : α, (support a → Bool) → Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Reg n → ℝ), (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      ∑ z, p z * localCost support clause z ≤ C :=
  ⟨(Fintype.card α : ℝ), by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance,
    fun p hp h1 => expectedCost_le_card p hp h1 support clause⟩

end Qatlib.Papers.QAOASupremacy16.Expectation
