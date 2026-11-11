/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems.FibreCounting
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Counting one-coordinate collision relations

The quantities `collDist`, `RelOne`, and `fibreMult` describe one-coordinate changes and the
numbers of fibres of each size. The sets `GainPairs` and `LossPairs` select updates that
respectively increase or decrease the fibre collision sum by one, and `card_gain_one` and
`card_loss_one` count these updates under the promise `FibresLeTwo`.

For inputs of size `4 * t`, `parity_gain_ge` and `parity_loss_ge` give quadratic lower bounds on
these update counts. The final inequality `parity_collision_ambainis` bounds the resulting
square-root relation parameter below by `(4 * t) / 12`, providing combinatorial estimates for
the parity-collision lower-bound setting of Theorem 8 in [BuhrmanEtAl2005].

## Main statements

* `card_gain_one`: the gain count is `fibreMult f 1 ^ 2 + 2 * fibreMult f 2 ^ 2 - N`.
* `card_loss_one`: the loss count is `2 * fibreMult f 2 * fibreMult f 0`.
* `gain_le_relCount` and `card_rel_at_x_le`: gain updates give distinct related functions, while
  at most `N` related functions can differ at a fixed coordinate.
* `parity_collision_ambainis`: the numerical relation parameter is at least `(4 * t) / 12` for
  the stated fibre and collision-sum hypotheses.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

/-- Count the inputs at which two functions `Fin N → Fin N` take different values. -/
def collDist (f g : Fin N → Fin N) : ℕ :=
  (Finset.univ.filter fun x => f x ≠ g x).card

/-- Require two functions `Fin N → Fin N` to differ at exactly one input. -/
def RelOne (f g : Fin N → Fin N) : Prop := collDist f g = 1

/-- Changing one function value to a different value produces a function related by `RelOne`.
This is a one-coordinate relation fact used in the collision-problem estimates of
[BuhrmanEtAl2005]. -/
theorem relOne_update (f : Fin N → Fin N) {x w : Fin N} (hw : w ≠ f x) :
    RelOne f (Function.update f x w) := by
  unfold RelOne collDist
  have hset : (Finset.univ.filter fun y => f y ≠ Function.update f x w y) = {x} := by
    ext y
    by_cases hy : y = x
    · subst hy
      simp [Function.update_self, Ne.symm hw]
    · simp [Function.update_apply, hy]
  rw [hset, Finset.card_singleton]

/-- If two functions differ at exactly one input and disagree at `x`, the second function is
obtained by updating the first at `x` to its second value. This identifies the related
inputs used in the collision-problem estimates of [BuhrmanEtAl2005]. -/
theorem eq_update_of_relOne {f g : Fin N → Fin N} {x : Fin N}
    (h : RelOne f g) (hx : f x ≠ g x) : g = Function.update f x (g x) := by
  unfold RelOne collDist at h
  have hxmem : x ∈ Finset.univ.filter (fun y => f y ≠ g y) := by
    simp [hx]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hax : a = x := by rw [ha] at hxmem; simpa [eq_comm] using hxmem
  have hfilter : (Finset.univ.filter fun y => f y ≠ g y) = {x} := by
    rw [ha, hax]
  funext y
  by_cases hy : y = x
  · subst hy
    simp
  · have hne : ¬ (f y ≠ g y) := by
      intro hd
      have hy' : y ∈ (Finset.univ.filter fun y => f y ≠ g y) := by simp [hd]
      rw [hfilter, Finset.mem_singleton] at hy'
      exact hy hy'
    have hfg : f y = g y := by
      by_contra hd
      exact hne hd
    rw [Function.update_of_ne hy]
    exact hfg.symm

/-- Count the values in `Fin N` whose fibre under `f` has cardinality `k`, including empty
fibres when `k = 0`. -/
def fibreMult (f : Fin N → Fin N) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun z => (fibre f z).card = k).card

/-- A finite sum equal to a fixed natural number `c` on a predicate and zero elsewhere is `c`
times the number of elements satisfying that predicate. -/
theorem sum_ite_const {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℕ) :
    (∑ x, if p x then c else 0) = c * (Finset.univ.filter p).card := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The number of elements satisfying a predicate in a finite type equals the sum of its
natural-valued indicator. -/
theorem card_filter_eq_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ z, (if p z then 1 else 0) := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

/-- A finite sum supported only at a specified element `c` equals the summand evaluated at `c`. -/
theorem sum_ite_eq_single {α : Type*} [Fintype α] [DecidableEq α]
    (c : α) (h : α → ℕ) : (∑ z, (if c = z then h z else 0)) = h c := by
  have h0 : ∀ b ∈ (Finset.univ : Finset α), b ≠ c →
      (if c = b then h b else 0) = 0 := by
    intro b _ hb
    rw [if_neg (Ne.symm hb)]
  have h1 : c ∉ (Finset.univ : Finset α) → (if c = c then h c else 0) = 0 := by
    intro hc
    exact absurd (Finset.mem_univ c) hc
  rw [Finset.sum_eq_single c h0 h1]
  simp

/-- Regroup a sum over inputs of a function of their fibre sizes as a sum over output values,
weighted by each fibre's cardinality. -/
theorem sum_comp_fibre_card (f : Fin N → Fin N) (g : ℕ → ℕ) :
    (∑ x, g (fibre f (f x)).card) = ∑ z, (fibre f z).card * g (fibre f z).card := by
  have hx : ∀ x, g (fibre f (f x)).card
      = ∑ z, (if f x = z then g (fibre f z).card else 0) := by
    intro x
    rw [← sum_ite_eq_single (f x) (fun z => g (fibre f z).card)]
  calc ∑ x, g (fibre f (f x)).card
      = ∑ x, ∑ z, (if f x = z then g (fibre f z).card else 0) :=
        Finset.sum_congr rfl fun x _ => hx x
    _ = ∑ z, ∑ x, (if f x = z then g (fibre f z).card else 0) := Finset.sum_comm
    _ = ∑ z, (fibre f z).card * g (fibre f z).card := by
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        simp [fibre]

/-- Under `FibresLeTwo`, the number of inputs lying in singleton fibres equals the number of
singleton fibres. -/
theorem card_singleton_elems (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    (Finset.univ.filter fun x => (fibre f (f x)).card = 1).card = fibreMult f 1 := by
  rw [card_filter_eq_sum]
  rw [sum_comp_fibre_card f (fun k => if k = 1 then 1 else 0)]
  rw [fibreMult, card_filter_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : (fibre f z).card = 1
  · simp [hz]
  · have hle := h2 z
    have hz0 : (fibre f z).card = 0 ∨ (fibre f z).card = 2 := by omega
    rcases hz0 with h0 | htwo
    · simp [h0]
    · simp [htwo]

/-- Under `FibresLeTwo`, the number of inputs lying in double fibres is twice the number of
double fibres. -/
theorem card_double_elems (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    (Finset.univ.filter fun x => (fibre f (f x)).card = 2).card = 2 * fibreMult f 2 := by
  rw [card_filter_eq_sum]
  rw [sum_comp_fibre_card f (fun k => if k = 2 then 1 else 0)]
  rw [fibreMult, card_filter_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : (fibre f z).card = 2
  · simp [hz]
  · have hle := h2 z
    have hz0 : (fibre f z).card = 0 ∨ (fibre f z).card = 1 := by omega
    rcases hz0 with h0 | hone
    · simp [h0]
    · simp [hone]

/-- When every fibre has size at most two, the numbers of empty, singleton, and double fibres
sum to the codomain size `N`. -/
theorem card_empty_add (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    fibreMult f 0 + fibreMult f 1 + fibreMult f 2 = N := by
  have hpoint : ∀ z, (if (fibre f z).card = 0 then (1 : ℕ) else 0)
      + (if (fibre f z).card = 1 then (1 : ℕ) else 0)
      + (if (fibre f z).card = 2 then (1 : ℕ) else 0) = 1 := by
    intro z
    have hz := h2 z
    have hcases : (fibre f z).card = 0 ∨ (fibre f z).card = 1 ∨ (fibre f z).card = 2 := by
      omega
    rcases hcases with h | h | h <;> rw [h] <;> norm_num
  have h0 : fibreMult f 0 = ∑ z, (if (fibre f z).card = 0 then (1 : ℕ) else 0) := by
    rw [fibreMult, card_filter_eq_sum]
  have h1 : fibreMult f 1 = ∑ z, (if (fibre f z).card = 1 then (1 : ℕ) else 0) := by
    rw [fibreMult, card_filter_eq_sum]
  have h2' : fibreMult f 2 = ∑ z, (if (fibre f z).card = 2 then (1 : ℕ) else 0) := by
    rw [fibreMult, card_filter_eq_sum]
  rw [h0, h1, h2', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc ∑ z, ((if (fibre f z).card = 0 then (1 : ℕ) else 0)
        + (if (fibre f z).card = 1 then (1 : ℕ) else 0)
        + (if (fibre f z).card = 2 then (1 : ℕ) else 0))
      = ∑ _z, (1 : ℕ) := Finset.sum_congr rfl fun z _ => hpoint z
    _ = N := by simp

/-- Under `FibresLeTwo`, the sum of each fibre size times the multiplicity of that size equals
the square of the singleton-fibre count plus twice the square of the double-fibre count. -/
theorem sum_fibreMult (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    (∑ z, (fibre f z).card * fibreMult f (fibre f z).card)
      = fibreMult f 1 * fibreMult f 1 + 2 * fibreMult f 2 * fibreMult f 2 := by
  have hpoint : ∀ z, (fibre f z).card * fibreMult f (fibre f z).card
      = (if (fibre f z).card = 1 then fibreMult f 1 else 0)
        + (if (fibre f z).card = 2 then 2 * fibreMult f 2 else 0) := by
    intro z
    have hz := h2 z
    have hcases : (fibre f z).card = 0 ∨ (fibre f z).card = 1 ∨ (fibre f z).card = 2 := by
      omega
    rcases hcases with h | h | h <;> rw [h] <;> norm_num
  calc ∑ z, (fibre f z).card * fibreMult f (fibre f z).card
      = ∑ z, ((if (fibre f z).card = 1 then fibreMult f 1 else 0)
          + (if (fibre f z).card = 2 then 2 * fibreMult f 2 else 0)) :=
        Finset.sum_congr rfl fun z _ => hpoint z
    _ = (∑ z, (if (fibre f z).card = 1 then fibreMult f 1 else 0))
          + (∑ z, (if (fibre f z).card = 2 then 2 * fibreMult f 2 else 0)) :=
        Finset.sum_add_distrib
    _ = fibreMult f 1 * fibreMult f 1 + 2 * fibreMult f 2 * fibreMult f 2 := by
        rw [sum_ite_const (fun z => (fibre f z).card = 1) (fibreMult f 1),
          sum_ite_const (fun z => (fibre f z).card = 2) (2 * fibreMult f 2)]
        simp only [fibreMult]

/-- Select updates `(x, w)` with `w ≠ f x` whose destination fibre and original fibre have equal
size; these updates increase `collSum` by one. -/
def GainPairs (f : Fin N → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => p.2 ≠ f p.1 ∧ (fibre f p.2).card = (fibre f (f p.1)).card

/-- Select updates `(x, w)` that move an input from a double fibre to an empty fibre; these
updates decrease `collSum` by one. -/
def LossPairs (f : Fin N → Fin N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p =>
    p.2 ≠ f p.1 ∧ (fibre f (f p.1)).card = 2 ∧ (fibre f p.2).card = 0

/-- Count pairs satisfying a predicate by summing, over their first coordinates, the numbers of
admissible second coordinates. -/
theorem card_filter_prod {P : Fin N × Fin N → Prop} [DecidablePred P] :
    (Finset.univ.filter P).card
      = ∑ x, (Finset.univ.filter fun w => P (x, w)).card := by
  rw [card_filter_eq_sum]
  simp_rw [card_filter_eq_sum]
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Under `FibresLeTwo`, the number of gain updates is the square of the singleton-fibre count
plus twice the square of the double-fibre count, minus `N` in natural arithmetic. This
supplies a relation-count estimate for [BuhrmanEtAl2005]. -/
theorem card_gain_one (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    (GainPairs f).card = fibreMult f 1 ^ 2 + 2 * fibreMult f 2 ^ 2 - N := by
  unfold GainPairs
  rw [card_filter_prod]
  have hinner : ∀ x, (Finset.univ.filter fun w =>
      w ≠ f x ∧ (fibre f w).card = (fibre f (f x)).card).card
      = (Finset.univ.filter fun w => (fibre f w).card = (fibre f (f x)).card).card - 1 := by
    intro x
    have hmem : f x ∈ Finset.univ.filter
        (fun w => (fibre f w).card = (fibre f (f x)).card) := by
      simp
    rw [← Finset.card_erase_of_mem hmem]
    congr 1
    ext w
    simp [Finset.mem_erase]
  simp_rw [hinner]
  have hA1 : ∀ x, 1 ≤ (Finset.univ.filter fun w =>
      (fibre f w).card = (fibre f (f x)).card).card := by
    intro x
    exact Finset.card_pos.mpr ⟨f x, by simp⟩
  have hsum : (∑ x, ((Finset.univ.filter fun w =>
        (fibre f w).card = (fibre f (f x)).card).card - 1))
      = (∑ x, (Finset.univ.filter fun w =>
        (fibre f w).card = (fibre f (f x)).card).card) - N := by
    rw [Finset.sum_tsub_distrib Finset.univ
      (f := fun x => (Finset.univ.filter fun w =>
        (fibre f w).card = (fibre f (f x)).card).card)
      (g := fun _ => 1) (fun x _ => hA1 x)]
    simp
  have hgroup : (∑ x, (Finset.univ.filter fun w =>
        (fibre f w).card = (fibre f (f x)).card).card)
      = ∑ z, (fibre f z).card * fibreMult f (fibre f z).card := by
    have h := sum_comp_fibre_card f (fun k => fibreMult f k)
    simpa [fibreMult] using h
  rw [hsum, hgroup, sum_fibreMult f h2]
  simp only [pow_two, mul_assoc]

/-- Under `FibresLeTwo`, the number of loss updates is twice the number of double fibres times
the number of empty fibres. This supplies a relation-count estimate for [BuhrmanEtAl2005]. -/
theorem card_loss_one (f : Fin N → Fin N) (h2 : FibresLeTwo f) :
    (LossPairs f).card = 2 * fibreMult f 2 * fibreMult f 0 := by
  unfold LossPairs
  have hset : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.2 ≠ f p.1 ∧ (fibre f (f p.1)).card = 2 ∧ (fibre f p.2).card = 0)
      = (Finset.univ.filter fun p : Fin N × Fin N =>
          (fibre f (f p.1)).card = 2 ∧ (fibre f p.2).card = 0) := by
    refine Finset.filter_congr ?_
    intro p _
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hne : p.2 ≠ f p.1 := by
        intro heq
        have hzero : (fibre f (f p.1)).card = 0 := by rw [← heq]; exact h2
        omega
      exact ⟨hne, h1, h2⟩
  rw [hset, card_filter_prod]
  have hinner : ∀ x, (Finset.univ.filter fun w =>
      (fibre f (f x)).card = 2 ∧ (fibre f w).card = 0).card
      = if (fibre f (f x)).card = 2 then fibreMult f 0 else 0 := by
    intro x
    by_cases hx : (fibre f (f x)).card = 2
    · rw [if_pos hx]
      have : (Finset.univ.filter fun w =>
          (fibre f (f x)).card = 2 ∧ (fibre f w).card = 0)
          = (Finset.univ.filter fun w => (fibre f w).card = 0) := by
        ext w
        simp [hx]
      rw [this, fibreMult]
    · rw [if_neg hx]
      have : (Finset.univ.filter fun w =>
          (fibre f (f x)).card = 2 ∧ (fibre f w).card = 0) = ∅ := by
        ext w
        simp [hx]
      rw [this, Finset.card_empty]
  simp_rw [hinner]
  rw [sum_ite_const (fun x => (fibre f (f x)).card = 2) (fibreMult f 0),
    card_double_elems f h2]
  ring

/-- Every update selected by `GainPairs` changes exactly one function value. -/
theorem gain_mem_rel {f : Fin N → Fin N} {p : Fin N × Fin N} (hp : p ∈ GainPairs f) :
    RelOne f (Function.update f p.1 p.2) := by
  have hw : p.2 ≠ f p.1 := (Finset.mem_filter.mp hp).2.1
  exact relOne_update f hw

/-- Every update selected by `GainPairs` increases the fibre collision sum by exactly one. -/
theorem gain_collSum {f : Fin N → Fin N} {p : Fin N × Fin N} (hp : p ∈ GainPairs f) :
    collSum (Function.update f p.1 p.2) = collSum f + 1 := by
  have hw : p.2 ≠ f p.1 := (Finset.mem_filter.mp hp).2.1
  have heq : (fibre f p.2).card = (fibre f (f p.1)).card := (Finset.mem_filter.mp hp).2.2
  have h := collSum_update_delta f p.1 p.2 hw
  rw [heq] at h
  have hn : (((fibre f (f p.1)).card : ℤ) - (((fibre f (f p.1)).card : ℤ) - 1)) = 1 := by ring
  have h2 : (collSum (Function.update f p.1 p.2) : ℤ) - (collSum f : ℤ) = 1 := by
    rw [h]; exact hn
  have : (collSum (Function.update f p.1 p.2) : ℤ) = (collSum f : ℤ) + 1 := by omega
  exact_mod_cast this

/-- Every update selected by `LossPairs` decreases the fibre collision sum by exactly one. -/
theorem loss_collSum {f : Fin N → Fin N} {p : Fin N × Fin N} (hp : p ∈ LossPairs f) :
    collSum (Function.update f p.1 p.2) + 1 = collSum f := by
  have hp' := Finset.mem_filter.mp hp
  have hw : p.2 ≠ f p.1 := hp'.2.1
  have hz2 : (fibre f (f p.1)).card = 2 := hp'.2.2.1
  have hw0 : (fibre f p.2).card = 0 := hp'.2.2.2
  have h := collSum_update_delta f p.1 p.2 hw
  rw [hz2, hw0] at h
  have h2 : (collSum (Function.update f p.1 p.2) : ℤ) - (collSum f : ℤ) = -1 := by
    rw [h]; norm_num
  have : (collSum (Function.update f p.1 p.2) : ℤ) + 1 = (collSum f : ℤ) := by omega
  exact_mod_cast this

/-- The number of gain updates is at most the number of functions differing at exactly one input
and having collision sum one greater. This is a relation-count comparison used in the
collision setting of [BuhrmanEtAl2005]. -/
theorem gain_le_relCount (f : Fin N → Fin N) :
    (GainPairs f).card ≤ (Finset.univ.filter fun g : Fin N → Fin N =>
      RelOne f g ∧ collSum g = collSum f + 1).card := by
  refine Finset.card_le_card_of_injOn (fun p : Fin N × Fin N => Function.update f p.1 p.2) ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, gain_mem_rel hp, gain_collSum hp⟩
  · intro p hp q hq heq
    have heq' : Function.update f p.1 p.2 = Function.update f q.1 q.2 := heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hpx : p.2 ≠ f p.1 := hp'.1
    have hqx : q.2 ≠ f q.1 := hq'.1
    have hdiff : ∀ (a b : Fin N), b ≠ f a →
        (Finset.univ.filter fun y => f y ≠ Function.update f a b y) = {a} := by
      intro a b hb
      ext y
      by_cases hy : y = a
      · subst hy
        simp [Function.update_self, Ne.symm hb]
      · simp [Function.update_apply, hy]
    have hp1 : (Finset.univ.filter fun y => f y ≠ Function.update f p.1 p.2 y)
        = {p.1} := hdiff p.1 p.2 hpx
    have hq1 : (Finset.univ.filter fun y => f y ≠ Function.update f q.1 q.2 y)
        = {q.1} := hdiff q.1 q.2 hqx
    have hsets : (Finset.univ.filter fun y => f y ≠ Function.update f p.1 p.2 y)
        = (Finset.univ.filter fun y => f y ≠ Function.update f q.1 q.2 y) := by
      rw [heq']
    rw [hp1, hq1] at hsets
    have hpq : p.1 = q.1 := by simpa using hsets
    have h2eq : p.2 = q.2 := by
      have hval := congrFun heq' p.1
      rw [Function.update_self] at hval
      rw [hpq] at hval
      rw [Function.update_self] at hval
      exact hval
    exact Prod.ext hpq h2eq

/-- For a fixed coordinate `x` and any additional predicate, at most `N` functions can differ
from `f` at exactly that coordinate while satisfying the predicate. This bounds a local
relation count in the collision setting of [BuhrmanEtAl2005]. -/
theorem card_rel_at_x_le (f : Fin N → Fin N) (P : (Fin N → Fin N) → Prop) [DecidablePred P]
    (x : Fin N) :
    (Finset.univ.filter fun g : Fin N → Fin N =>
      RelOne f g ∧ P g ∧ f x ≠ g x).card ≤ N := by
  have hle : (Finset.univ.filter fun g : Fin N → Fin N =>
      RelOne f g ∧ P g ∧ f x ≠ g x).card
      ≤ (Finset.univ : Finset (Fin N)).card := by
    refine Finset.card_le_card_of_injOn (fun g : Fin N → Fin N => g x) ?_ ?_
    · intro g _
      exact Finset.mem_univ _
    · intro g hg h hh heq
      have heq' : g x = h x := heq
      have hg' := (Finset.mem_filter.mp hg).2
      have hh' := (Finset.mem_filter.mp hh).2
      rw [eq_update_of_relOne hg'.1 hg'.2.2, eq_update_of_relOne hh'.1 hh'.2.2, heq']
  simpa using hle

/-- For an input of size `4 * t` with `t > 0`, fibre sizes at most two, and collision sum `t`,
the number of gain updates is at least `(4 * t)^2 / 8`. This is a combinatorial estimate for
the parity-collision argument in [BuhrmanEtAl2005]. -/
theorem parity_gain_ge (t : ℕ) (ht : 0 < t) (f : Fin (4 * t) → Fin (4 * t))
    (h2 : FibresLeTwo f) (hc : collSum f = t) :
    (4 * t : ℝ) ^ 2 / 8 ≤ ((GainPairs f).card : ℝ) := by
  have hS2 : fibreMult f 2 = t := by
    rw [fibreMult, ← collSum_eq_card_doubles f h2]
    exact hc
  have hS1 : fibreMult f 1 = 2 * t := by
    have h := card_singletons_add f h2
    have h2c : (Finset.univ.filter fun z => (fibre f z).card = 2).card = t := hS2
    rw [h2c] at h
    have hs : (Finset.univ.filter fun z => (fibre f z).card = 1).card = 2 * t := by
      omega
    exact hs
  have hnat : (GainPairs f).card + 4 * t = (2 * t) ^ 2 + 2 * t ^ 2 := by
    rw [card_gain_one f h2, hS1, hS2]
    have hle : 4 * t ≤ (2 * t) ^ 2 + 2 * t ^ 2 := by nlinarith
    omega
  have hreal : ((GainPairs f).card : ℝ) + 4 * t = (2 * t : ℝ) ^ 2 + 2 * (t : ℝ) ^ 2 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at this ⊢
    exact this
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hcard : ((GainPairs f).card : ℝ) = 6 * (t : ℝ) ^ 2 - 4 * t := by
    nlinarith [hreal]
  have hprod : (0 : ℝ) ≤ (t - 1) * t := mul_nonneg (by linarith) ht0
  nlinarith [hcard, hprod]

/-- For an input of size `4 * t` with `t > 0`, fibre sizes at most two, and collision sum `t +
1`, the number of loss updates is at least `(4 * t)^2 / 16`. This is a combinatorial
estimate for the parity-collision argument in [BuhrmanEtAl2005]. -/
theorem parity_loss_ge (t : ℕ) (ht : 0 < t) (g : Fin (4 * t) → Fin (4 * t))
    (h2 : FibresLeTwo g) (hc : collSum g = t + 1) :
    (4 * t : ℝ) ^ 2 / 16 ≤ ((LossPairs g).card : ℝ) := by
  have hS2 : fibreMult g 2 = t + 1 := by
    rw [fibreMult, ← collSum_eq_card_doubles g h2]
    exact hc
  have hS1 : fibreMult g 1 = 2 * t - 2 := by
    have h := card_singletons_add g h2
    have h2c : (Finset.univ.filter fun z => (fibre g z).card = 2).card = t + 1 := hS2
    rw [h2c] at h
    have hs : (Finset.univ.filter fun z => (fibre g z).card = 1).card = 2 * t - 2 := by
      omega
    exact hs
  have hS0 : fibreMult g 0 = t + 1 := by
    have h := card_empty_add g h2
    rw [hS1, hS2] at h
    omega
  have hnat : (LossPairs g).card = 2 * (t + 1) * (t + 1) := by
    rw [card_loss_one g h2, hS2, hS0]
  have hreal : ((LossPairs g).card : ℝ) = 2 * ((t : ℝ) + 1) * ((t : ℝ) + 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at this ⊢
    exact this
  nlinarith [hreal]

/-- Under the stated fibre promises and adjacent collision sums, the square root of the
gain-count times loss-count divided by `(4 * t)^2` is at least `(4 * t) / 12`. This bounds
the numerical relation parameter used in the parity-collision lower-bound argument of
[BuhrmanEtAl2005]. -/
theorem parity_collision_ambainis (t : ℕ) (ht : 0 < t)
    (f g : Fin (4 * t) → Fin (4 * t))
    (hf : FibresLeTwo f) (hcf : collSum f = t)
    (hg : FibresLeTwo g) (hcg : collSum g = t + 1) :
    (4 * t : ℝ) / 12 ≤ Real.sqrt
      (((GainPairs f).card : ℝ) * ((LossPairs g).card : ℝ)
        / ((4 * t : ℝ) * (4 * t : ℝ))) := by
  have hm : (4 * t : ℝ) ^ 2 / 8 ≤ ((GainPairs f).card : ℝ) :=
    parity_gain_ge t ht f hf hcf
  have hmp : (4 * t : ℝ) ^ 2 / 16 ≤ ((LossPairs g).card : ℝ) :=
    parity_loss_ge t ht g hg hcg
  have hN : (0 : ℝ) < 4 * t := by positivity
  have hm0 : (0 : ℝ) ≤ ((GainPairs f).card : ℝ) :=
    le_trans (by positivity) hm
  have hmp0 : (0 : ℝ) ≤ ((LossPairs g).card : ℝ) :=
    le_trans (by positivity) hmp
  have hprod : ((4 * t : ℝ) ^ 2 / 8) * ((4 * t : ℝ) ^ 2 / 16)
      ≤ ((GainPairs f).card : ℝ) * ((LossPairs g).card : ℝ) :=
    mul_le_mul hm hmp (by positivity) hm0
  have hden : (0 : ℝ) < (4 * t : ℝ) * (4 * t : ℝ) := by positivity
  have hratio : (4 * t : ℝ) ^ 2 / 128
      ≤ ((GainPairs f).card : ℝ) * ((LossPairs g).card : ℝ)
        / ((4 * t : ℝ) * (4 * t : ℝ)) := by
    rw [le_div_iff₀ hden]
    nlinarith [hprod, hN]
  have hsqrt : Real.sqrt ((4 * t : ℝ) ^ 2 / 128)
      ≤ Real.sqrt (((GainPairs f).card : ℝ) * ((LossPairs g).card : ℝ)
        / ((4 * t : ℝ) * (4 * t : ℝ))) := Real.sqrt_le_sqrt hratio
  have h12 : (4 * t : ℝ) / 12 ≤ Real.sqrt ((4 * t : ℝ) ^ 2 / 128) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [hN]
  linarith

end Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems
