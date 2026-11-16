/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabLearn11.PairVoting.Models
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Finite directed Bonferroni scores

The old cover condition subtracts every ordered distinct overlap. Its exact
pointwise score is `2*k-k^2`, hence at most one. The extra-set variant is
handled with its actual single extra-overlap subtraction as well.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AdiabLearn11.PairVoting.FiniteCover
open Models

/-- The rational incidence of an actual finite event. -/
def hit {V κ : Type*} [DecidableEq V] (E : κ → Finset V) (p : κ) (x : V) : ℚ :=
  if x ∈ E p then 1 else 0

/-- The exact old directed-overlap score at one sample. -/
def score {V κ : Type*} [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) (x : V) : ℚ :=
  (∑ p ∈ J, hit E p x)-
    ∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), hit E p x*hit E q x

/-- Every incidence is an actual zero-one value. -/
theorem hitSquare {V κ : Type*} [DecidableEq V] (E : κ → Finset V) (p : κ) (x : V) :
    (hit E p x)^2=hit E p x := by
  by_cases h : x ∈ E p <;> simp [hit,h]

/-- Every incidence is nonnegative. -/
theorem hitNonneg {V κ : Type*} [DecidableEq V] (E : κ → Finset V) (p : κ) (x : V) :
    0 ≤ hit E p x := by
  by_cases h : x ∈ E p <;> simp [hit,h]

/-- Removing the actual diagonal gives the entire ordered-pair moment. -/
theorem pairMoment {V κ : Type*} [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) (x : V) :
    (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), hit E p x*hit E q x)=
      (∑ p ∈ J, hit E p x)^2-(∑ p ∈ J, hit E p x) := by
  have hrow (p : κ) (hp : p ∈ J) :
      hit E p x*(∑ q ∈ J, hit E q x)=
        hit E p x+∑ q ∈ J.filter (fun q => q≠p), hit E p x*hit E q x := by
    have hf : J.filter (fun q => q≠p)=J.erase p := by ext q; simp [and_comm]
    rw [hf,Finset.mul_sum]
    have he := Finset.sum_erase_add (s := J) (f := fun q => hit E p x*hit E q x) hp
    have hs : hit E p x*hit E p x=hit E p x := by simpa only [pow_two] using hitSquare E p x
    rw [hs] at he
    linarith
  have hs := Finset.sum_congr rfl (fun p hp => hrow p hp)
  rw [← Finset.sum_mul,Finset.sum_add_distrib] at hs
  nlinarith

/-- The whole old directed score is bounded pointwise, without a cover premise. -/
theorem scoreBound {V κ : Type*} [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) (x : V) : score E J x ≤ 1 := by
  rw [score,pairMoment]
  nlinarith [sq_nonneg ((∑ p ∈ J, hit E p x)-1)]

/-- Event mass is the actual normalized finite incidence sum. -/
theorem massSum {V κ : Type*} [Fintype V] [DecidableEq V]
    (E : κ → Finset V) (p : κ) :
    Pr (E p)=(∑ x : V, hit E p x)/(Fintype.card V : ℚ) := by
  unfold Pr
  congr 1
  simp [hit]

/-- The complete finite probability expression is the mean of the actual score. -/
theorem scoreMean {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
    (E : κ → Finset V) (J : Finset κ) :
    (∑ p ∈ J, Pr (E p))-
        (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (E p ∩ E q))=
      (∑ x : V, score E J x)/(Fintype.card V : ℚ) := by
  have hi (p q : κ) : Pr (E p ∩ E q)=
      (∑ x : V, hit E p x*hit E q x)/(Fintype.card V : ℚ) := by
    rw [massSum (fun a : Unit => E p ∩ E q) ()]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : x ∈ E p <;> by_cases hq : x ∈ E q <;> simp [hit,hp,hq]
  simp_rw [massSum E,hi]
  simp_rw [← Finset.sum_div]
  rw [← sub_div]
  congr 1
  simp only [score,Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_comm
  · calc
      _ = ∑ p ∈ J, ∑ x : V,
          ∑ q ∈ J.filter (fun q => q≠p), hit E p x*hit E q x := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm

end Qatlib.Papers.AdiabLearn11.PairVoting.FiniteCover
