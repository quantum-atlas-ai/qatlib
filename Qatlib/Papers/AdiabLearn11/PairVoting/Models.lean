/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Image

@[expose] public section


/-! # Literal finite classifier data

The original classifier targets use a nonempty uniformly sampled finite domain.
The rational mass is totalized at the empty domain; all probability-one consumers
will supply nonemptiness. Binary incidence weights are preserved, and their
source pair-sum bookkeeping is kept as a separate structural condition.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AdiabLearn11.PairVoting.Models

/-- Uniform finite-event mass, with the old empty-domain totalization. -/
def Pr {V : Type*} [Fintype V] (s : Finset V) : ℚ :=
  (s.card : ℚ)/(Fintype.card V : ℚ)

/-- The actual event on which one weak classifier is correct. -/
def CorrectSet {V ι : Type*} [Fintype V]
    (c : ι → V → ℤ) (i : ι) : Finset V := Finset.univ.filter (fun x => c i x=1)

/-- The actual joint-correctness event of one classifier pair. -/
def pairMeet {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (p : ι × ι) : Finset V := CorrectSet c p.1 ∩ CorrectSet c p.2

/-- The old strict single-classifier advantage condition. -/
def Condition1 {V ι : Type*} [Fintype V]
    (c : ι → V → ℤ) (A : Finset ι) : Prop :=
  ∀ i ∈ A, (1/2 : ℚ)<Pr (CorrectSet c i)

/-- The exact old minimum-overlap identity for every selected pair. -/
def Condition2 {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) : Prop :=
  ∀ p ∈ J, Pr (pairMeet c p)=Pr (CorrectSet c p.1)+Pr (CorrectSet c p.2)-1

/-- The relaxed old overlap identity with its explicit per-pair error. -/
def Condition2a {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) (ε : ι × ι → ℚ) : Prop :=
  ∀ p ∈ J, Pr (pairMeet c p)=Pr (CorrectSet c p.1)+Pr (CorrectSet c p.2)-1+ε p

/-- The entire old directed-pair subtraction identity is retained. -/
def Condition3 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) : Prop :=
  (∑ p ∈ J, Pr (pairMeet c p))-
    (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (pairMeet c p ∩ pairMeet c q))=1

/-- The entire old extra-classifier cover identity is retained. -/
def Condition3a {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) (a : ι) : Prop :=
  (∑ p ∈ J, Pr (pairMeet c p))+Pr (CorrectSet c a)-
    (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q≠p), Pr (pairMeet c p ∩ pairMeet c q))-
    (∑ p ∈ J, Pr (CorrectSet c a ∩ pairMeet c p))=1

/-- The old integer sign convention sends zero votes to zero. -/
def sgn (t : ℤ) : ℤ := if 0<t then 1 else if t<0 then -1 else 0

/-- The actual integer sign vote of the weighted weak classifiers. -/
def Vote {V ι : Type*} [Fintype ι] (h : ι → V → ℤ) (w : ι → ℤ) (x : V) : ℤ :=
  sgn (∑ i, w i*h i x)

/-- Pointwise equality of the actual weighted vote with the target labels. -/
def Perfect {V ι : Type*} [Fintype ι] (h : ι → V → ℤ) (y : V → ℤ)
    (w : ι → ℤ) : Prop := ∀ x, Vote h w x=y x

/-- The exact binary union-incidence weights of the old pair model. -/
def pairWeight {ι : Type*} [DecidableEq ι] (J : Finset (ι × ι)) : ι → ℤ :=
  fun i => if i ∈ J.image Prod.fst ∪ J.image Prod.snd then 1 else 0

/-- Binary union incidence with the additional old stand-alone classifier. -/
def pairWeightA {ι : Type*} [DecidableEq ι] (J : Finset (ι × ι)) (a : ι) : ι → ℤ :=
  fun i => if i ∈ J.image Prod.fst ∪ J.image Prod.snd ∪ {a} then 1 else 0

/-- The actual lower mass bound on strictly positive weighted correctness. -/
def EpsPerfect {V ι : Type*} [Fintype V] [Fintype ι]
    (c : ι → V → ℤ) (w : ι → ℤ) (ε : ℚ) : Prop :=
  1-ε ≤ Pr (Finset.univ.filter (fun x => 0<∑ i, w i*c i x))

end Qatlib.Papers.AdiabLearn11.PairVoting.Models
