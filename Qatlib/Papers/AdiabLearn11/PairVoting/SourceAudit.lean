/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabLearn11.PairVoting.Models
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Rat.Defs

@[expose] public section


/-! # The missing pair-incidence bridge

The fixed source Eq41 uses binary weights of the union of pair indices, but
its proof sums all pair votes. These coincide for a matching, not for arbitrary
pairs. The nonmatching example below even has disjoint left/right index sets
and satisfies all actual finite Conditions1--3. It diagnoses the unqualified
pair interpretation; a source reading with a matching condition is not refuted.
Actual matching examples separately certify satisfiability of the old premises.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AdiabLearn11.PairVoting.SourceAudit
open Models

/-- Seven actual Boolean correctness functions on a complete five-bit domain. -/
def corr (i : Fin 7) (x : Fin 32) : ℤ :=
  if i.val=0 then (if x.val<20 then 1 else -1)
  else if i.val≤4 then (if 20≤x.val ∨ x.val/5+1=i.val then 1 else -1)
  else if i.val=5 then (if 20≤x.val ∨ x.val<10 then 1 else -1)
  else (if 10≤x.val then 1 else -1)

/-- Four pairs share index zero; a separate pair covers the remaining domain. -/
def pairs : Finset (Fin 7 × Fin 7) := {(0,1),(0,2),(0,3),(0,4),(5,6)}

/-- All exact printed finite conditions and left/right disjointness really hold. -/
theorem sourceInputs :
    (∀ i x, corr i x=1 ∨ corr i x=-1) ∧
    Condition1 corr Finset.univ ∧ Condition2 corr pairs ∧ Condition3 corr pairs ∧
    Disjoint (pairs.image Prod.fst) (pairs.image Prod.snd) := by
  unfold Condition1 Condition2 Condition3
  decide +kernel

/-- The actual binary classifier makes the wrong vote at a concrete input. -/
theorem voteFails : Vote corr (pairWeight pairs) 0=-1 := by decide

/-- The required pair-sum bookkeeping fails despite the exact stated conditions. -/
theorem bookFails :
    (∑ i, pairWeight pairs i*corr i 0) ≠
      (∑ p ∈ pairs, (corr p.1 0+corr p.2 0)) := by decide

/-- Conditions1--3 plus left/right disjointness cannot supply the missing bridge. -/
theorem binaryFailure :
    ¬(∀ (c : Fin 7 → Fin 32 → ℤ) (J : Finset (Fin 7 × Fin 7)),
      (∀ i x, c i x=1 ∨ c i x=-1) → Condition1 c Finset.univ →
      Condition2 c J → Condition3 c J →
      Disjoint (J.image Prod.fst) (J.image Prod.snd) →
      Perfect c (fun _ => 1) (pairWeight J)) := by
  intro h
  obtain ⟨hr,h1,h2,h3,hd⟩ := sourceInputs
  have hv := h corr pairs hr h1 h2 h3 hd 0
  rw [voteFails] at hv
  norm_num at hv

/-- Six actual weak classifiers forming three disjoint correct-cover pairs. -/
def posCorr (i : Fin 6) (x : Fin 3) : ℤ :=
  if x.val=i.val/2 ∨
      x.val=(i.val/2+(if i.val%2=0 then 1 else 2))%3 then 1 else -1

/-- A genuine three-pair matching, with every index used once. -/
def matching : Finset (Fin 6 × Fin 6) := {(0,1),(2,3),(4,5)}

/-- Every old advantage, overlap, cover and bookkeeping premise is satisfiable. -/
theorem matchingGood :
    (∀ i x, posCorr i x=1 ∨ posCorr i x=-1) ∧
    Condition1 posCorr Finset.univ ∧ Condition2 posCorr matching ∧
    Condition3 posCorr matching ∧
    (∀ x, (∑ i, pairWeight matching i*posCorr i x)=
      (∑ p ∈ matching, (posCorr p.1 x+posCorr p.2 x))) := by
  unfold Condition1 Condition2 Condition3
  decide +kernel

/-- Two disjoint pairs used with a separate fifth classifier. -/
def twoPairs : Finset (Fin 6 × Fin 6) := {(0,1),(2,3)}

/-- The extra-classifier condition and its whole bookkeeping premise are satisfiable. -/
theorem extraGood : Condition1 posCorr Finset.univ ∧ Condition2 posCorr twoPairs ∧
    Condition3a posCorr twoPairs 4 ∧
    (∀ x, (∑ i, pairWeightA twoPairs 4 i*posCorr i x)=
      (∑ p ∈ twoPairs, (posCorr p.1 x+posCorr p.2 x))+posCorr 4 x) := by
  unfold Condition1 Condition2 Condition3a
  decide +kernel

end Qatlib.Papers.AdiabLearn11.PairVoting.SourceAudit
