/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedBind
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.LawTransport

/-!
# Joint return-value and fee laws

The tree `paidTree` records each complete program return together with its total fee. This
module relates that joint law to value laws and return specifications, and proves a budgeted
composition formula when the first program has no save nodes; it supports finite adaptive
algorithm cost analysis [AticiServedio2007].

## Main statements

* `run_bind_paid_law`: Budgeted composition factors through the first program's joint value-fee
  law.
* `paidTree_deterministic_fee`: A fee determined by the return value makes the joint law a
  pushforward.
* `paidTree_mapCode_law`: Mapping values preserves the fee coordinate.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open scoped Classical

/-- The finite tree of complete return values paired with their accumulated natural-number
payment fees. -/
def paidTree {I α : Type} (cost : I → ℝ) (current : I) : Code I α → Tree (α×ℕ)
  | .ret a => .pure (a,0)
  | .pay n c => (paidTree cost current c).map (fun x => (x.1,n+x.2))
  | .draw m p c => .sample m p (fun i => paidTree cost current (c i))
  | .save i c => paidTree cost (selectLower cost current i) (c (selectLower cost current i))

/-- The first marginal of the joint return-value and fee law is the program's value law. -/
theorem paidTree_value_law {I α : Type} (cost : I → ℝ) (current : I) (c : Code I α) :
    (paidTree cost current c).law.map Prod.fst=valueLaw cost current c := by
  induction c generalizing current with
  | ret a => simp [paidTree,valueLaw,Tree.law,PMF.pure_map]
  | pay n c ih => simpa only [paidTree,Tree.law_map,PMF.map_comp,Function.comp_def] using! ih current
  | draw m p c ih =>
    simp only [paidTree,Tree.law,valueLaw,PMF.map_bind]
    congr 1
    funext i
    exact ih i current
  | save i c ih => exact ih (selectLower cost current i) (selectLower cost current i)

/-- A structural `Returns` specification holds on every leaf of `paidTree`. -/
theorem paidTree_returns {I α : Type} (cost : I → ℝ) (current : I) (c : Code I α)
    (P : α → ℕ → Prop) (h : Returns cost current c P) :
    (paidTree cost current c).All (fun x => P x.1 x.2) := by
  induction c generalizing current P with
  | ret a => exact h
  | pay n c ih =>
    rw [paidTree,Tree.all_map]
    exact ih current (fun a fee => P a (n+fee)) h
  | draw m p c ih => exact fun i => ih i current P (h i)
  | save i c ih => exact ih (selectLower cost current i) (selectLower cost current i) P h

/-- Continue from a value-fee pair using the remaining budget and adding the initial fee, or
return an interrupted result if that fee exceeds the budget. -/
def continuePaid {I α β : Type} (cost : I → ℝ) (current : I) (B : ℕ)
    (f : α → Code I β) (x : α×ℕ) : PMF (Result I β) :=
  if x.2≤B then (run cost current (B-x.2) (f x.1)).law.map (charge x.2)
  else PMF.pure ⟨none,B,current⟩

/-- When the first program has no save nodes, the law of budgeted sequential execution factors
through its joint value-fee law and `continuePaid`. -/
theorem run_bind_paid_law {I α β : Type} (cost : I → ℝ) (current : I) (B : ℕ)
    (c : Code I α) (hc : NoSave c) (f : α → Code I β) :
    (run cost current B (bindCode c f)).law=
      (paidTree cost current c).law.bind (continuePaid cost current B f) := by
  induction c generalizing current B with
  | ret a =>
    simp only [bindCode,paidTree,Tree.law,PMF.pure_bind,continuePaid,Nat.zero_le,
      if_true,Nat.sub_zero]
    have hzero : charge (I:=I) (α:=β) 0=id := by funext r; cases r; simp [charge]
    rw [hzero,PMF.map_id]
  | pay n c ih =>
    by_cases hn : n≤B
    · simp only [bindCode,run,hn,if_true,Tree.law_map,paidTree,PMF.bind_map]
      rw [ih current (B-n) hc,PMF.map_bind]
      apply congrArg (PMF.bind (paidTree cost current c).law)
      funext x
      by_cases hx : x.2≤B-n
      · have hnx : n+x.2≤B := by omega
        simp only [Function.comp_def,continuePaid,hx,hnx,if_true,PMF.map_comp]
        have he : B-n-x.2=B-(n+x.2) := by omega
        rw [he]
        congr 1
        funext r
        cases r
        simp [charge,Nat.add_assoc]
      · have hnx : ¬n+x.2≤B := by omega
        simp only [Function.comp_def,continuePaid,hx,hnx,if_false,PMF.pure_map]
        congr 1
        simp only [charge]
        congr 1
        omega
    · simp only [bindCode,run,hn,if_false,Tree.law,paidTree,Tree.law_map,PMF.bind_map]
      symm
      have he : (fun x : α×ℕ => continuePaid cost current B f (x.1,n+x.2))=
          fun _ => PMF.pure (⟨none,B,current⟩ : Result I β) := by
        funext x
        simp [continuePaid,show ¬n+x.2≤B by omega]
      change (paidTree cost current c).law.bind
          (fun x => continuePaid cost current B f (x.1,n+x.2))=_
      rw [he,PMF.bind_const]
  | draw m p c ih =>
    simp only [bindCode,run,Tree.law,paidTree,PMF.bind_bind]
    apply congrArg (PMF.bind p)
    funext i
    exact ih i current B (hc i)
  | save i c ih => exact False.elim hc

/-- If every complete return has fee `fee a`, the joint value-fee law is the value law mapped to
`(a, fee a)`. -/
theorem paidTree_deterministic_fee {I α : Type} (cost : I → ℝ) (current : I)
    (c : Code I α) (fee : α → ℕ) (h : Returns cost current c (fun a n => n=fee a)) :
    (paidTree cost current c).law=(valueLaw cost current c).map (fun a => (a,fee a)) := by
  have hall:=paidTree_returns cost current c _ h
  have he := Tree.law_map_congr (paidTree cost current c) id
    (fun x => (x.1,fee x.1)) (Tree.all_mono _ hall (fun x hx => by
      exact Prod.ext rfl hx))
  rw [PMF.map_id] at he
  rw [he,← paidTree_value_law cost current c,PMF.map_comp]
  rfl

/-- Mapping program return values maps the first coordinate of the joint value-fee law and
leaves the fee unchanged. -/
theorem paidTree_mapCode_law {I α β : Type} (cost : I → ℝ) (current : I)
    (f : α → β) (c : Code I α) :
    (paidTree cost current (mapCode f c)).law=
      (paidTree cost current c).law.map (fun x => (f x.1,x.2)) := by
  induction c generalizing current with
  | ret a => simp [mapCode,paidTree,Tree.law,PMF.pure_map]
  | pay n c ih =>
    simp only [mapCode,paidTree,Tree.law_map,ih,PMF.map_comp]
    rfl
  | draw m p c ih => simp only [mapCode,paidTree,Tree.law,ih,PMF.map_bind]
  | save i c ih => exact ih (selectLower cost current i) (selectLower cost current i)

end Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
