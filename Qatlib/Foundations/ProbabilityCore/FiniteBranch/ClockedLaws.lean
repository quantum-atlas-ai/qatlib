/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open scoped Classical

def drawF {I α Ω : Type} [Fintype Ω] (p : PMF Ω) (f : Ω → Code I α) : Code I α :=
  .draw (Fintype.card Ω) (p.map (Fintype.equivFin Ω))
    (fun i => f ((Fintype.equivFin Ω).symm i))

def mapCode {I α β : Type} (f : α → β) : Code I α → Code I β
  | .ret a => .ret (f a)
  | .pay n c => .pay n (mapCode f c)
  | .draw m p c => .draw m p (fun i => mapCode f (c i))
  | .save i c => .save i (fun current => mapCode f (c current))

def valueLaw {I α : Type} (cost : I → ℝ) (current : I) : Code I α → PMF α
  | .ret a => PMF.pure a
  | .pay _ c => valueLaw cost current c
  | .draw _ p c => p.bind (fun i => valueLaw cost current (c i))
  | .save i c => valueLaw cost (selectLower cost current i) (c (selectLower cost current i))

theorem valueLaw_drawF {I α Ω : Type} [Fintype Ω] (cost : I → ℝ) (current : I)
    (p : PMF Ω) (f : Ω → Code I α) :
    valueLaw cost current (drawF p f)=p.bind (fun a => valueLaw cost current (f a)) := by
  simp only [drawF,valueLaw,PMF.bind_map,Function.comp_def,Equiv.symm_apply_apply]

theorem valueLaw_mapCode {I α β : Type} (cost : I → ℝ) (current : I) (f : α → β) (c : Code I α) :
    valueLaw cost current (mapCode f c)=(valueLaw cost current c).map f := by
  induction c generalizing current with
  | ret a => simp only [mapCode,valueLaw,PMF.pure_map]
  | pay n c ih => exact ih current
  | draw m p c ih => simp only [mapCode,valueLaw,ih,PMF.map_bind]
  | save i c ih => exact ih (selectLower cost current i) (selectLower cost current i)

def returnValue {I α : Type} : List (Event I α) → Option α
  | [] => none
  | .ret a::_ => some a
  | .pay _::es => returnValue es
  | .save _::es => returnValue es

theorem complete_value_law {I α : Type} (cost : I → ℝ) (current : I) (c : Code I α) :
    (complete cost current c).law.map returnValue=(valueLaw cost current c).map some := by
  induction c generalizing current with
  | ret a => simp [complete,valueLaw,Tree.law,PMF.pure_map,returnValue]
  | pay n c ih => simpa only [complete,Tree.law_map,PMF.map_comp,Function.comp_def,returnValue,valueLaw] using ih current
  | draw m p c ih =>
    simp only [complete,valueLaw,Tree.law,PMF.map_bind]
    congr 1
    funext i
    exact ih i current
  | save i c ih =>
    simpa only [complete,Tree.law_map,PMF.map_comp,Function.comp_def,returnValue,valueLaw] using
      ih (selectLower cost current i) (selectLower cost current i)

def transcriptCost {I α : Type} : List (Event I α) → ℕ
  | [] => 0
  | .ret _::_ => 0
  | .pay n::es => n+transcriptCost es
  | .save _::es => transcriptCost es

def replayFull {I α : Type} (cost : I → ℝ) (current : I) : List (Event I α) → Result I α
  | [] => ⟨none,0,current⟩
  | .ret a::_ => ⟨some a,0,current⟩
  | .pay n::es => charge n (replayFull cost current es)
  | .save i::es => replayFull cost (selectLower cost current i) es

theorem replayFull_paid {I α : Type} (cost : I → ℝ) (current : I) (es : List (Event I α)) :
    (replayFull cost current es).paid=transcriptCost es := by
  induction es generalizing current with
  | nil => rfl
  | cons e es ih => cases e <;> simp [replayFull,transcriptCost,charge,ih]

theorem replay_complete {I α : Type} (cost : I → ℝ) (current : I) (B : ℕ)
    (es : List (Event I α)) (hcost : transcriptCost es≤B) :
    replay cost current B es=replayFull cost current es := by
  induction es generalizing current B with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | ret a => rfl
    | save i => exact ih _ _ hcost
    | pay n =>
      have hn : n≤B := by change n+transcriptCost es≤B at hcost; omega
      rw [replay,if_pos hn,replayFull]
      rw [ih current (B-n) (by change n+transcriptCost es≤B at hcost; omega)]
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
