/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedReturns
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode

def bindCode {I α β : Type} : Code I α → (α → Code I β) → Code I β
  | .ret a, f => f a
  | .pay n c, f => .pay n (bindCode c f)
  | .draw m p c, f => .draw m p (fun i => bindCode (c i) f)
  | .save i c, f => .save i (fun current => bindCode (c current) f)

def NoSave {I α : Type} : Code I α → Prop
  | .ret _ => True
  | .pay _ c => NoSave c
  | .draw _ _ c => ∀ i,NoSave (c i)
  | .save _ _ => False

theorem noSave_mapCode {I α β : Type} (f : α → β) (c : Code I α) :
    NoSave (mapCode f c) ↔ NoSave c := by
  induction c with
  | ret a => rfl
  | pay n c ih => exact ih
  | draw m p c ih => simp only [mapCode,NoSave,ih]
  | save i c ih => rfl

theorem noSave_drawF {I α Ω : Type} [Fintype Ω] (p : PMF Ω) (f : Ω → Code I α) :
    NoSave (drawF p f) ↔ ∀ a,NoSave (f a) := by
  constructor
  · intro h a
    simpa only [Equiv.symm_apply_apply] using h (Fintype.equivFin Ω a)
  · intro h a
    exact h ((Fintype.equivFin Ω).symm a)

theorem noSave_bindCode {I α β : Type} (c : Code I α) (hc : NoSave c) (f : α → Code I β)
    (hf : ∀ a,NoSave (f a)) : NoSave (bindCode c f) := by
  induction c with
  | ret a => exact hf a
  | pay n c ih => exact ih hc
  | draw m p c ih => exact fun i => ih i (hc i)
  | save i c ih => exact False.elim hc

theorem valueLaw_bindCode {I α β : Type} (cost : I → ℝ) (current : I) (c : Code I α)
    (hc : NoSave c) (f : α → Code I β) :
    valueLaw cost current (bindCode c f)=
      (valueLaw cost current c).bind (fun a => valueLaw cost current (f a)) := by
  induction c generalizing current with
  | ret a => simp [bindCode,valueLaw]
  | pay n c ih => exact ih current hc
  | draw m p c ih =>
    simp only [bindCode,valueLaw,PMF.bind_bind]
    congr 1
    funext i
    exact ih i current (hc i)
  | save i c ih => exact False.elim hc

theorem noSave_run_best {I α : Type} (cost : I → ℝ) (current : I) (B : ℕ) (c : Code I α)
    (hc : NoSave c) : (run cost current B c).All (fun r => r.best=current) := by
  induction c generalizing current B with
  | ret a => simp [run,Tree.All]
  | pay n c ih =>
    rw [run]
    split_ifs with hn
    · rw [Tree.all_map]
      exact ih current (B-n) hc
    · simp [Tree.All]
  | draw m p c ih => exact fun i => ih i current B (hc i)
  | save i c ih => exact False.elim hc

theorem returns_bindCode {I α β : Type} (cost : I → ℝ) (current : I) (c : Code I α)
    (hc : NoSave c) (f : α → Code I β) (P : β → ℕ → Prop)
    (h : Returns cost current c (fun a fee => Returns cost current (f a) (fun b fee' => P b (fee+fee')))) :
    Returns cost current (bindCode c f) P := by
  induction c generalizing current P with
  | ret a => simpa only [bindCode,Returns,Nat.zero_add] using h
  | pay n c ih =>
    change Returns cost current (bindCode c f) (fun b fee => P b (n+fee))
    apply ih current hc (fun b fee => P b (n+fee))
    simpa only [Returns,Nat.add_assoc] using h
  | draw m p c ih => exact fun i => ih i current (hc i) P (h i)
  | save i c ih => exact False.elim hc
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
