/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedLaws
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open scoped Classical

def Returns {I α : Type} (cost : I → ℝ) (current : I) : Code I α → (α → ℕ → Prop) → Prop
  | .ret a, P => P a 0
  | .pay n c, P => Returns cost current c (fun a fee => P a (n+fee))
  | .draw _ _ c, P => ∀ i, Returns cost current (c i) P
  | .save i c, P => Returns cost (selectLower cost current i) (c (selectLower cost current i)) P

theorem returns_mono {I α : Type} (cost : I → ℝ) (current : I) (c : Code I α)
    {P Q : α → ℕ → Prop} (h : Returns cost current c P)
    (hpq : ∀ a fee,P a fee → Q a fee) : Returns cost current c Q := by
  induction c generalizing current P Q with
  | ret a => exact hpq a 0 h
  | pay n c ih => exact ih current h (fun a fee => hpq a (n+fee))
  | draw m p c ih => exact fun i => ih i current (h i) hpq
  | save i c ih => exact ih (selectLower cost current i) (selectLower cost current i) h hpq

theorem returns_mapCode {I α β : Type} (cost : I → ℝ) (current : I) (f : α → β)
    (c : Code I α) (P : β → ℕ → Prop) :
    Returns cost current (mapCode f c) P ↔ Returns cost current c (fun a fee => P (f a) fee) := by
  induction c generalizing current P with
  | ret a => rfl
  | pay n c ih => exact ih current (fun b fee => P b (n+fee))
  | draw m p c ih => simp only [mapCode,Returns,ih]
  | save i c ih => exact ih (selectLower cost current i) (selectLower cost current i) P

theorem returns_drawF {I α Ω : Type} [Fintype Ω] (cost : I → ℝ) (current : I)
    (p : PMF Ω) (f : Ω → Code I α) (P : α → ℕ → Prop) :
    Returns cost current (drawF p f) P ↔ ∀ a,Returns cost current (f a) P := by
  constructor
  · intro h a
    simpa only [Equiv.symm_apply_apply] using h (Fintype.equivFin Ω a)
  · intro h a
    exact h ((Fintype.equivFin Ω).symm a)

theorem returns_complete {I α : Type} (cost : I → ℝ) (current : I) (c : Code I α)
    (P : α → ℕ → Prop) (h : Returns cost current c P) :
    (complete cost current c).All (fun es => ∃ a,returnValue es=some a ∧ P a (transcriptCost es)) := by
  induction c generalizing current P with
  | ret a => exact ⟨a,rfl,h⟩
  | pay n c ih =>
    rw [complete,Tree.all_map]
    apply Tree.all_mono _ (ih current (fun a fee => P a (n+fee)) h)
    intro es he
    obtain ⟨a,ha,hp⟩:=he
    exact ⟨a,ha,hp⟩
  | draw m p c ih => exact fun i => ih i current P (h i)
  | save i c ih =>
    rw [complete,Tree.all_map]
    apply Tree.all_mono _ (ih (selectLower cost current i) (selectLower cost current i) P h)
    intro es he
    obtain ⟨a,ha,hp⟩:=he
    exact ⟨a,ha,hp⟩
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
