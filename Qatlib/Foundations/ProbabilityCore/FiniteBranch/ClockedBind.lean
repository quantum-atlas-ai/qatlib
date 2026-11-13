/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedReturns

/-!
# Sequential composition of clocked programs

This module defines `bindCode` and the structural predicate `NoSave`, which excludes changes to
the stored candidate. It proves composition laws for return values and fees, and shows that a
program without save nodes preserves the initial candidate; such finite sampling semantics
supports adaptive quantum algorithms [AticiServedio2007].

## Main statements

* `valueLaw_bindCode`: Sequential composition follows PMF bind when the first program has no
  saves.
* `returns_bindCode`: Return specifications compose by adding fees.
* `noSave_run_best`: A program without saves leaves the stored candidate unchanged.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode

/-- Sequential composition of clocked programs, replacing each return of the first program by
its continuation. -/
def bindCode {I α β : Type} : Code I α → (α → Code I β) → Code I β
  | .ret a, f => f a
  | .pay n c, f => .pay n (bindCode c f)
  | .draw m p c, f => .draw m p (fun i => bindCode (c i) f)
  | .save i c, f => .save i (fun current => bindCode (c current) f)

/-- The structural predicate that a clocked program contains no save nodes. -/
def NoSave {I α : Type} : Code I α → Prop
  | .ret _ => True
  | .pay _ c => NoSave c
  | .draw _ _ c => ∀ i,NoSave (c i)
  | .save _ _ => False

/-- Mapping return values preserves and reflects the absence of save nodes. -/
theorem noSave_mapCode {I α β : Type} (f : α → β) (c : Code I α) :
    NoSave (mapCode f c) ↔ NoSave c := by
  induction c with
  | ret a => rfl
  | pay n c ih => exact ih
  | draw m p c ih => simp only [mapCode,NoSave,ih]
  | save i c ih => rfl

/-- A finite draw contains no save nodes exactly when every continuation contains no save nodes. -/
theorem noSave_drawF {I α Ω : Type} [Fintype Ω] (p : PMF Ω) (f : Ω → Code I α) :
    NoSave (drawF p f) ↔ ∀ a,NoSave (f a) := by
  constructor
  · intro h a
    simpa only [Equiv.symm_apply_apply] using h (Fintype.equivFin Ω a)
  · intro h a
    exact h ((Fintype.equivFin Ω).symm a)

/-- Binding a program without save nodes to continuations without save nodes produces a program
without save nodes. -/
theorem noSave_bindCode {I α β : Type} (c : Code I α) (hc : NoSave c) (f : α → Code I β)
    (hf : ∀ a,NoSave (f a)) : NoSave (bindCode c f) := by
  induction c with
  | ret a => exact hf a
  | pay n c ih => exact ih hc
  | draw m p c ih => exact fun i => ih i (hc i)
  | save i c ih => exact False.elim hc

/-- If the first program has no save nodes, the value law of sequential composition is the PMF
bind of its value law with the continuation value laws at the initial candidate. -/
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

/-- Every branch of a budgeted run of a program without save nodes keeps `best` equal to the
initial candidate. -/
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

/-- If the first program has no save nodes, return specifications for it and its continuations
compose with the two fees added. -/
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
