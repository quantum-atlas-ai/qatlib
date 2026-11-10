/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Basic
import Init.Data.Vector.InsertIdx
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable

structure Run (α : Type) where
  value : α
  work : ℕ
  cells : ℕ
  deriving Repr

structure TailPacket (α : Type) (n : ℕ) where
  head : α
  rest : List α
  rest_length : rest.length = n

namespace TailPacket
variable {α : Type} {n : ℕ}

def toList (p : TailPacket α n) : List α := p.head :: p.rest

@[simp] theorem toList_length (p : TailPacket α n) :
    p.toList.length = n+1 := by simp [toList,p.rest_length]

def prepend (p : TailPacket α n) (x : α) : TailPacket α (n+1) :=
  ⟨x,p.head :: p.rest,by simp [p.rest_length]⟩

def toVector (p : TailPacket α n) : Vector α (n+1) :=
  ⟨p.toList.toArray,by simp⟩

@[simp] theorem toVector_toList (p : TailPacket α n) :
    p.toVector.toList = p.toList := rfl

@[simp] theorem toVector_head (p : TailPacket α n) :
    p.toVector[0] = p.head := by simp [toVector,toList]

theorem toVector_prepend (p : TailPacket α n) (x : α) :
    (p.prepend x).toVector = p.toVector.insertIdx 0 x := by
  apply Vector.toList_inj.mp
  rw [Vector.toList_insertIdx]
  rfl

end TailPacket

structure Collection (α : Type) where
  value : α
  calls : ℕ
  pushes : ℕ

def collect {α : Type} : List α → Array α → Collection (Array α)
  | [], acc => ⟨acc,1,0⟩
  | x :: xs, acc =>
    let child := collect xs (acc.push x)
    ⟨child.value,child.calls+1,child.pushes+1⟩

theorem collect_spec {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).value.toList = acc.toList ++ xs ∧
    (collect xs acc).calls = xs.length+1 ∧
    (collect xs acc).pushes = xs.length := by
  induction xs generalizing acc with
  | nil => simp [collect]
  | cons x xs ih =>
    rcases ih (acc.push x) with ⟨hv,hc,hp⟩
    simp [collect,hv,hc,hp,List.append_assoc]

theorem collect_size {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).value.size = acc.size+xs.length := by
  have h := congrArg List.length (collect_spec xs acc).1
  simpa using h

def finish {α : Type} {n : ℕ} (p : TailPacket α n) :
    Collection (Vector α (n+1)) :=
  let xs := p.toList
  let out := collect xs (Array.emptyWithCapacity (n+1))
  ⟨⟨out.value,by simp [out,xs,collect_size]⟩,out.calls,out.pushes⟩

theorem finish_spec {α : Type} {n : ℕ} (p : TailPacket α n) :
    (finish p).value = p.toVector ∧
    (finish p).calls = n+2 ∧ (finish p).pushes = n+1 := by
  have h := collect_spec p.toList (Array.emptyWithCapacity (n+1))
  refine ⟨?_,?_,?_⟩
  · apply Vector.toList_inj.mp
    simpa [finish] using h.1
  · simpa [finish,Nat.add_assoc] using h.2.1
  · simpa [finish] using h.2.2

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable
