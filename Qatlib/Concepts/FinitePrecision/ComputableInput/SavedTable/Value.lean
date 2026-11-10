/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Data

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value

def gather {ι α : Type} (f : ι → α) : List ι → List α
  | [] => []
  | i::is => let child := f i; let tail := gather f is; child::tail

theorem gather_eq_map {ι α : Type} (f : ι → α) (is : List ι) :
    gather f is = is.map f := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [gather,List.map_cons,ih]

def collect {α : Type} : List α → Array α → Array α
  | [], acc => acc
  | x::xs, acc => collect xs (acc.push x)

theorem collect_toList {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).toList = acc.toList++xs := by
  induction xs generalizing acc with
  | nil => simp [collect]
  | cons x xs ih => simp [collect,ih,List.append_assoc]

theorem collect_size {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).size = acc.size+xs.length := by
  simpa using congrArg List.length (collect_toList xs acc)

def tabulate {α : Type} {n : ℕ} (is : List (Fin n))
    (hi : is = List.finRange n) (f : Fin n → α) : Vector α n :=
  let saved := gather f is
  ⟨collect saved (Array.emptyWithCapacity n),by
    simp [saved,collect_size,gather_eq_map,hi]⟩

theorem tabulate_eq {α : Type} {n : ℕ} (is : List (Fin n))
    (hi : is = List.finRange n) (f : Fin n → α) :
    tabulate is hi f = Vector.ofFn f := by
  apply Vector.toList_inj.mp
  simp [tabulate,collect_toList,gather_eq_map,hi,Vector.toList_ofFn,List.ofFn_eq_map]

abbrev Packet := Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.TailPacket

def Packet.prepend {α : Type} {n : ℕ} (p : Packet α n) (x : α) : Packet α (n+1) :=
  Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.TailPacket.prepend p x

def finish {α : Type} {n : ℕ} (p : Packet α n) : Vector α (n+1) :=
  ⟨collect (p.head::p.rest) (Array.emptyWithCapacity (n+1)),by
    simp [collect_size,p.rest_length]⟩

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value
