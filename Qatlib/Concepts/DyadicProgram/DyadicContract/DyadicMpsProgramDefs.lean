/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Log
import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
namespace Qatlib.Concepts.DyadicProgram.DyadicContract
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

abbrev GI := ℤ×ℤ
def add (x y : GI) : GI := (x.1+y.1,x.2+y.2)
def mul (x y : GI) : GI := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1)
noncomputable def decode (p : ℕ) (z : GI) : ℂ := ((z.1:ℂ)+(z.2:ℂ)*Complex.I)/(2:ℂ)^p

def dot {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) (j : Fin D) : GI :=
  (List.ofFn (fun i : Fin D => mul (v i) (A i j))).foldl add (0,0)
def row {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) : Fin D→GI := fun j=>dot v A j

def initial (D : ℕ) : Fin D→GI := fun i=>if i.val=0 then (1,0) else (0,0)
def run {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) : Fin D→GI := As.foldl row (initial D)

def scalar {D : ℕ} (hD : 0 < D) (As : List (Matrix (Fin D) (Fin D) GI)) : GI := run As ⟨0,hD⟩
noncomputable def matrixWord {D : ℕ} (p : ℕ) (As : List (Matrix (Fin D) (Fin D) GI)) : Matrix (Fin D) (Fin D) ℂ :=
  (As.map fun A=>fun i j=>decode p (A i j)).prod

structure Counted (α : Type) where
 value : α
 muls : ℕ
 adds : ℕ

def dotCounted {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) (j : Fin D) : Counted GI :=
  (List.ofFn (fun i : Fin D=>(v i,A i j))).foldl
    (fun s xy=>⟨add s.value (mul xy.1 xy.2),s.muls+4,s.adds+4⟩) ⟨(0,0),0,0⟩

def rowCounted {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) : Counted (Fin D→GI) :=
  let ds := List.ofFn (fun j : Fin D=>dotCounted v A j)
  ⟨fun j=>(ds[j.val]?.getD ⟨(0,0),0,0⟩).value,(ds.map Counted.muls).sum,(ds.map Counted.adds).sum⟩

def runCounted {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) : Counted (Fin D→GI) :=
  As.foldl (fun s A=>let t:=rowCounted s.value A;⟨t.value,s.muls+t.muls,s.adds+t.adds⟩) ⟨initial D,0,0⟩

end Qatlib.Concepts.DyadicProgram.DyadicContract
