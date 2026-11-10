/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedAdditionData
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

def booleanMuxSources {α : Type*} (H : ℕ) (a b : Fin H → α) (c : α) : Fin (2*H+1) → α :=
  fun j => if hj : j.val < H then a ⟨j.val,hj⟩
    else if hk : j.val < 2*H then b ⟨j.val-H,by omega⟩ else c

def booleanSelectFourRaw (H K : ℕ) (row : Fin 4) (j : Fin H) : Fin (4*H+2+K) :=
  ⟨row.val*H+j.val,by have := row.isLt; have := j.isLt; nlinarith⟩
def booleanSelectFourHigh (H K : ℕ) : Fin (4*H+2+K) := ⟨4*H,by omega⟩
def booleanSelectFourLow (H K : ℕ) : Fin (4*H+2+K) := ⟨4*H+1,by omega⟩

def booleanSelectFourFirstInputs (H : ℕ) : Fin (2*H+1) → Fin (4*H+2+0) :=
  booleanMuxSources H (booleanSelectFourRaw H 0 1) (booleanSelectFourRaw H 0 0) (booleanSelectFourLow H 0)
def booleanSelectFourFirst (H : ℕ) : BooleanDAG (4*H+2) (0+3*H) :=
  booleanDAGSplice .nil (booleanSelectFourFirstInputs H) (booleanWordMuxDAG H)
def booleanSelectFourSecondInputs (H : ℕ) : Fin (2*H+1) → Fin (4*H+2+(0+3*H)) :=
  booleanMuxSources H (booleanSelectFourRaw H (0+3*H) 3) (booleanSelectFourRaw H (0+3*H) 2)
    (booleanSelectFourLow H (0+3*H))
def booleanSelectFourSecond (H : ℕ) : BooleanDAG (4*H+2) ((0+3*H)+3*H) :=
  booleanDAGSplice (booleanSelectFourFirst H) (booleanSelectFourSecondInputs H) (booleanWordMuxDAG H)

def booleanSelectFourFinalInputs (H : ℕ) : Fin (2*H+1) → Fin (4*H+2+((0+3*H)+3*H)) :=
  booleanMuxSources H
    (fun j => booleanSpliceSource (booleanSelectFourSecondInputs H) (booleanWordMuxSelect H j))
    (fun j => Fin.castLE (by omega)
      (booleanSpliceSource (booleanSelectFourFirstInputs H) (booleanWordMuxSelect H j)))
    (booleanSelectFourHigh H ((0+3*H)+3*H))
def booleanSelectFourDAG (H : ℕ) : BooleanDAG (4*H+2) (((0+3*H)+3*H)+3*H) :=
  booleanDAGSplice (booleanSelectFourSecond H) (booleanSelectFourFinalInputs H) (booleanWordMuxDAG H)
def booleanSelectFourOutput (H : ℕ) : Fin H → Fin (4*H+2+(((0+3*H)+3*H)+3*H)) :=
  fun j => booleanSpliceSource (booleanSelectFourFinalInputs H) (booleanWordMuxSelect H j)

def booleanSelectFourInput (H : ℕ) (a : Fin 4 → Reg H) (high low : Bool) : Reg (4*H+2) :=
  fun j => if hj : j.val < 4*H then a ⟨j.val/H,by
    by_cases hh : H=0
    · subst H; omega
    · exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hh)).mpr (by omega)⟩
      ⟨j.val%H,by
        by_cases hh : H=0
        · subst H; omega
        · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hh)⟩
    else if j.val=4*H then high else low

def booleanSelectFourWord (H : ℕ) (x : Reg (4*H+2)) (row : Fin 4) : Reg H :=
  fun j => x (booleanSelectFourRaw H 0 row j)
def booleanSelectFourResult (H : ℕ) (x : Reg (4*H+2)) : Reg H :=
  fun j => booleanDAGValue (booleanSelectFourDAG H) x (booleanSelectFourOutput H j)
def booleanSelectFourRow (high low : Bool) : Fin 4 :=
  if high then (if low then 3 else 2) else (if low then 1 else 0)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
