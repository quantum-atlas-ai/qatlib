/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.MatrixTensor
import Qatlib.Foundations.PureStateMath.Tensor
import Mathlib.LinearAlgebra.Matrix.Reindex
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GateVocabulary.GateVocab

open Matrix

def pauliYBool : Matrix Bool Bool ℂ :=
  fun i j => if i = j then 0 else if i then Complex.I else -Complex.I

def phaseS : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then Complex.I else 1)

def pauliBool (a : Fin 4) : Matrix Bool Bool ℂ :=
  if a.val = 0 then 1 else if a.val = 1 then Qatlib.Foundations.PureStateMath.PauliX else
    if a.val = 2 then pauliYBool else Qatlib.Foundations.PureStateMath.PauliZ

def pauliProductIndex (a b : Fin 4) : Fin 4 :=
  ⟨(a.val % 2 + b.val % 2) % 2 + 2 * ((a.val / 2 + b.val / 2) % 2),
    by fin_cases a <;> fin_cases b <;> decide⟩

def regOneBool : Qatlib.Foundations.PureStateMath.Reg 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool

def pauliProductPhase (a b : Fin 4) : ℂ :=
  if a.val = 0 ∨ b.val = 0 ∨ a.val = b.val then 1 else
    if (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 3) ∨
      (a.val = 3 ∧ b.val = 1) then Complex.I else -Complex.I

def toFinGate : Matrix Bool Bool ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ Qatlib.Foundations.PureStateMath.boolEquivFin2

def pauliFin (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := toFinGate (pauliBool a)
def pauliAxis (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliFin ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩
def hadamardFin : Matrix (Fin 2) (Fin 2) ℂ :=
    toFinGate Qatlib.Foundations.PureStateMath.Hadamard
def phaseSFin : Matrix (Fin 2) (Fin 2) ℂ := toFinGate phaseS

def swapGate : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  permMatrix (fun x => (x.2, x.1))

def toffoliUpdate {n : ℕ} (a b t : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.PureStateMath.Reg n :=
  Function.update x t (x t ^^ (x a && x b))

def toffoliGate {n : ℕ} (a b t : Fin n) : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ :=
  permMatrix (toffoliUpdate a b t)

end Qatlib.Concepts.GateVocabulary.GateVocab
