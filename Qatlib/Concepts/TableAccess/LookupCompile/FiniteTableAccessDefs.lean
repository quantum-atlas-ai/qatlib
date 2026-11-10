/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAG
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.RitzPipeline
namespace Qatlib.Concepts.TableAccess.LookupCompile
open scoped BigOperators
set_option autoImplicit false
inductive Expr (m : ℕ) where
  | var (i : Fin m)
  | constant (b : Bool)
  | neg (a : Expr m)
  | xor (a b : Expr m)
  | conj (a b : Expr m)
  deriving DecidableEq

def eval {m : ℕ} : Expr m → Reg m → Bool
  | .var i, x => x i
  | .constant b, _ => b
  | .neg a, x => !(eval a x)
  | .xor a b, x => eval a x ^^ eval b x
  | .conj a b, x => eval a x && eval b x

def nodes {m : ℕ} : Expr m → ℕ
  | .var _ => 0
  | .constant _ => 1
  | .neg a => nodes a + 1
  | .xor a b => nodes a + nodes b + 1
  | .conj a b => nodes a + nodes b + 1

def inputs (a b : ℕ) := a + (2^a)*b + 1

def addressWire (a b : ℕ) (i : Fin a) : Fin (inputs a b) := ⟨i.val,by simp [inputs]; omega⟩
def tableWire (a b : ℕ) (r : Fin (2^a)) (j : Fin b) : Fin (inputs a b) :=
  ⟨a+r.val*b+j.val,by
    have hr := r.isLt
    have hj := j.isLt
    have h := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hr)
    simp only [Nat.succ_mul] at h
    simp only [inputs]
    omega⟩
def enableWire (a b : ℕ) : Fin (inputs a b) := ⟨a+(2^a)*b,by simp [inputs]⟩

def matchExpr (a b : ℕ) (r : Fin (2^a)) : Expr (inputs a b) :=
  (List.finRange a).foldr (fun i z =>
    .conj (if r.val.testBit i.val then .var (addressWire a b i)
      else .neg (.var (addressWire a b i))) z) (.constant true)

def lookupExpr (a b : ℕ) (j : Fin b) : Expr (inputs a b) :=
  (List.finRange (2^a)).foldr (fun r z =>
    .xor (.conj (.var (enableWire a b))
      (.conj (matchExpr a b r) (.var (tableWire a b r j)))) z) (.constant false)
end Qatlib.Concepts.TableAccess.LookupCompile
