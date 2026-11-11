/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAG

/-!
# Boolean expressions for finite table lookup

This module defines the Boolean expression language `Expr`, its evaluation `eval`, and its
computation-node count `nodes`. Variables contribute no computation nodes, while constants and
Boolean operations each contribute one. For background on classical and quantum computation, see
[KitaevShenVyalyi2002].

The input layout contains `a` address bits, a table with `2^a` rows of `b` bits, and one enable
bit. The wire selectors locate these inputs, `matchExpr` compares the address with a row index
using least-significant-bit-first indexing, and `lookupExpr` forms the enabled lookup of a
chosen output bit by XOR over all rows.

## Main definitions

* `Expr`, `eval`, `nodes`: Boolean expressions, their semantics, and their computation-node
  count.
* `inputs`, `addressWire`, `tableWire`, `enableWire`: the input size and wire layout.
* `matchExpr`: the conjunction testing whether the address equals a given row index.
* `lookupExpr`: the enabled table lookup expression for a given bit position.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.RitzPipeline
namespace Qatlib.Concepts.TableAccess.LookupCompile
open scoped BigOperators
set_option autoImplicit false
/-- Boolean expressions over `m` input variables, built from constants, negation, exclusive OR,
and conjunction. -/
inductive Expr (m : ℕ) where
  | var (i : Fin m)
  | constant (b : Bool)
  | neg (a : Expr m)
  | xor (a b : Expr m)
  | conj (a b : Expr m)
  deriving DecidableEq

/-- Evaluates a Boolean expression on an input register, interpreting its constructors as the
corresponding Boolean operations. -/
def eval {m : ℕ} : Expr m → Reg m → Bool
  | .var i, x => x i
  | .constant b, _ => b
  | .neg a, x => !(eval a x)
  | .xor a b, x => eval a x ^^ eval b x
  | .conj a b, x => eval a x && eval b x

/-- Counts computation nodes in an expression tree, assigning zero to variables and one to each
constant or Boolean operation. Repeated subexpressions are counted separately at each
occurrence. -/
def nodes {m : ℕ} : Expr m → ℕ
  | .var _ => 0
  | .constant _ => 1
  | .neg a => nodes a + 1
  | .xor a b => nodes a + nodes b + 1
  | .conj a b => nodes a + nodes b + 1

/-- The number `a + (2^a)*b + 1` of input bits for an `a`-bit address, a table of `2^a` rows of
`b` bits, and one enable bit. -/
def inputs (a b : ℕ) := a + (2^a)*b + 1

/-- The wire for address bit `i`, located at index `i.val` in the lookup input register. -/
def addressWire (a b : ℕ) (i : Fin a) : Fin (inputs a b) := ⟨i.val,by simp [inputs]; omega⟩
/-- The wire for bit `j` of table row `r`, located at index `a + r.val*b + j.val` after the
address bits. -/
def tableWire (a b : ℕ) (r : Fin (2^a)) (j : Fin b) : Fin (inputs a b) :=
  ⟨a+r.val*b+j.val,by
    have hr := r.isLt
    have hj := j.isLt
    have h := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hr)
    simp only [Nat.succ_mul] at h
    simp only [inputs]
    omega⟩
/-- The final input wire, at index `a + (2^a)*b`, carrying the enable bit for table lookup. -/
def enableWire (a b : ℕ) : Fin (inputs a b) := ⟨a+(2^a)*b,by simp [inputs]⟩

/-- The conjunction comparing each address bit with the corresponding binary digit of row index
`r`, with bit zero least significant. The empty conjunction is the constant true expression. -/
def matchExpr (a b : ℕ) (r : Fin (2^a)) : Expr (inputs a b) :=
  (List.finRange a).foldr (fun i z =>
    .conj (if r.val.testBit i.val then .var (addressWire a b i)
      else .neg (.var (addressWire a b i))) z) (.constant true)

/-- The Boolean expression for enabled lookup of bit `j` at the input address. It XORs over all
rows the conjunction of the enable bit, the row's address match, and that row's table bit
`j`. -/
def lookupExpr (a b : ℕ) (j : Fin b) : Expr (inputs a b) :=
  (List.finRange (2^a)).foldr (fun r z =>
    .xor (.conj (.var (enableWire a b))
      (.conj (matchExpr a b r) (.var (tableWire a b r j)))) z) (.constant false)
end Qatlib.Concepts.TableAccess.LookupCompile
