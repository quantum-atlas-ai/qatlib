/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TableAccess.LookupCompile.FiniteTableAccessDefs
import Mathlib.Data.Nat.Bitwise

/-!
# Coherent compilation of finite table lookup

This module compiles finite Boolean expression families into a common `BooleanDAG` and proves
correctness and size bounds for enabled finite-table lookup expressions. The resulting
reflection circuit implements coherent XOR lookup with zero oracle queries and restores the
clean auxiliary wires.

The reversible compute-and-uncompute viewpoint follows the circuit framework of
[NielsenChuang2010]. The theorem `g3` also shows that applying the same lookup circuit twice
restores every embedded input state.

## Main statements

* `g1`: Boolean expression families compiled with a node-count bound
* `g2`: enabled lookup correctness and total expression size
* `g3`: coherent reflection compilation, resources, and involution on embedded states

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.TableAccess.LookupCompile
open Matrix
open scoped BigOperators
set_option autoImplicit false

/-- Appending a Boolean DAG node preserves the values of all existing wires. -/
private theorem snoc_old {m n : ℕ} (g : BooleanDAG m n) (node : BooleanNode (m+n))
    (x : Reg m) (i : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) i) = booleanDAGValue g x i := by
  change booleanDAGValue (g.snoc node) x i.castSucc = _
  simp only [booleanDAGValue, Fin.lastCases_castSucc]

/-- The final wire of a DAG with an appended node evaluates that node against the previous wire
values. -/
private theorem snoc_last {m n : ℕ} (g : BooleanDAG m n) (node : BooleanNode (m+n))
    (x : Reg m) :
    booleanDAGValue (g.snoc node) x (Fin.last (m+n)) = booleanNodeValue node (booleanDAGValue g x) := by
  simp only [booleanDAGValue]
  exact Fin.lastCases_last (n := m+n) (motive := fun _ => Bool)
    (last := booleanNodeValue node (booleanDAGValue g x)) (cast := booleanDAGValue g x)

/-- A Boolean DAG's input wires retain the supplied input values. -/
private theorem dag_input {m n : ℕ} (g : BooleanDAG m n) (x : Reg m) (i : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) i) = x i := by
  induction g with
  | nil => rfl
  | @snoc n g node ih => exact (snoc_old g node x _).trans ih

/-- A Boolean expression can be compiled by extending an existing DAG with at most its node
count, preserving existing wires and producing a wire with the expression's value. -/
private theorem compile_expr {m : ℕ} (e : Expr m) {n : ℕ} (g : BooleanDAG m n) :
    ∃ (k : ℕ) (h : BooleanDAG m k) (w : Fin (m+k)),
      ∃ (hnk : n ≤ k), k ≤ n + nodes e ∧
      (∀ (x : Reg m) (i : Fin (m+n)),
        booleanDAGValue h x (Fin.castLE (by omega) i) = booleanDAGValue g x i) ∧
      ∀ x : Reg m, booleanDAGValue h x w = eval e x := by
  induction e generalizing n with
  | var i =>
    refine ⟨n,g,Fin.castLE (by omega) i,le_rfl,by simp [nodes],?_,?_⟩
    · intro x j; rfl
    · intro x; exact dag_input g x i
  | constant b =>
    refine ⟨n+1,g.snoc (.constant b),Fin.last (m+n),by omega,by simp [nodes],?_,?_⟩
    · intro x i; exact snoc_old g _ x i
    · intro x; exact snoc_last g _ x
  | neg e ih =>
    obtain ⟨k,h,w,hnk,hk,hp,hw⟩ := ih g
    refine ⟨k+1,h.snoc (.neg w),Fin.last (m+k),by omega,by simp only [nodes]; omega,?_,?_⟩
    · intro x i
      exact (snoc_old h _ x (Fin.castLE (by omega) i)).trans (hp x i)
    · intro x
      rw [snoc_last]
      simpa only [booleanNodeValue,eval] using congrArg Bool.not (hw x)
  | xor a b ihA ihB =>
    obtain ⟨ka,ga,wa,hnka,hka,hpa,hwa⟩ := ihA g
    obtain ⟨kb,gb,wb,hkab,hkb,hpb,hwb⟩ := ihB ga
    let wa' : Fin (m+kb) := Fin.castLE (by omega) wa
    refine ⟨kb+1,gb.snoc (.xor wa' wb),Fin.last (m+kb),by omega,by simp only [nodes]; omega,?_,?_⟩
    · intro x i
      exact (snoc_old gb _ x (Fin.castLE (by omega) i)).trans
        ((hpb x (Fin.castLE (by omega) i)).trans (hpa x i))
    · intro x
      rw [snoc_last]
      simp only [booleanNodeValue,wa',hpb,hwa,hwb,eval]
  | conj a b ihA ihB =>
    obtain ⟨ka,ga,wa,hnka,hka,hpa,hwa⟩ := ihA g
    obtain ⟨kb,gb,wb,hkab,hkb,hpb,hwb⟩ := ihB ga
    let wa' : Fin (m+kb) := Fin.castLE (by omega) wa
    refine ⟨kb+1,gb.snoc (.conj wa' wb),Fin.last (m+kb),by omega,by simp only [nodes]; omega,?_,?_⟩
    · intro x i
      exact (snoc_old gb _ x (Fin.castLE (by omega) i)).trans
        ((hpb x (Fin.castLE (by omega) i)).trans (hpa x i))
    · intro x
      rw [snoc_last]
      simp only [booleanNodeValue,wa',hpb,hwa,hwb,eval]

/-- A finite family of Boolean expressions compiles into one DAG with at most the sum of their
node counts and an output wire computing each expression. -/
theorem g1 :
    ∀ (m o : ℕ) (es : Fin o → Expr m),
      ∃ (k : ℕ) (g : BooleanDAG m k) (out : Fin o → Fin (m+k)),
        k ≤ ∑ j, nodes (es j) ∧
        ∀ (x : Reg m) (j : Fin o), booleanDAGValue g x (out j) = eval (es j) x := by
  intro m o
  induction o with
  | zero =>
    intro es
    refine ⟨0,.nil,Fin.elim0,by simp,?_⟩
    intro x j; exact Fin.elim0 j
  | succ o ih =>
    intro es
    obtain ⟨n,g,out,hn,ho⟩ := ih (fun j => es j.castSucc)
    obtain ⟨k,h,w,hnk,hk,hp,hw⟩ := compile_expr (es (Fin.last o)) g
    refine ⟨k,h,Fin.lastCases w (fun j => Fin.castLE (by omega) (out j)),?_,?_⟩
    · rw [Fin.sum_univ_castSucc]
      omega
    · intro x j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.lastCases_last] using hw x
      · simpa only [Fin.lastCases_castSucc] using (hp x (out i)).trans (ho x i)

/-- The folded conjunction over an address-bit list is true exactly when all listed bits match
the row index. -/
private theorem matching_list (a b : ℕ) (s : Fin (2^a))
    (x : Reg (inputs a b)) (ls : List (Fin a)) :
    eval (ls.foldr (fun i z => Expr.conj
      (if s.val.testBit i.val then .var (addressWire a b i)
        else .neg (.var (addressWire a b i))) z) (.constant true)) x = true ↔
      ∀ i ∈ ls, x (addressWire a b i) = s.val.testBit i.val := by
  induction ls with
  | nil => simp [eval]
  | cons i ls ih =>
    cases ht : s.val.testBit i.val <;>
      simp [List.foldr_cons,eval,ht,ih, Bool.and_eq_true]

/-- The row-matching expression is true exactly when every address bit matches the row's binary
representation. -/
private theorem matching_true (a b : ℕ) (s : Fin (2^a)) (x : Reg (inputs a b)) :
    eval (matchExpr a b s) x = true ↔
      ∀ i : Fin a, x (addressWire a b i) = s.val.testBit i.val := by
  simpa only [matchExpr, List.mem_finRange, forall_const] using
    matching_list a b s x (List.finRange a)

/-- Two indices below `2 ^ a` are equal when their first `a` binary bits agree. -/
private theorem row_ext (a : ℕ) (r s : Fin (2^a))
    (h : ∀ i : Fin a, r.val.testBit i.val = s.val.testBit i.val) : r = s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < a
  · exact h ⟨i,hi⟩
  · have hp : 2^a ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (r.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (s.isLt.trans_le hp)]

/-- When the input address encodes row `r`, the matching expression for `s` evaluates to the
Boolean equality test `s = r`. -/
private theorem matching_value (a b : ℕ) (x : Reg (inputs a b))
    (r s : Fin (2^a))
    (hx : ∀ i : Fin a, x (addressWire a b i) = r.val.testBit i.val) :
    eval (matchExpr a b s) x = if s = r then true else false := by
  by_cases hs : s = r
  · subst s
    simpa using (matching_true a b r x).mpr hx
  · have hn : eval (matchExpr a b s) x ≠ true := by
      intro he
      have hm := (matching_true a b s x).mp he
      exact hs (row_ext a s r (fun i => (hm i).symm.trans (hx i)))
    cases he : eval (matchExpr a b s) x <;> simp_all

/-- A row-matching expression uses at most `2 * a + 1` nodes. -/
private theorem matching_nodes (a b : ℕ) (s : Fin (2^a)) :
    nodes (matchExpr a b s) ≤ 2*a+1 := by
  have h : ∀ ls : List (Fin a),
      nodes (ls.foldr (fun i z => Expr.conj
        (if s.val.testBit i.val then .var (addressWire a b i)
          else .neg (.var (addressWire a b i))) z) (.constant true)) ≤ 2*ls.length+1 := by
    intro ls
    induction ls with
    | nil => simp [nodes]
    | cons i ls ih =>
      cases ht : s.val.testBit i.val <;> simp only [List.foldr_cons,ht, Bool.false_eq_true,
        ↓reduceIte, nodes, List.length_cons] <;> omega
  simpa only [matchExpr, List.length_finRange] using h (List.finRange a)

/-- For a duplicate-free list of rows, the folded lookup expression returns the enabled selected
table bit when the addressed row is listed, and false otherwise. -/
private theorem lookup_list (a b : ℕ) (x : Reg (inputs a b))
    (r : Fin (2^a)) (j : Fin b)
    (hx : ∀ i : Fin a, x (addressWire a b i) = r.val.testBit i.val)
    (ls : List (Fin (2^a))) (hn : ls.Nodup) :
    eval (ls.foldr (fun s z => Expr.xor (.conj (.var (enableWire a b))
      (.conj (matchExpr a b s) (.var (tableWire a b s j)))) z) (.constant false)) x =
      if r ∈ ls then x (enableWire a b) && x (tableWire a b r j) else false := by
  induction ls with
  | nil => simp [eval]
  | cons s ls ih =>
    have hnot := (List.nodup_cons.mp hn).1
    have htail := (List.nodup_cons.mp hn).2
    rw [List.foldr_cons]
    simp only [eval, matching_value a b x r s hx, ih htail]
    by_cases hs : s = r
    · subst s
      simp [hnot]
    · simp [hs, Ne.symm hs]

/-- Each table lookup expression uses at most `1 + 2 ^ a * (2 * a + 5)` nodes. -/
private theorem lookup_nodes (a b : ℕ) (j : Fin b) :
    nodes (lookupExpr a b j) ≤ 1+(2^a)*(2*a+5) := by
  have h : ∀ ls : List (Fin (2^a)),
      nodes (ls.foldr (fun s z => Expr.xor (.conj (.var (enableWire a b))
        (.conj (matchExpr a b s) (.var (tableWire a b s j)))) z) (.constant false)) ≤
        1+ls.length*(2*a+5) := by
    intro ls
    induction ls with
    | nil => simp [nodes]
    | cons s ls ih =>
      have hm := matching_nodes a b s
      simp only [List.foldr_cons,nodes,List.length_cons]
      nlinarith
  simpa only [lookupExpr,List.length_finRange] using h (List.finRange (2^a))

/-- The lookup expressions return the enabled table bits at the encoded address, and their total
node count is at most `b * (1 + 2 ^ a * (2 * a + 5))`. -/
theorem g2 :
    ∀ (a b : ℕ),
      (∀ (x : Reg (inputs a b)) (r : Fin (2^a)) (j : Fin b),
        (∀ i : Fin a, x (addressWire a b i) = r.val.testBit i.val) →
        eval (lookupExpr a b j) x =
          (x (enableWire a b) && x (tableWire a b r j))) ∧
      (∑ j : Fin b, nodes (lookupExpr a b j)) ≤ b*(1+(2^a)*(2*a+5)) := by
  intro a b
  constructor
  · intro x r j hx
    simpa only [lookupExpr,List.mem_finRange,↓reduceIte] using
      lookup_list a b x r j hx (List.finRange (2^a)) (List.nodup_finRange _)
  · calc
      _ ≤ ∑ _j : Fin b, (1+(2^a)*(2*a+5)) := Finset.sum_le_sum (fun j _ => lookup_nodes a b j)
      _ = _ := by simp

/-- Finite table lookup possesses a legal reflection-compiled Boolean DAG with zero queries and
at most `30 * k + b` gates, implementing coherent XOR lookup with clean auxiliary wires.
Applying the same compiled circuit twice restores every embedded input state. -/
theorem g3 :
    ∀ (a b : ℕ),
      ∃ (k : ℕ) (g : BooleanDAG (inputs a b) k)
        (out : Fin b → Fin (inputs a b+k)),
        k ≤ b*(1+(2^a)*(2*a+5)) ∧
        reflectionLegal (booleanDAGSteps g out) ∧
        QueryCount (reflectionCompile (booleanDAGSteps g out)) = 0 ∧
        GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30*k+b ∧
        (∀ (ψ : QState (Reg (inputs a b) × Reg b)),
          Run (1 : Matrix (Reg (inputs a b+k+b)) (Reg (inputs a b+k+b)) ℂ)
            (reflectionCompile (booleanDAGSteps g out))
            (booleanDAGEmbed (inputs a b) k b ψ) =
            ∑ xy, ψ xy • Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (inputs a b) k b xy.1
              (fun j => xy.2 j ^^ eval (lookupExpr a b j) xy.1))) ∧
        (∀ (ψ : QState (Reg (inputs a b) × Reg b)),
          Run (1 : Matrix (Reg (inputs a b+k+b)) (Reg (inputs a b+k+b)) ℂ)
            ((reflectionCompile (booleanDAGSteps g out)) ++
             (reflectionCompile (booleanDAGSteps g out)))
            (booleanDAGEmbed (inputs a b) k b ψ) =
            booleanDAGEmbed (inputs a b) k b ψ) := by
  intro a b
  obtain ⟨k,g,out,hk,hval⟩ := g1 (inputs a b) b (lookupExpr a b)
  have hr := boolean_dag_resources g out
  have hout (x : Reg (inputs a b)) (y : Reg b) :
      booleanDAGOutput g out x y = (fun j => y j ^^ eval (lookupExpr a b j) x) := by
    funext j
    change (y j ^^ booleanDAGValue g x (out j)) = _
    rw [hval]
  have hinv (x : Reg (inputs a b)) (y : Reg b) :
      booleanDAGOutput g out x (booleanDAGOutput g out x y) = y := by
    funext j
    change ((y j ^^ booleanDAGValue g x (out j)) ^^ booleanDAGValue g x (out j)) = y j
    simp only [Bool.xor_assoc,Bool.xor_self,Bool.xor_false]
  refine ⟨k,g,out,hk.trans (g2 a b).2,hr.1,hr.2.2.1,?_,?_,?_⟩
  · rw [hr.2.2.2]
    exact hr.2.1
  · intro ψ
    simpa only [hout] using boolean_dag_coherent g out ψ
  · intro ψ
    rw [run_append,boolean_dag_coherent]
    simp only [run_reflectionCompile_sum,run_reflectionCompile_smul,boolean_dag_basis,
      hinv,booleanDAGEmbed]

end Qatlib.Concepts.TableAccess.LookupCompile
