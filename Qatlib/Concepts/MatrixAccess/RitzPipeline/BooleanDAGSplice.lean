/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSpliceData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdder
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

theorem boolean_node_rename_value {n k : ℕ} (r : Fin n → Fin k)
    (node : BooleanNode n) (x : Reg k) :
    booleanNodeValue (booleanNodeRename r node) x =
      booleanNodeValue node (fun i => x (r i)) := by
  cases node <;> rfl

private theorem splice_source_castSucc {M K m n : ℕ}
    (r : Fin m → Fin (M+K)) (i : Fin (m+n)) :
    booleanSpliceSource (n := n+1) r (Fin.castSucc i) =
      Fin.castSucc (booleanSpliceSource r i) := by
  apply Fin.ext
  by_cases hi : i.val < m <;> simp [booleanSpliceSource,hi]

private theorem splice_source_last {M K m n : ℕ}
    (r : Fin m → Fin (M+K)) :
    booleanSpliceSource (n := n+1) r (Fin.last (m+n)) =
      Fin.last (M+(K+n)) := by
  apply Fin.ext
  have hnot : ¬m+n < m := by omega
  simp [booleanSpliceSource,hnot,Nat.add_assoc]

theorem boolean_dag_splice_prefix {M K m n : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n) (x : Reg M)
    (i : Fin (M+K)) :
    booleanDAGValue (booleanDAGSplice g r h) x (Fin.castLE (by omega) i) =
      booleanDAGValue g x i := by
  induction h with
  | nil => rfl
  | @snoc n h node ih =>
    simp only [booleanDAGSplice,booleanDAGValue]
    have he : (Fin.castLE (by omega) i : Fin (M+(K+(n+1)))) =
        Fin.castSucc (Fin.castLE (by omega) i : Fin (M+(K+n))) := Fin.ext rfl
    rw [he,Fin.lastCases_castSucc]
    exact ih

theorem boolean_dag_splice_value {M K m n : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n) (x : Reg M)
    (i : Fin (m+n)) :
    booleanDAGValue (booleanDAGSplice g r h) x (booleanSpliceSource r i) =
      booleanDAGValue h (fun j => booleanDAGValue g x (r j)) i := by
  induction h with
  | nil =>
    have hi : i.val < m := i.isLt
    simp only [booleanDAGSplice,booleanSpliceSource,dif_pos hi,booleanDAGValue]
    rfl
  | @snoc n h node ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · calc
        booleanDAGValue (booleanDAGSplice g r (h.snoc node)) x
            (booleanSpliceSource r (Fin.last (m+n))) =
            booleanDAGValue (booleanDAGSplice g r (h.snoc node)) x
              (Fin.last (M+(K+n))) := congrArg _ (splice_source_last r)
        _ = _ := ?_
      simp only [booleanDAGSplice,booleanDAGValue,Fin.lastCases_last,
        boolean_node_rename_value]
      trans booleanNodeValue node (fun j =>
        booleanDAGValue (booleanDAGSplice g r h) x (booleanSpliceSource r j))
      · exact Fin.lastCases_last (n := M+(K+n)) (motive := fun _ => Bool)
          (last := booleanNodeValue node (fun j =>
            booleanDAGValue (booleanDAGSplice g r h) x (booleanSpliceSource r j)))
          (cast := booleanDAGValue (booleanDAGSplice g r h) x)
      · congr 1
        funext j
        exact ih j
    · rw [splice_source_castSucc (M := M) (K := K) (m := m) (n := n) r j]
      simp only [booleanDAGSplice,booleanDAGValue,Fin.lastCases_castSucc]
      exact ih j

theorem boolean_dag_append_adder_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) (x : Reg M) :
    booleanWordLSBValue (w+1) (fun j =>
      booleanDAGValue (booleanDAGAppendAdder g w a b) x
        (booleanDAGAppendAdderSelect w a b j)) =
      booleanWordLSBValue w (fun j => booleanDAGValue g x (a j)) +
        booleanWordLSBValue w (fun j => booleanDAGValue g x (b j)) := by
  have hv : (fun j => booleanDAGValue (booleanDAGAppendAdder g w a b) x
      (booleanDAGAppendAdderSelect w a b j)) =
      booleanWordAdderResult w (fun j => booleanDAGValue g x (a j))
        (fun j => booleanDAGValue g x (b j)) := by
    funext j
    unfold booleanDAGAppendAdder booleanDAGAppendAdderSelect
    rw [boolean_dag_splice_value]
    unfold booleanWordAdderResult booleanWordAdderInput
    congr 2
    funext s
    by_cases hs : s.val < w <;> simp [hs]
  rw [hv]
  exact boolean_word_adder_value w _ _

theorem boolean_dag_splice_resources {M K m n o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n)
    (out : Fin o → Fin (M+(K+n))) :
    reflectionLegal (booleanDAGSteps (booleanDAGSplice g r h) out) ∧
      (booleanDAGSteps (booleanDAGSplice g r h) out).length ≤ 30*(K+n)+o ∧
      QueryCount (reflectionCompile (booleanDAGSteps (booleanDAGSplice g r h) out)) = 0 ∧
      GateCount (reflectionCompile (booleanDAGSteps (booleanDAGSplice g r h) out)) =
        (booleanDAGSteps (booleanDAGSplice g r h) out).length :=
  boolean_dag_resources _ _

theorem boolean_dag_splice_basis {M K m n o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n)
    (out : Fin o → Fin (M+(K+n))) (x : Reg M) (y : Reg o) :
    Run (1 : Matrix (Reg (M+(K+n)+o)) (Reg (M+(K+n)+o)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanDAGSplice g r h) out))
      (Ket (booleanDAGInput M (K+n) o x y)) =
      Ket (booleanDAGInput M (K+n) o x
        (booleanDAGOutput (booleanDAGSplice g r h) out x y)) :=
  boolean_dag_basis _ _ _ _

theorem boolean_dag_splice_coherent {M K m n o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n)
    (out : Fin o → Fin (M+(K+n))) (ψ : QState (Reg M × Reg o)) :
    Run (1 : Matrix (Reg (M+(K+n)+o)) (Reg (M+(K+n)+o)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanDAGSplice g r h) out))
      (booleanDAGEmbed M (K+n) o ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput M (K+n) o xy.1
        (booleanDAGOutput (booleanDAGSplice g r h) out xy.1 xy.2)) :=
  boolean_dag_coherent _ _ _

end Qatlib.Concepts.MatrixAccess.RitzPipeline
