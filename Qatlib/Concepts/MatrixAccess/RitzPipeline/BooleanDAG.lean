/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGNodes
import Qatlib.Concepts.CircuitImpl.ReflectionCompile.CleanZeroReflection
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

private def dagFilled {m n L : ℕ} (g : BooleanDAG m n) (_h : m+n ≤ L)
    (x : Reg m) (s : Reg L) : Reg L := fun w =>
  if hw : w.val < m+n then booleanDAGValue g x ⟨w.val,hw⟩ else s w

private theorem dag_filled_source {m n L : ℕ} (g : BooleanDAG m n)
    (h : m+n ≤ L) (x : Reg m) (s : Reg L) (i : Fin (m+n)) :
    dagFilled g h x s (Fin.castLE h i)=booleanDAGValue g x i := by
  simp [dagFilled,i.isLt]

private theorem dag_compute_into_basis {m n L : ℕ} (g : BooleanDAG m n)
    (h : m+n ≤ L) (x : Reg m) (s : Reg L)
    (hx : ∀i:Fin m,s (Fin.castLE (by omega) i)=x i)
    (hw : ∀i:Fin L,m ≤ i.val → i.val < m+n → s i=false) :
    Run (1:Matrix (Reg L) (Reg L) ℂ) (reflectionCompile (booleanDAGComputeInto g h))
      (Ket s)=Ket (dagFilled g h x s) := by
  induction g generalizing L x s with
  | nil =>
    simp only [booleanDAGComputeInto,reflectionCompile,List.map_nil,run_nil]
    congr 1
    funext w
    by_cases hwm : w.val < m
    · have hi := hx ⟨w.val,hwm⟩
      have he : Fin.castLE (by omega : m ≤ L) (⟨w.val,hwm⟩:Fin m)=w := Fin.ext rfl
      rw [he] at hi
      simpa [dagFilled,booleanDAGValue,hwm] using hi
    · simp [dagFilled,hwm]
  | @snoc n g node ih =>
    have hp : m+n ≤ L := by omega
    have ht : m+n < L := by omega
    have hwg : ∀i:Fin L,m ≤ i.val → i.val < m+n → s i=false := by
      intro i hi hj
      exact hw i hi (by omega)
    rw [booleanDAGComputeInto,reflectionCompile_append,run_append,ih hp x s hx hwg,
      boolean_node_basis]
    have hsource : (fun i:Fin (m+n) => dagFilled g hp x s (Fin.castLE ht.le i))=
        booleanDAGValue g x := by
      funext i
      exact dag_filled_source g hp x s i
    have hzero : dagFilled g hp x s (⟨m+n,ht⟩:Fin L)=false := by
      simp only [dagFilled,dif_neg (Nat.lt_irrefl (m+n))]
      exact hw (⟨m+n,ht⟩ : Fin L) (by change m ≤ m+n; omega)
        (by change m+n < m+(n+1); omega)
    rw [hsource,hzero,Bool.false_xor]
    congr 1
    funext w
    by_cases hwt : w=(⟨m+n,ht⟩:Fin L)
    · subst w
      have hnew : m+n < m+(n+1) := by omega
      simp only [Function.update_self,dagFilled,dif_pos hnew,booleanDAGValue]
      have he : (⟨m+n,hnew⟩ : Fin (m+(n+1))) = Fin.last (m+n) := Fin.ext rfl
      rw [he]
      exact (Fin.lastCases_last (n := m+n) (motive := fun _ => Bool)
        (last := booleanNodeValue node (booleanDAGValue g x))
        (cast := booleanDAGValue g x)).symm
    · rw [Function.update_of_ne hwt]
      by_cases hwp : w.val < m+n
      · have hnew : w.val < m+(n+1) := by omega
        simp only [dagFilled,dif_pos hwp,dif_pos hnew,booleanDAGValue]
        have he : (⟨w.val,hnew⟩:Fin (m+(n+1)))=
            Fin.castSucc (⟨w.val,hwp⟩:Fin (m+n)) := Fin.ext rfl
        rw [he,Fin.lastCases_castSucc]
      · have hval : w.val ≠ m+n := by
          intro he
          apply hwt
          exact Fin.ext he
        have hnew : ¬w.val < m+(n+1) := by omega
        simp [dagFilled,hwp,hnew]

private theorem dag_compute_into_resources {m n L : ℕ} (g : BooleanDAG m n)
    (h : m+n ≤ L) :
    reflectionLegal (booleanDAGComputeInto g h) ∧
      (booleanDAGComputeInto g h).length ≤ 15*n := by
  induction g generalizing L with
  | nil => simp [booleanDAGComputeInto,reflectionLegal]
  | @snoc n g node ih =>
    have hp : m+n ≤ L := by omega
    have ht : m+n < L := by omega
    have hg := ih hp
    have hn := boolean_node_resources node ht
    constructor
    · rw [booleanDAGComputeInto,reflectionLegal_append]
      exact ⟨hg.1,hn.1⟩
    · rw [booleanDAGComputeInto,List.length_append]
      omega

theorem boolean_dag_compute_basis {m n : ℕ} (g : BooleanDAG m n) (o : ℕ)
    (x : Reg m) (y : Reg o) :
    Run (1 : Matrix (Reg (m+n+o)) (Reg (m+n+o)) ℂ)
      (reflectionCompile (booleanDAGCompute g o)) (Ket (booleanDAGInput m n o x y)) =
      Ket (booleanDAGComputed g o x y) := by
  have hx : ∀i:Fin m, booleanDAGInput m n o x y (Fin.castLE (by omega) i)=x i := by
    intro i
    simp [booleanDAGInput,i.isLt]
  have hw : ∀i:Fin (m+n+o),m ≤ i.val → i.val < m+n →
      booleanDAGInput m n o x y i=false := by
    intro i hi hj
    simp [booleanDAGInput,show ¬i.val < m by omega,hj]
  rw [booleanDAGCompute,dag_compute_into_basis g _ x _ hx hw]
  congr 1
  funext w
  by_cases hwp : w.val < m+n
  · simp [dagFilled,booleanDAGComputed,hwp]
  · have hm : ¬w.val < m := by omega
    simp [dagFilled,booleanDAGComputed,booleanDAGInput,hwp,hm]

private def dagOutputWire (m n o : ℕ) (j : Fin o) : Fin (m+n+o) :=
  ⟨m+n+j.val,by have := j.isLt; omega⟩

private theorem dag_computed_output {m n : ℕ} (g : BooleanDAG m n)
    (o : ℕ) (x : Reg m) (y : Reg o) (j : Fin o) :
    booleanDAGComputed g o x y (dagOutputWire m n o j)=y j := by
  have hnot : ¬m+n+j.val < m+n := by omega
  simp [dagOutputWire,booleanDAGComputed,hnot]

private theorem dag_computed_source {m n : ℕ} (g : BooleanDAG m n)
    (o : ℕ) (x : Reg m) (y : Reg o) (i : Fin (m+n)) :
    booleanDAGComputed g o x y (Fin.castLE (by omega) i)=booleanDAGValue g x i := by
  simp [booleanDAGComputed,i.isLt]

private theorem dag_computed_update {m n : ℕ} (g : BooleanDAG m n)
    (o : ℕ) (x : Reg m) (y : Reg o) (j : Fin o) (v : Bool) :
    Function.update (booleanDAGComputed g o x y) (dagOutputWire m n o j) v =
      booleanDAGComputed g o x (Function.update y j v) := by
  funext w
  by_cases hw : w=dagOutputWire m n o j
  · subst w
    simp [dag_computed_output]
  · rw [Function.update_of_ne hw]
    by_cases hp : w.val < m+n
    · simp [booleanDAGComputed,hp]
    · have hj : (⟨w.val-(m+n),by omega⟩:Fin o) ≠ j := by
        intro he
        apply hw
        apply Fin.ext
        have hv := congrArg Fin.val he
        change w.val-(m+n) = j.val at hv
        change w.val = m+n+j.val
        omega
      simp [booleanDAGComputed,hp,Function.update_of_ne hj]

private def dagCopyGate {m n o : ℕ} (out : Fin o → Fin (m+n)) (j : Fin o) :
    ReflectionGate (m+n+o) := .inr (Fin.castLE (by omega) (out j),dagOutputWire m n o j)

private theorem dag_copy_distinct {m n o : ℕ} (out : Fin o → Fin (m+n)) (j : Fin o) :
    Fin.castLE (by omega) (out j) ≠ dagOutputWire m n o j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := (out j).isLt
  dsimp [dagOutputWire] at hv
  omega

private theorem dag_copy_list_basis {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (xs : List (Fin o)) (hxs : xs.Nodup)
    (x : Reg m) (y : Reg o) :
    Run (1:Matrix (Reg (m+n+o)) (Reg (m+n+o)) ℂ)
      (reflectionCompile (xs.map (dagCopyGate out))) (Ket (booleanDAGComputed g o x y)) =
      Ket (booleanDAGComputed g o x
        (fun j => y j ^^ (if j ∈ xs then booleanDAGValue g x (out j) else false))) := by
  induction xs generalizing y with
  | nil => simp [reflectionCompile]
  | cons i xs ih =>
    have hn := (List.nodup_cons.mp hxs).1
    have ht := (List.nodup_cons.mp hxs).2
    simp only [List.map_cons,reflectionCompile,List.map_cons,run_gate,reflectionGateMatrix,
      dagCopyGate]
    rw [applyGate_cnotGate_ket _ _ _ (dag_copy_distinct out i),
      dag_computed_output,dag_computed_source,dag_computed_update]
    change Run _ (reflectionCompile (xs.map (dagCopyGate out))) _ = _
    rw [ih ht]
    congr 2
    funext j
    by_cases hj : j=i
    · subst j
      simp [hn]
    · simp [hj]

private theorem dag_copy_basis {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (x : Reg m) (y : Reg o) :
    Run (1:Matrix (Reg (m+n+o)) (Reg (m+n+o)) ℂ)
      (reflectionCompile (booleanDAGCopy m n o out)) (Ket (booleanDAGComputed g o x y)) =
      Ket (booleanDAGComputed g o x (booleanDAGOutput g out x y)) := by
  simpa [booleanDAGCopy,dagCopyGate,dagOutputWire,booleanDAGOutput] using!
    dag_copy_list_basis g out (List.finRange o) (List.nodup_finRange o) x y

private theorem dag_copy_resources {m n o : ℕ} (out : Fin o → Fin (m+n)) :
    reflectionLegal (booleanDAGCopy m n o out) ∧ (booleanDAGCopy m n o out).length=o := by
  constructor
  · intro gate hg
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
    exact dag_copy_distinct out j
  · simp [booleanDAGCopy]

theorem boolean_dag_resources {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) :
    reflectionLegal (booleanDAGSteps g out) ∧
    (booleanDAGSteps g out).length ≤ 30*n+o ∧
    QueryCount (reflectionCompile (booleanDAGSteps g out)) = 0 ∧
    GateCount (reflectionCompile (booleanDAGSteps g out)) = (booleanDAGSteps g out).length := by
  have hc := dag_compute_into_resources g (by omega : m+n ≤ m+n+o)
  have hp := dag_copy_resources out
  have ha := reflectionAdjoint_legal (booleanDAGCompute g o) hc.1
  have hlen : (booleanDAGCompute g o).length ≤ 15*n := hc.2
  refine ⟨?_,?_,queryCount_reflectionCompile _,gateCount_reflectionCompile _⟩
  · simp only [booleanDAGSteps,reflectionLegal_append]
    exact ⟨⟨hc.1,hp.1⟩,ha⟩
  · simp only [booleanDAGSteps,List.length_append,reflectionAdjoint_length,hp.2]
    omega

private theorem dag_adjoint_uncomputes {L : ℕ} (gs : List (ReflectionGate L))
    (hg : reflectionLegal gs) (s t : Reg L)
    (hst : Run (1:Matrix (Reg L) (Reg L) ℂ) (reflectionCompile gs) (Ket s)=Ket t) :
    Run (1:Matrix (Reg L) (Reg L) ℂ) (reflectionCompile (reflectionAdjoint gs))
      (Ket t)=Ket s := by
  rw [← hst,run_reflectionCompile,run_reflectionCompile,reflectionAdjoint_matrix gs hg,
    ← applyGate_mul]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (reflectionProgramMatrix_unitary gs hg)
  simp only [Matrix.star_eq_conjTranspose] at hu
  rw [hu,applyGate_one]

theorem boolean_dag_basis {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (x : Reg m) (y : Reg o) :
    Run (1 : Matrix (Reg (m+n+o)) (Reg (m+n+o)) ℂ)
      (reflectionCompile (booleanDAGSteps g out)) (Ket (booleanDAGInput m n o x y)) =
      Ket (booleanDAGInput m n o x (booleanDAGOutput g out x y)) := by
  rw [booleanDAGSteps,reflectionCompile_append,reflectionCompile_append,
    run_append,run_append,boolean_dag_compute_basis,dag_copy_basis]
  exact dag_adjoint_uncomputes (booleanDAGCompute g o)
    (dag_compute_into_resources g (by omega : m+n ≤ m+n+o)).1 _ _
    (boolean_dag_compute_basis g o x (booleanDAGOutput g out x y))

theorem boolean_dag_coherent {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (ψ : QState (Reg m × Reg o)) :
    Run (1 : Matrix (Reg (m+n+o)) (Reg (m+n+o)) ℂ)
      (reflectionCompile (booleanDAGSteps g out)) (booleanDAGEmbed m n o ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput m n o xy.1 (booleanDAGOutput g out xy.1 xy.2)) := by
  simp only [booleanDAGEmbed,run_reflectionCompile_sum,run_reflectionCompile_smul,
    boolean_dag_basis]

end Qatlib.Concepts.MatrixAccess.RitzPipeline
