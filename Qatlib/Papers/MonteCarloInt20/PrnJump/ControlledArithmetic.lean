/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.ModularArithmetic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord
open scoped Classical
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Controlled

def packed {w : ℕ} (x : Reg w) (b : Bool) : Reg (w+1) := Fin.snoc x b

def dataSource (w : ℕ) : Fin w → Fin ((w+1)+0) := fun j => ⟨j.val,by omega⟩

def lifted {w n : ℕ} (g : BooleanDAG w n) : BooleanDAG (w+1) (0+n) :=
  booleanDAGSplice .nil (dataSource w) g

def liftedOut {w n : ℕ} (out : Fin w → Fin (w+n)) : Fin w → Fin ((w+1)+(0+n)) :=
  fun j => booleanSpliceSource (dataSource w) (out j)

def controlWire (w n : ℕ) : Fin ((w+1)+n) := ⟨w,by omega⟩

def oldData (w n : ℕ) : Fin w → Fin ((w+1)+n) := fun j => ⟨j.val,by omega⟩

def controlled {w n : ℕ} (g : BooleanDAG w n) (out : Fin w → Fin (w+n)) :
    BooleanDAG (w+1) ((0+n)+3*w) :=
  booleanDAGSplice (lifted g)
    (booleanMuxSources w (liftedOut out) (oldData w (0+n)) (controlWire w (0+n)))
    (booleanWordMuxDAG w)

def controlledOut {w n : ℕ} (out : Fin w → Fin (w+n)) :
    Fin (w+1) → Fin ((w+1)+((0+n)+3*w)) :=
  Fin.snoc (fun j => booleanSpliceSource
    (booleanMuxSources w (liftedOut out) (oldData w (0+n)) (controlWire w (0+n)))
    (booleanWordMuxSelect w j)) (controlWire w ((0+n)+3*w))

theorem lifted_value {w n : ℕ} (g : BooleanDAG w n) (out : Fin w → Fin (w+n))
    (x : Reg w) (b : Bool) :
    (fun j => booleanDAGValue (lifted g) (packed x b) (liftedOut out j)) =
      InPlace.value g out x := by
  funext j
  rw [lifted,liftedOut,boolean_dag_splice_value]
  have hx : (fun j => booleanDAGValue (.nil : BooleanDAG (w+1) 0)
      (packed x b) (dataSource w j)) = x := by
    funext i
    change packed x b i.castSucc = x i
    simp [packed]
  rw [hx]
  rfl

theorem controlled_value {w n : ℕ} (g : BooleanDAG w n) (out : Fin w → Fin (w+n))
    (x : Reg w) (b : Bool) :
    InPlace.value (controlled g out) (controlledOut out) (packed x b) =
      packed (if b then InPlace.value g out x else x) b := by
  have hm := shared_mux (lifted g) (liftedOut out) (oldData w (0+n))
    (controlWire w (0+n)) (packed x b)
  have hc : booleanDAGValue (lifted g) (packed x b) (controlWire w (0+n)) = b := by
    have h := input_wire (lifted g) (packed x b) (Fin.last w)
    simpa only [packed,Fin.snoc_last] using! h
  have ho : (fun j => booleanDAGValue (lifted g) (packed x b) (oldData w (0+n) j)) = x := by
    funext j
    exact (input_wire (lifted g) (packed x b) j.castSucc).trans (by simp [packed])
  rw [hc,lifted_value,ho] at hm
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [InPlace.value,controlledOut,Fin.snoc_last,packed]
    exact (input_wire (controlled g out) (packed x b) (Fin.last w)).trans (by simp [packed])
  · simp only [InPlace.value,controlledOut,Fin.snoc_castSucc,packed]
    exact congrFun hm i

theorem controlled_inverse {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng))
    (hinv : ∀ x, InPlace.value g go (InPlace.value f fo x) = x) (x : Reg (w+1)) :
    InPlace.value (controlled g go) (controlledOut go)
      (InPlace.value (controlled f fo) (controlledOut fo) x) = x := by
  have hx : x = packed (fun j => x j.castSucc) (x (Fin.last w)) := by
    exact (Fin.snoc_init_self x).symm
  rw [hx,controlled_value]
  by_cases hb : x (Fin.last w) = true
  · simp only [hb,ite_true,controlled_value,hinv]
  · have hb' : x (Fin.last w) = false := Bool.eq_false_iff.mpr hb
    simp only [hb',Bool.false_eq_true,ite_false,controlled_value]

noncomputable def controlledWord {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :=
  InPlace.word (controlled f fo) (controlledOut fo) (controlled g go) (controlledOut go)

theorem controlled_word_basis {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng))
    (hinv : ∀ x, InPlace.value g go (InPlace.value f fo x) = x) (x : Reg w) (b : Bool) :
    Run 1 (reflectionCompile (controlledWord f fo g go))
      (Ket (booleanDAGInput (w+1) (max ((0+nf)+3*w) ((0+ng)+3*w)) (w+1)
        (packed x b) (fun _ => false))) =
      Ket (booleanDAGInput (w+1) (max ((0+nf)+3*w) ((0+ng)+3*w)) (w+1)
        (packed (if b then InPlace.value f fo x else x) b) (fun _ => false)) := by
  have h := InPlace.basis (controlled f fo) (controlledOut fo) (controlled g go) (controlledOut go)
    (controlled_inverse f fo g go hinv) (packed x b)
  simpa only [controlledWord,controlled_value] using! h

theorem controlled_word_resources {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :
    reflectionLegal (controlledWord f fo g go) ∧
    (controlledWord f fo g go).length ≤ 30*(nf+ng+6*w)+5*(w+1) ∧
    QueryCount (reflectionCompile (controlledWord f fo g go)) = 0 ∧
    GateCount (reflectionCompile (controlledWord f fo g go)) = (controlledWord f fo g go).length := by
  have h :=
      InPlace.resources (controlled f fo) (controlledOut fo) (controlled g go) (controlledOut go)
  refine ⟨h.1,?_,h.2.2⟩
  have he : (0+nf)+3*w+((0+ng)+3*w) = nf+ng+6*w := by omega
  simpa only [he] using! h.2.1

def mulControlWork (w : ℕ) := max ((0+Guarded.nodes (Guarded.mulRaw w))+3*w)
  ((0+Guarded.nodes (Guarded.mulRaw w))+3*w)

def addControlWork (w : ℕ) := max ((0+Guarded.nodes (Guarded.addRaw w))+3*w)
  ((0+Guarded.nodes (Guarded.addRaw w))+3*w)

noncomputable def controlledMul (w : ℕ) (a m : Reg w) :
    List (ReflectionGate ((w+1)+mulControlWork w+(w+1))) :=
  controlledWord (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))

noncomputable def controlledAdd (w : ℕ) (a m : Reg w) :
    List (ReflectionGate ((w+1)+addControlWork w+(w+1))) :=
  controlledWord (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))

theorem controlled_mul_basis (w : ℕ) (a m x : Reg w) (b : Bool)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    Run 1 (reflectionCompile (controlledMul w a m))
      (Ket (booleanDAGInput (w+1) (mulControlWork w) (w+1) (packed x b) (fun _ => false))) =
      Ket (booleanDAGInput (w+1) (mulControlWork w) (w+1)
        (packed (if b then Native.mulFunction w a m x else x) b) (fun _ => false)) :=
  controlled_word_basis _ _ _ _ (fun x => Native.mul_function_inverse w a m x hc) x b

theorem controlled_add_basis (w : ℕ) (a m x : Reg w) (b : Bool) :
    Run 1 (reflectionCompile (controlledAdd w a m))
      (Ket (booleanDAGInput (w+1) (addControlWork w) (w+1) (packed x b) (fun _ => false))) =
      Ket (booleanDAGInput (w+1) (addControlWork w) (w+1)
        (packed (if b then Native.addFunction w a m x else x) b) (fun _ => false)) :=
  controlled_word_basis _ _ _ _ (Native.add_function_inverse w a m) x b

theorem controlled_mul_resources (w : ℕ) (a m : Reg w) :
    reflectionLegal (controlledMul w a m) ∧
    (controlledMul w a m).length ≤ 5460*w^2+1745*w+425 ∧
    QueryCount (reflectionCompile (controlledMul w a m)) = 0 ∧
    GateCount (reflectionCompile (controlledMul w a m)) = (controlledMul w a m).length := by
  have h := controlled_word_resources (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
  refine ⟨h.1,?_,h.2.2⟩
  have hn := Native.mul_node_bound w
  exact h.2.1.trans (by nlinarith)

theorem controlled_add_resources (w : ℕ) (a m : Reg w) :
    reflectionLegal (controlledAdd w a m) ∧
    (controlledAdd w a m).length ≤ 1200*w^2+4025*w+1985 ∧
    QueryCount (reflectionCompile (controlledAdd w a m)) = 0 ∧
    GateCount (reflectionCompile (controlledAdd w a m)) = (controlledAdd w a m).length := by
  have h := controlled_word_resources (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
  refine ⟨h.1,?_,h.2.2⟩
  have hn := Native.add_node_bound w
  exact h.2.1.trans (by nlinarith)

theorem encoded_controlled_mul (n : ℕ) (a : (ZMod (2^n))ˣ) (x : ZMod (2^n)) (b : Bool) :
    Run 1 (reflectionCompile (controlledMul (n+1) (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n (a:ZMod (2^n)))
      (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.modulusBits n)))
      (Ket (booleanDAGInput ((n+1)+1) (mulControlWork (n+1)) ((n+1)+1)
        (packed (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n x) b) (fun _ => false))) =
      Ket (booleanDAGInput ((n+1)+1) (mulControlWork (n+1)) ((n+1)+1)
        (packed (if b then Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n ((a:ZMod (2^n))*x)
          else Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n x) b) (fun _ => false)) := by
  have hc : (booleanWordLSBValue (n+1) (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n (a:ZMod (2^n)))).Coprime
      (booleanWordLSBValue (n+1) (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.modulusBits n)) := by
    rw [Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode_value,Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.modulus_value]
    exact ZMod.val_coe_unit_coprime a
  simpa only [Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.native_mul_value] using! controlled_mul_basis (n+1)
    (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n (a:ZMod (2^n))) (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.modulusBits n)
    (Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic.encode n x) b hc
end Qatlib.Papers.MonteCarloInt20.PrnJump.Controlled
