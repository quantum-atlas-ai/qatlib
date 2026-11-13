/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.ModularArithmetic

/-!
# Controlled native modular arithmetic

This module adds a preserved control bit to Boolean arithmetic graphs and selects between their
output and the original data word. Given an inverse graph, `controlledWord` compiles the
resulting controlled update into native reflection gates with clean workspace behavior.

The specialized multiplication and addition words support the coherent PRN jumps used in
[KanekoEtAl2020]. Their resource theorems give explicit quadratic length bounds and zero query
counts.

## Main statements

* `controlled_value`: identifies the controlled graph with the conditional data update.
* `controlled_word_basis`: proves the compiled controlled update on clean inputs.
* `controlled_mul_resources`: bounds the controlled multiplication word.
* `encoded_controlled_mul`: specializes multiplication to encoded residues modulo `2 ^ n`.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- Append a Boolean control bit to a data word. -/
def packed {w : ℕ} (x : Reg w) (b : Bool) : Reg (w+1) := Fin.snoc x b

/-- Embed the original data-wire indices into the input wires of the extended data-and-control
graph. -/
def dataSource (w : ℕ) : Fin w → Fin ((w+1)+0) := fun j => ⟨j.val,by omega⟩

/-- Lift a Boolean graph to inputs containing one extra control bit, retaining the original data
sources. -/
def lifted {w n : ℕ} (g : BooleanDAG w n) : BooleanDAG (w+1) (0+n) :=
  booleanDAGSplice .nil (dataSource w) g

/-- Translate the original graph's output-wire indices into the lifted graph. -/
def liftedOut {w n : ℕ} (out : Fin w → Fin (w+n)) : Fin w → Fin ((w+1)+(0+n)) :=
  fun j => booleanSpliceSource (dataSource w) (out j)

/-- The index of the preserved control input wire in a graph with `w` data inputs and `n`
computed nodes. -/
def controlWire (w n : ℕ) : Fin ((w+1)+n) := ⟨w,by omega⟩

/-- The original data-input wire indices in the graph extended by a control bit and computed
nodes. -/
def oldData (w n : ℕ) : Fin w → Fin ((w+1)+n) := fun j => ⟨j.val,by omega⟩

/-- Extend a Boolean graph with a word multiplexer selecting its computed output when the
control is true and the original data otherwise. -/
def controlled {w n : ℕ} (g : BooleanDAG w n) (out : Fin w → Fin (w+n)) :
    BooleanDAG (w+1) ((0+n)+3*w) :=
  booleanDAGSplice (lifted g)
    (booleanMuxSources w (liftedOut out) (oldData w (0+n)) (controlWire w (0+n)))
    (booleanWordMuxDAG w)

/-- The output-wire map for the controlled graph, including the preserved control bit. -/
def controlledOut {w n : ℕ} (out : Fin w → Fin (w+n)) :
    Fin (w+1) → Fin ((w+1)+((0+n)+3*w)) :=
  Fin.snoc (fun j => booleanSpliceSource
    (booleanMuxSources w (liftedOut out) (oldData w (0+n)) (controlWire w (0+n)))
    (booleanWordMuxSelect w j)) (controlWire w ((0+n)+3*w))

/-- The lifted graph on a packed input computes the same data output as the original graph,
independently of the control bit. -/
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

/-- The controlled graph preserves the control bit and returns the original graph's output when
it is true, or the unchanged input data when it is false. -/
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

/-- If one graph's data function reverses another's, their controlled data functions also
compose to the identity. -/
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

/-- The native in-place reflection word built from the controlled forward and reverse Boolean
graphs. -/
noncomputable def controlledWord {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :=
  InPlace.word (controlled f fo) (controlledOut fo) (controlled g go) (controlledOut go)

/-- If the supplied reverse graph reverses the forward data function, the compiled word
conditionally applies that function, preserves the control bit, and restores the clean
scratch and output workspace. -/
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

/-- The controlled word is legal, has length at most `30 * (nf + ng + 6 * w) + 5 * (w + 1)`, and
compiles to zero queries and one known gate per word element. -/
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

/-- The scratch width used for the controlled forward and inverse guarded multiplication graphs. -/
def mulControlWork (w : ℕ) := max ((0+Guarded.nodes (Guarded.mulRaw w))+3*w)
  ((0+Guarded.nodes (Guarded.mulRaw w))+3*w)

/-- The scratch width used for the controlled forward and inverse guarded addition graphs. -/
def addControlWork (w : ℕ) := max ((0+Guarded.nodes (Guarded.addRaw w))+3*w)
  ((0+Guarded.nodes (Guarded.addRaw w))+3*w)

/-- The native controlled guarded multiplication word built from the multiplier graph and its
inverse-multiplier graph. -/
noncomputable def controlledMul (w : ℕ) (a m : Reg w) :
    List (ReflectionGate ((w+1)+mulControlWork w+(w+1))) :=
  controlledWord (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))

/-- The native controlled guarded addition word built from the increment graph and its
inverse-increment graph. -/
noncomputable def controlledAdd (w : ℕ) (a m : Reg w) :
    List (ReflectionGate ((w+1)+addControlWork w+(w+1))) :=
  controlledWord (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))

/-- When the encoded multiplier and modulus are coprime, the controlled multiplication word
applies `Native.mulFunction` exactly on the true branch, preserves the control bit, and
restores clean workspace. -/
theorem controlled_mul_basis (w : ℕ) (a m x : Reg w) (b : Bool)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    Run 1 (reflectionCompile (controlledMul w a m))
      (Ket (booleanDAGInput (w+1) (mulControlWork w) (w+1) (packed x b) (fun _ => false))) =
      Ket (booleanDAGInput (w+1) (mulControlWork w) (w+1)
        (packed (if b then Native.mulFunction w a m x else x) b) (fun _ => false)) :=
  controlled_word_basis _ _ _ _ (fun x => Native.mul_function_inverse w a m x hc) x b

/-- The controlled addition word applies `Native.addFunction` exactly on the true branch,
preserves the control bit, and restores clean workspace. -/
theorem controlled_add_basis (w : ℕ) (a m x : Reg w) (b : Bool) :
    Run 1 (reflectionCompile (controlledAdd w a m))
      (Ket (booleanDAGInput (w+1) (addControlWork w) (w+1) (packed x b) (fun _ => false))) =
      Ket (booleanDAGInput (w+1) (addControlWork w) (w+1)
        (packed (if b then Native.addFunction w a m x else x) b) (fun _ => false)) :=
  controlled_word_basis _ _ _ _ (Native.add_function_inverse w a m) x b

/-- The controlled multiplication word is legal and has length at most `5460 * w ^ 2 + 1745 * w
+ 425`; its compiled circuit uses zero queries and one known gate per word element. -/
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

/-- The controlled addition word is legal and has length at most `1200 * w ^ 2 + 4025 * w +
1985`; its compiled circuit uses zero queries and one known gate per word element. -/
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

/-- On an encoded residue modulo `2 ^ n`, controlled multiplication by a unit writes the encoded
product on the true branch, preserves the input on the false branch, and restores the clean
workspace. -/
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
