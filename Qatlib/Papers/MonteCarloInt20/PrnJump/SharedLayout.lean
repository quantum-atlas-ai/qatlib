/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.ControlledArithmetic
import Qatlib.Papers.MonteCarloInt20.PrnJump.AffineWord

/-!
# Shared layouts for controlled PRN arithmetic

This module extends data DAGs by unchanged control bits and uses word muxes to condition updates
on one selected control. `indexedWord` compiles these controlled functions with clean workspace,
and `paddedWord` places different arithmetic programs in a common layout.

`commonMul` and `commonAdd` share a workspace size for controlled modular arithmetic, providing
basis semantics and explicit gate bounds for native PRN jump construction. See [KanekoEtAl2020].

## Main statements

* `indexed_basis`: controlled application of a DAG function with controls preserved.
* `common_mul_basis` and `common_add_basis`: controlled modular updates in the common layout.
* `mul_resources` and `add_resources`: legality and gate bounds.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
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
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Shared

/-- Embeds a data DAG into a register extended by `k` control bits. -/
def dataGraph {w n : ℕ} (k : ℕ) (g : BooleanDAG w n) : BooleanDAG (w+k) (0+n) :=
  booleanDAGSplice .nil (fun j => (Fin.castAdd k j).castLE (by omega)) g

/-- Selects the data DAG outputs followed by the unchanged control wires. -/
def dataOut {w n : ℕ} (k : ℕ) (out : Fin w → Fin (w+n)) :
    Fin (w+k) → Fin ((w+k)+(0+n)) :=
  Fin.append (fun j => booleanSpliceSource (fun j => (Fin.castAdd k j).castLE (by omega)) (out j))
    (fun q => (Fin.natAdd w q).castLE (by omega))

/-- The extended DAG applies the original word function to the data block and preserves the
control block. -/
theorem data_value {w n : ℕ} (k : ℕ) (g : BooleanDAG w n) (out : Fin w → Fin (w+n))
    (x : Reg (w+k)) :
    InPlace.value (dataGraph k g) (dataOut k out) x =
      Fin.append (InPlace.value g out (fun j => x (Fin.castAdd k j))) (fun q => x (Fin.natAdd w q)) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun q => ?_) j
  · simp only [InPlace.value,dataOut,Fin.append_left]
    rw [dataGraph,boolean_dag_splice_value]
    rfl
  · simp only [InPlace.value,dataOut,Fin.append_right]
    exact input_wire _ _ _

/-- The extended data DAG leaves every control bit unchanged. -/
theorem data_keeps_control {w n : ℕ} (k : ℕ) (g : BooleanDAG w n) (out : Fin w → Fin (w+n))
    (q : Fin k) (x : Reg (w+k)) :
    InPlace.value (dataGraph k g) (dataOut k out) x (Fin.natAdd w q) = x (Fin.natAdd w q) := by
  rw [data_value]
  simp only [Fin.append_right]

/-- A left-inverse pair of data DAG functions remains a left-inverse pair after extending by
control bits. -/
theorem data_inverse {w nf ng : ℕ} (k : ℕ) (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng))
    (hinv : ∀ x, InPlace.value g go (InPlace.value f fo x) = x) (x : Reg (w+k)) :
    InPlace.value (dataGraph k g) (dataOut k go)
      (InPlace.value (dataGraph k f) (dataOut k fo) x) = x := by
  simp only [data_value,Fin.append_left,Fin.append_right,hinv]
  exact Fin.append_castAdd_natAdd

/-- Appends a word mux that chooses the DAG output or the original input according to input bit
`q`. -/
def muxGraph {m n : ℕ} (g : BooleanDAG m n) (out : Fin m → Fin (m+n)) (q : Fin m) :
    BooleanDAG m (n+3*m) :=
  booleanDAGSplice g (booleanMuxSources m out (fun j => j.castLE (by omega)) (q.castLE (by omega)))
    (booleanWordMuxDAG m)

/-- Selects the outputs of the conditional word mux. -/
def muxOut {m n : ℕ} (out : Fin m → Fin (m+n)) (q : Fin m) : Fin m → Fin (m+(n+3*m)) :=
  fun j => booleanSpliceSource
    (booleanMuxSources m out (fun j => j.castLE (by omega)) (q.castLE (by omega)))
    (booleanWordMuxSelect m j)

/-- The mux graph applies the DAG function when the chosen input control is true and otherwise
returns the input. -/
theorem mux_value {m n : ℕ} (g : BooleanDAG m n) (out : Fin m → Fin (m+n)) (q : Fin m)
    (x : Reg m) : InPlace.value (muxGraph g out q) (muxOut out q) x =
      if x q then InPlace.value g out x else x := by
  have h := shared_mux g out (fun j => j.castLE (by omega)) (q.castLE (by omega)) x
  have hc := input_wire g x q
  have hx : (fun j : Fin m => booleanDAGValue g x (j.castLE (by omega))) = x := by
    funext j
    exact input_wire g x j
  rw [hc,hx] at h
  exact h

/-- Controlled DAG functions form a left-inverse pair when the forward function preserves the
control and the original functions form a left-inverse pair. -/
theorem mux_inverse {m nf ng : ℕ} (f : BooleanDAG m nf) (fo : Fin m → Fin (m+nf))
    (g : BooleanDAG m ng) (go : Fin m → Fin (m+ng)) (q : Fin m)
    (hkeep : ∀ x, InPlace.value f fo x q = x q)
    (hinv : ∀ x, InPlace.value g go (InPlace.value f fo x) = x) (x : Reg m) :
    InPlace.value (muxGraph g go q) (muxOut go q)
      (InPlace.value (muxGraph f fo q) (muxOut fo q) x) = x := by
  rw [mux_value]
  by_cases hb : x q = true
  · simp only [hb,ite_true,mux_value,hkeep,hinv]
  · have hb' : x q = false := Bool.eq_false_iff.mpr hb
    simp only [hb',Bool.false_eq_true,ite_false,mux_value]

/-- Compiles a data function controlled by a selected bit of a separate control register using
its inverse DAG for cleanup. -/
noncomputable def indexedWord {w nf ng : ℕ} (k : ℕ) (q : Fin k)
    (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :=
  InPlace.word (muxGraph (dataGraph k f) (dataOut k fo) (Fin.natAdd w q))
    (muxOut (dataOut k fo) (Fin.natAdd w q))
    (muxGraph (dataGraph k g) (dataOut k go) (Fin.natAdd w q))
    (muxOut (dataOut k go) (Fin.natAdd w q))

/-- Given a left-inverse DAG, the indexed program conditionally updates the data word, preserves
the controls, and restores auxiliary registers. -/
theorem indexed_basis {w nf ng : ℕ} (k : ℕ) (q : Fin k)
    (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng))
    (hinv : ∀ x, InPlace.value g go (InPlace.value f fo x) = x) (x : Reg w) (bits : Reg k) :
    Run 1 (reflectionCompile (indexedWord k q f fo g go))
      (Ket (booleanDAGInput (w+k) (max ((0+nf)+3*(w+k)) ((0+ng)+3*(w+k))) (w+k)
        (Fin.append x bits) (fun _ => false))) =
      Ket (booleanDAGInput (w+k) (max ((0+nf)+3*(w+k)) ((0+ng)+3*(w+k))) (w+k)
        (Fin.append (if bits q then InPlace.value f fo x else x) bits) (fun _ => false)) := by
  have hi := mux_inverse (dataGraph k f) (dataOut k fo) (dataGraph k g) (dataOut k go)
    (Fin.natAdd w q) (data_keeps_control k f fo q) (data_inverse k f fo g go hinv)
  have h := InPlace.basis _ _ _ _ hi (Fin.append x bits)
  have he : (if (Fin.append x bits) (Fin.natAdd w q) then
      InPlace.value (dataGraph k f) (dataOut k fo) (Fin.append x bits) else Fin.append x bits) =
      Fin.append (if bits q then InPlace.value f fo x else x) bits := by
    simp only [Fin.append_right,data_value,Fin.append_left]
    split <;> rfl
  simpa only [indexedWord,mux_value,he] using! h

/-- The indexed program is legal and query-free with the stated bound in terms of the two graph
sizes and register width. -/
theorem indexed_resources {w nf ng : ℕ} (k : ℕ) (q : Fin k)
    (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :
    reflectionLegal (indexedWord k q f fo g go) ∧
    (indexedWord k q f fo g go).length ≤ 30*(nf+ng+6*(w+k))+5*(w+k) ∧
    QueryCount (reflectionCompile (indexedWord k q f fo g go)) = 0 ∧
    GateCount (reflectionCompile (indexedWord k q f fo g go)) = (indexedWord k q f fo g go).length := by
  have h := InPlace.resources (muxGraph (dataGraph k f) (dataOut k fo) (Fin.natAdd w q))
    (muxOut (dataOut k fo) (Fin.natAdd w q))
    (muxGraph (dataGraph k g) (dataOut k go) (Fin.natAdd w q))
    (muxOut (dataOut k go) (Fin.natAdd w q))
  refine ⟨h.1,?_,h.2.2⟩
  have he : (0+nf)+3*(w+k)+((0+ng)+3*(w+k)) = nf+ng+6*(w+k) := by omega
  simpa only [he] using! h.2.1

/-- Embeds a reflection-gate word into a larger workspace without changing its data or output
blocks. -/
noncomputable def paddedWord {m n N : ℕ} (hn : n ≤ N)
    (gs : List (ReflectionGate (m+n+m))) : List (ReflectionGate (m+N+m)) :=
  gs.map (knownWireGateMap (Layout.paddedWires m n m N hn))

/-- Padding a legal program preserves its specified clean-workspace basis action. -/
theorem padded_basis {m n N : ℕ} (hn : n ≤ N) (gs : List (ReflectionGate (m+n+m)))
    (hgs : reflectionLegal gs) (x y : Reg m)
    (hxy : Run 1 (reflectionCompile gs) (Ket (booleanDAGInput m n m x (fun _ => false))) =
      Ket (booleanDAGInput m n m y (fun _ => false))) :
    Run 1 (reflectionCompile (paddedWord hn gs)) (Ket (booleanDAGInput m N m x (fun _ => false))) =
      Ket (booleanDAGInput m N m y (fun _ => false)) := by
  have h := wire_context_program (m+n+m) (m+N+m) (Layout.paddedWires m n m N hn)
    (booleanDAGInput m N m x (fun _ => false)) gs hgs (Ket (booleanDAGInput m n m x (fun _ => false)))
  have hbg : wireContextExtend (Layout.paddedWires m n m N hn)
      (booleanDAGInput m N m x (fun _ => false)) (booleanDAGInput m n m y (fun _ => false)) =
      wireContextExtend (Layout.paddedWires m n m N hn)
      (booleanDAGInput m N m y (fun _ => false)) (booleanDAGInput m n m y (fun _ => false)) := by
    funext j
    by_cases hj : ∃ i, Layout.paddedWires m n m N hn i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [(wire_context_extend _ _ _ _).1,(wire_context_extend _ _ _ _).1]
    · rw [(wire_context_extend _ _ _ _).2.1 _ j hj,(wire_context_extend _ _ _ _).2.1 _ j hj]
      have hm : ¬ j.val < m := by
        intro hlt
        apply hj
        refine ⟨⟨j.val,by omega⟩,?_⟩
        apply Fin.ext
        simp [Layout.paddedWires,show j.val < m+n by omega]
      simp [booleanDAGInput,hm]
  rw [hxy,wire_context_ket,wire_context_ket,Layout.padded_context,hbg,Layout.padded_context] at h
  exact h

/-- Padding a legal program preserves legality and length and gives a query-free compilation
with the same gate count. -/
theorem padded_resources {m n N : ℕ} (hn : n ≤ N) (gs : List (ReflectionGate (m+n+m)))
    (hgs : reflectionLegal gs) : reflectionLegal (paddedWord hn gs) ∧
    (paddedWord hn gs).length = gs.length ∧
    QueryCount (reflectionCompile (paddedWord hn gs)) = 0 ∧
    GateCount (reflectionCompile (paddedWord hn gs)) = gs.length := by
  exact ⟨knownWireMapList_legal _ gs hgs,List.length_map _,
    queryCount_reflectionCompile _,(gateCount_reflectionCompile _).trans (List.length_map _)⟩

/-- The workspace size for indexed native modular multiplication. -/
def mulScratch (w k : ℕ) := max ((0+Guarded.nodes (Guarded.mulRaw w))+3*(w+k))
  ((0+Guarded.nodes (Guarded.mulRaw w))+3*(w+k))

/-- The workspace size for indexed native modular addition. -/
def addScratch (w k : ℕ) := max ((0+Guarded.nodes (Guarded.addRaw w))+3*(w+k))
  ((0+Guarded.nodes (Guarded.addRaw w))+3*(w+k))

/-- The maximum workspace required by indexed multiplication and addition. -/
def commonScratch (w k : ℕ) := max (mulScratch w k) (addScratch w k)

/-- The indexed native multiplication program controlled by the selected exponent bit. -/
noncomputable def mulWord (w k : ℕ) (q : Fin k) (a m : Reg w) :
    List (ReflectionGate ((w+k)+mulScratch w k+(w+k))) :=
  indexedWord k q (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))

/-- The indexed native addition program controlled by the selected exponent bit. -/
noncomputable def addWord (w k : ℕ) (q : Fin k) (a m : Reg w) :
    List (ReflectionGate ((w+k)+addScratch w k+(w+k))) :=
  indexedWord k q (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))

/-- Pads indexed native multiplication into the common arithmetic workspace. -/
noncomputable def commonMul (w k : ℕ) (q : Fin k) (a m : Reg w) :=
  paddedWord (Nat.le_max_left (mulScratch w k) (addScratch w k)) (mulWord w k q a m)

/-- Pads indexed native addition into the common arithmetic workspace. -/
noncomputable def commonAdd (w k : ℕ) (q : Fin k) (a m : Reg w) :=
  paddedWord (Nat.le_max_right (mulScratch w k) (addScratch w k)) (addWord w k q a m)

/-- Indexed multiplication is legal and query-free and satisfies the stated quadratic gate bound
with a linear control-width term. -/
theorem mul_resources (w k : ℕ) (q : Fin k) (a m : Reg w) :
    reflectionLegal (mulWord w k q a m) ∧
    (mulWord w k q a m).length ≤ 5460*w^2+1745*w+185*k+420 ∧
    QueryCount (reflectionCompile (mulWord w k q a m)) = 0 ∧
    GateCount (reflectionCompile (mulWord w k q a m)) = (mulWord w k q a m).length := by
  have h := indexed_resources k q (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (Native.mulInvBits w a m) m (by omega))
  refine ⟨h.1,?_,h.2.2⟩
  exact h.2.1.trans (by nlinarith [Native.mul_node_bound w])

/-- Indexed addition is legal and query-free and satisfies the stated quadratic gate bound with
a linear control-width term. -/
theorem add_resources (w k : ℕ) (q : Fin k) (a m : Reg w) :
    reflectionLegal (addWord w k q a m) ∧
    (addWord w k q a m).length ≤ 1200*w^2+4025*w+185*k+1980 ∧
    QueryCount (reflectionCompile (addWord w k q a m)) = 0 ∧
    GateCount (reflectionCompile (addWord w k q a m)) = (addWord w k q a m).length := by
  have h := indexed_resources k q (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (Native.addInvBits w a m) m (by omega))
  refine ⟨h.1,?_,h.2.2⟩
  exact h.2.1.trans (by nlinarith [Native.add_node_bound w])

/-- For a multiplier coprime to the modulus, common-layout multiplication conditionally updates
the data word and preserves controls and clean auxiliary registers. -/
theorem common_mul_basis (w k : ℕ) (q : Fin k) (a m x : Reg w) (bits : Reg k)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    Run 1 (reflectionCompile (commonMul w k q a m))
      (Ket (booleanDAGInput (w+k) (commonScratch w k) (w+k) (Fin.append x bits) (fun _ => false))) =
      Ket (booleanDAGInput (w+k) (commonScratch w k) (w+k)
        (Fin.append (if bits q then Native.mulFunction w a m x else x) bits) (fun _ => false)) := by
  exact padded_basis _ _ (mul_resources w k q a m).1 _ _
    (indexed_basis k q _ _ _ _ (fun x => Native.mul_function_inverse w a m x hc) x bits)

/-- Common-layout addition conditionally updates the data word and preserves controls and clean
auxiliary registers. -/
theorem common_add_basis (w k : ℕ) (q : Fin k) (a m x : Reg w) (bits : Reg k) :
    Run 1 (reflectionCompile (commonAdd w k q a m))
      (Ket (booleanDAGInput (w+k) (commonScratch w k) (w+k) (Fin.append x bits) (fun _ => false))) =
      Ket (booleanDAGInput (w+k) (commonScratch w k) (w+k)
        (Fin.append (if bits q then Native.addFunction w a m x else x) bits) (fun _ => false)) := by
  exact padded_basis _ _ (add_resources w k q a m).1 _ _
    (indexed_basis k q _ _ _ _ (Native.add_function_inverse w a m) x bits)
end Qatlib.Papers.MonteCarloInt20.PrnJump.Shared
