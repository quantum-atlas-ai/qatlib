/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.Preentangled.PreentangledGraphConsumers
import Qatlib.Concepts.InstrumentCore.PatternCompile.ClusterEulerConsumers
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitEuler
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState

/-!
# Definitions for universal graph compilation

This module defines the compilation of local reflection gates into cluster-network words and the
observed circuits used to execute them. The definitions `mbqcGraphWord`, `mbqcRawProgram`, and
`mbqcReadoutProgram` provide the graph, its adaptive measurements, and a final readout with
classical Pauli-frame decoding, following the measurement-based model of
[RaussendorfBriegel2000].

The raw branch maps retain the final Pauli frame and can act on inputs with a reference system.
Resource-state constructors and event-mass definitions support the later correctness and
resource bounds.

## Main definitions

* `mbqcCompiledWord`: expand local gates into cluster-network gates.
* `mbqcRawReference`: execute a raw branch while retaining a reference system.
* `mbqcReadoutAcceptance`: sum the masses of accepted readout branches.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- The cluster Euler word obtained from the extracted one-qubit parameters of `U`. -/
def mbqcQubitWord (U : Matrix Bool Bool ℂ) : List ℂ :=
  let p := knownQubitAnglesOfUnitary U
  clusterEulerWord (-p.alpha-Real.pi/2) p.theta (-p.beta+Real.pi/2)

/-- The complex phase factor computed from the extracted one-qubit angles of `U`. -/
def mbqcQubitScalar (U : Matrix Bool Bool ℂ) : ℂ :=
  let p := knownQubitAnglesOfUnitary U
  Complex.exp ((((p.theta-p.alpha-p.beta)/2-p.delta : ℝ) : ℂ)*Complex.I)

/-- Expand a local reflection gate into cluster-network gates, using an Euler word for a
one-qubit gate and a Hadamard-CZ-Hadamard word for a controlled-NOT. -/
def mbqcLocalExpansion {n : ℕ} : ReflectionGate n → List (ClusterNetworkGate n)
  | .inl (i,U) => (mbqcQubitWord U).map fun ζ => .inl (i,ζ)
  | .inr (c,t) => [.inl (t,1),.inr (c,t),.inl (t,1)]

/-- Compile a reflection-gate list by concatenating its local cluster-network expansions. -/
def mbqcCompiledWord {n : ℕ} (gs : List (ReflectionGate n)) : List (ClusterNetworkGate n) :=
  gs.flatMap mbqcLocalExpansion

/-- Count the one-qubit gates and controlled-NOT gates in a reflection-gate list. -/
def mbqcLocalCounts {n : ℕ} : List (ReflectionGate n) → ℕ × ℕ
  | [] => (0,0)
  | .inl _ :: gs => let r := mbqcLocalCounts gs; (r.1+1,r.2)
  | .inr _ :: gs => let r := mbqcLocalCounts gs; (r.1,r.2+1)

/-- The product of the one-qubit phase factors accumulated by local cluster compilation. -/
def mbqcLocalScalar {n : ℕ} : List (ReflectionGate n) → ℂ
  | [] => 1
  | .inl (_,U) :: gs => mbqcLocalScalar gs * mbqcQubitScalar U
  | .inr _ :: gs => mbqcLocalScalar gs

/-- The matrix of a reflection-gate program, relabeled from bit-vector indices to `Fin (2^n)`. -/
def mbqcLogicalMatrix {n : ℕ} (gs : List (ReflectionGate n)) : Operator (2^n) :=
  relabelGate (bitVecEquiv n) (reflectionProgramMatrix gs)

/-- The graph word indexed by the positions of `mbqcCompiledWord gs`. -/
def mbqcGraphWord {n : ℕ} (gs : List (ReflectionGate n)) :
    GraphWord n (mbqcCompiledWord gs).length := fun t => (mbqcCompiledWord gs)[t]

/-- The adaptive observed circuit for the specified graph slots and initial Pauli frame,
terminating with acceptance after the slots are processed. -/
def mbqcRawTail {n L : ℕ} (gs : GraphWord n L) :
    List (Fin L) → PauliFrame n → ObservedCircuit (Fin (2^(n+L)))
  | [],_ => .halt true
  | t::ts,F =>
    match gs t with
    | .inl (i,ζ) =>
      let v := graphLayoutBefore gs t i
      .step (.gate (graphPhysicalPhase n L v (if F.1 i then star ζ else ζ)))
        (.step (.gate (graphPhysicalH n L v))
          (.measure 2 (graphPhysicalLabel n L v) (fun a =>
            mbqcRawTail gs ts (graphWireFrame F i (boolEquivFin2.symm a)))))
    | .inr (i,j) => mbqcRawTail gs ts (graphCzFrame F i j)

/-- The observed circuit that prepares fresh qubits, applies the graph edges, and executes the
raw measurement tail from the zero Pauli frame. -/
def mbqcRawProgram {n L : ℕ} (gs : GraphWord n L) : ObservedCircuit (Fin (2^(n+L))) :=
  graphPrepend (graphFreshGates n L)
    (graphPrepend (graphEdgeGates gs)
      (mbqcRawTail gs (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)))

/-- The raw program leaf selected by a graph history, with a zero rejecting leaf as the default
for an out-of-range index. -/
def mbqcRawLeaf {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    ObservedKrausLeaf (2^(n+L)) :=
  (observedKrausLeaves 1 (mbqcRawProgram gs)).getD (graphHistoryIndex gs h)
    ⟨0,false,0,0,0,[]⟩

/-- The raw branch map with an untouched reference system, obtained by embedding the input,
applying the history's physical Kraus operator, and discarding the non-output qubits. -/
def mbqcRawReference {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) (R : ℕ)
    (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :=
  let F := (graphInputFrame n L) ⊗ₖ (1 : Operator R)
  let K := TensorGate (mbqcRawLeaf gs h).operator (1 : Operator R)
  graphDiscardReference n L R (graphLayoutFinal gs) (K*(F*X*Fᴴ)*Kᴴ)

/-- The logical raw branch map obtained from `mbqcRawReference` with a one-dimensional reference
system. -/
def mbqcRawBranch {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ρ : Operator (2^n)) : Operator (2^n) :=
  let Y := mbqcRawReference gs h 1 (TensorGate ρ (1 : Operator 1))
  fun i j => Y (i,0) (j,0)

/-- Decode a computational-basis label by XOR with the X component of a Pauli frame. -/
def mbqcFrameDecode {n : ℕ} (F : PauliFrame n) (i : Fin (2^n)) : Fin (2^n) :=
  bitVecEquiv n (fun w => ((bitVecEquiv n).symm i w) ^^ F.1 w)

/-- The set of physical output labels whose Pauli-frame decoding belongs to `E`. -/
def mbqcDecodedEvent {n : ℕ} (F : PauliFrame n) (E : Finset (Fin (2^n))) :
    Finset (Fin (2^n)) := Finset.univ.filter fun i => mbqcFrameDecode F i ∈ E

/-- The real part of the trace of `ρ` against the computational-basis projector onto `E`. -/
def mbqcDensityEvent {D : ℕ} (ρ : Operator D) (E : Finset (Fin D)) : ℝ :=
  (Matrix.trace (Projector E * ρ)).re

/-- Prepend Hadamard gates on all wires and the X gates specified by `x` to the reflection word
`gs`. -/
def mbqcClassicalInputWord {n : ℕ} (gs : List (ReflectionGate n)) (x : Reg n) :
    List (ReflectionGate n) :=
  (List.ofFn (fun i : Fin n => .inl (i,Hadamard))) ++
    (List.ofFn (fun i : Fin n => .inl (i,if x i then PauliX else 1))) ++ gs

/-- The graph word for classical-input preparation followed by `gs`, indexed by `8*n +
(mbqcCompiledWord gs).length` slots. -/
def mbqcInputGraph {n : ℕ} [NeZero n] (gs : List (ReflectionGate n)) (x : Reg n) :
    GraphWord n (8*n+(mbqcCompiledWord gs).length) := fun t =>
  (mbqcCompiledWord (mbqcClassicalInputWord gs x)).getD t.val (.inl (0,1))

/-- The operator obtained by applying the graph-edge gates to the all-plus pure state on all
physical qubits. -/
def mbqcAllPlusResource {n L : ℕ} (gs : GraphWord n L) : Operator (2^(n+L)) :=
  let U := graphGateProduct (graphEdgeGates gs)
  U * outerProduct (Uniform (Fin (2^(n+L)))) * Uᴴ

/-- The operator obtained by embedding an all-plus logical input and applying the fresh-qubit
and graph-edge preparation gates. -/
def mbqcPreparedResource {n L : ℕ} (gs : GraphWord n L) : Operator (2^(n+L)) :=
  let A := graphInputFrame n L
  let U := graphGateProduct (graphFreshGates n L ++ graphEdgeGates gs)
  U * (A * outerProduct (Uniform (Fin (2^n))) * Aᴴ) * Uᴴ

/-- Extract the logical output basis label from the physical bits at the final graph layout. -/
def mbqcOutputLabel {n L : ℕ} (G : GraphWord n L) (r : Fin (2^(n+L))) : Fin (2^n) :=
  bitVecEquiv n (fun i => ((bitVecEquiv (n+L)).symm r) (graphLayoutFinal G i))

/-- Execute the adaptive graph tail from a given Pauli frame, then measure the logical output
and accept exactly when its decoded label lies in `E`. -/
def mbqcReadoutTail {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n))) :
    List (Fin L) → PauliFrame n → ObservedCircuit (Fin (2^(n+L)))
  | [],F => .measure (2^n) (mbqcOutputLabel G)
      (fun y => .halt (decide (mbqcFrameDecode F y ∈ E)))
  | t::ts,F =>
    match G t with
    | .inl (i,ζ) =>
      let v := graphLayoutBefore G t i
      .step (.gate (graphPhysicalPhase n L v (if F.1 i then star ζ else ζ)))
        (.step (.gate (graphPhysicalH n L v))
          (.measure 2 (graphPhysicalLabel n L v) (fun a =>
            mbqcReadoutTail G E ts (graphWireFrame F i (boolEquivFin2.symm a)))))
    | .inr (i,j) => mbqcReadoutTail G E ts (graphCzFrame F i j)

/-- Prepare the graph resource and execute its adaptive tail with a final output measurement and
decoded event test. -/
def mbqcReadoutProgram {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n))) :
    ObservedCircuit (Fin (2^(n+L))) :=
  graphPrepend (graphFreshGates n L)
    (graphPrepend (graphEdgeGates G)
      (mbqcReadoutTail G E (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)))

/-- The readout leaf indexed by a graph history and output label, with a zero rejecting leaf as
the default for an out-of-range index. -/
def mbqcReadoutLeaf {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) : ObservedKrausLeaf (2^(n+L)) :=
  (observedKrausLeaves 1 (mbqcReadoutProgram G E)).getD
    (graphHistoryIndex G h * 2^n + y.val) ⟨0,false,0,0,0,[]⟩

/-- Embed a logical input operator into the physical register using `graphInputFrame`. -/
def mbqcPhysicalInput {n L : ℕ} (_G : GraphWord n L) (ρ : Operator (2^n)) :
    Operator (2^(n+L)) := graphInputFrame n L * ρ * (graphInputFrame n L)ᴴ

/-- The sum of the masses of accepted mixed traces of the graph readout program on the embedded
logical input. -/
def mbqcReadoutAcceptance {n L : ℕ} (G : GraphWord n L) (E : Finset (Fin (2^n)))
    (ρ : Operator (2^n)) : ℝ :=
  (((observedMixedTraces 1 (mbqcReadoutProgram G E) (mbqcPhysicalInput G ρ)).filter
    (fun t => t.accepted)).map mixedMass).sum

end Qatlib.Concepts.InstrumentCore.PatternCompile
