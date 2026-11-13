/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachine
import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeStandardDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGate
import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGateDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardDefs

/-!
# Local quantum Turing machine simulation data

This module defines register projections, bounded address-word compilation, and finite-window
configurations for local quantum Turing machine simulations. `LayerState`, `CellState`, and
`AllCellState` describe gate layers on one cell, a selected cell, and a tour of all input cells,
respectively, in the circuit and machine setting of [BernsteinVazirani1997].

The configuration lemmas describe tape updates and control states explicitly. `TensorState`,
`tourAmps`, and `compositeCellCircuit` express the corresponding independent-wire circuit
semantics, while `DLambdaBitTMUniformity` records a bit-tape uniformity specification.

## Main definitions

* `allCellStep`: local transition amplitudes for a tour of the input cells.
* `allCellTourCfg`: configurations carrying the processed prefix of a tour.
* `HeadStayLightconeSpec`: a circuit simulation specification with acceptance-probability
  equality.
* `amplificationCopies`: an odd repetition count for error reduction.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachine
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option autoImplicit false

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal
namespace QtmUniform

open Matrix

/-- Restrict a register on `n + m` wires to its `n` address wires. -/
def addrPart {n m : ℕ} (x : Reg (n + m)) : Reg n :=
  fun w => x (addrWire m w)

/-- Restrict a register on `n + m` wires to its `m` ancillary wires. -/
def ancPart {n m : ℕ} (x : Reg (n + m)) : Reg m :=
  fun a => x (ancWire n a)

/-- Compile an address word into bounded gates by concatenating the multi-controlled NOT
programs for its operations. -/
def addrWordBounded {n : ℕ} : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n →
    List (BoundedGate (n + (n - 1)))
  | [] => []
  | g :: l => mcxProgram g.target g.pattern ++ addrWordBounded l

/-- The ancillary wire count `n - 1` used to compile an address word on `n` wires. -/
def addrWordBoundedAncillas {n : ℕ} (_w : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n) : ℕ :=
    n - 1

/-- The set of input positions queried on Alice's side by a communication decision list. -/
def alicePositions {m : ℕ} (P : CommDecisionList m) : Finset (Fin m) :=
  ((P.queries.toFinset).filter (fun q => q.1 = true)).image (fun q => q.2)

/-- The set of input positions queried on Bob's side by a communication decision list. -/
def bobPositions {m : ℕ} (P : CommDecisionList m) : Finset (Fin m) :=
  ((P.queries.toFinset).filter (fun q => q.1 = false)).image (fun q => q.2)

/-- The finite set of variables occurring in a Boolean formula. -/
def formulaVars {n : ℕ} : BoolFormula (Fin n) → Finset (Fin n)
  | .var v => {v}
  | .not f => formulaVars f
  | .and f g => formulaVars f ∪ formulaVars g
  | .or f g => formulaVars f ∪ formulaVars g

/-- The set of wire indices at which a Boolean register is `true`. -/
def regSupport {n : ℕ} (x : Reg n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

/-- The Boolean register whose true entries are exactly the members of a given finite set. -/
def regOfSet {n : ℕ} (S : Finset (Fin n)) : Reg n := fun j => decide (j ∈ S)

/-- The first `k` indices of `Fin n`, embedded using the bound `k ≤ n`. -/
def firstIndices {n : ℕ} (k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)

/-- The transition amplitude `U b a` for a stationary head move, and zero for other moves. -/
def gateStep (U : Matrix Bool Bool ℂ) (a : Bool) (d : QtmMove) (b : Bool) : ℂ :=
  if d = QtmMove.stay then U b a else 0

/-- The one-state local transition function obtained from the stationary single-qubit gate `U`. -/
def gateStepFn (U : Matrix Bool Bool ℂ) : Unit → Bool → QtmMove → Unit → Bool → ℂ :=
  fun _ a d _ b => gateStep U a d b

/-- Replace the tape symbol at the current head position by `b`. -/
def writeHead {w : ℕ} {Q A : Type} (c : WindowCfg w Q A) (b : A) : WindowCfg w Q A :=
  { c with tape := fun j => if j = c.head then b else c.tape j }

/-- Control states for entering the input cell, executing `k` gate layers, and performing
acceptance and rejection transitions. -/
inductive LayerState (k : ℕ) where
  | toInput : LayerState k
  | layer (i : Fin (k + 1)) : LayerState k
  | acc : LayerState k
  | rej : LayerState k
  | meas2 : LayerState k
  deriving DecidableEq, Fintype

/-- The control-state update for the layered machine, advancing through the layers and branching
on the read bit at measurement. -/
def layerNext {k : ℕ} : LayerState k → Bool → LayerState k
  | .toInput, _ => .layer 0
  | .layer i, a =>
      if h : i.val < k then .layer ⟨i.val + 1, by omega⟩ else (if a then .acc else .rej)
  | .acc, _ => .meas2
  | .rej, _ => .toInput
  | .meas2, a => if a then .acc else .rej

/-- The layered machine's head move: right when entering the input cell and stationary
otherwise. -/
def layerMove {k : ℕ} : LayerState k → QtmMove
  | .toInput => .right
  | _ => .stay

/-- The symbol transition amplitudes for the layered machine, using the specified gates before
the final bit flip. -/
def layerAmp {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ) : LayerState k → Bool → Bool → ℂ
  | .layer i, a, b => if h : i.val < k then Us ⟨i.val, h⟩ b a else (if b = !a then 1 else 0)
  | _, a, b => if b = a then 1 else 0

/-- The layered machine's local transition amplitudes, supported on its prescribed head move and
control-state update. -/
def layerStep {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ) :
    LayerState k → Bool → QtmMove → LayerState k → Bool → ℂ :=
  fun q a d q' b => if d = layerMove q ∧ q' = layerNext q a then layerAmp Us q a b else 0

/-- The layer state at index `k`, immediately after the `k` specified gates. -/
def measState (k : ℕ) : LayerState k := .layer ⟨k, by omega⟩

/-- The chronological product of the first `j` gates, with each new gate multiplying on the
left. -/
noncomputable def gateSeqProd {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ) : (j : ℕ) → j ≤ k →
    Matrix Bool Bool ℂ
  | 0, _ => 1
  | j + 1, hj => Us ⟨j, by omega⟩ * gateSeqProd Us j (by omega)

/-- Set the control state and head symbol of a base configuration while preserving its head
position and all other tape cells. -/
def layerCfg {k w : ℕ} (base : WindowCfg w (LayerState k) Bool) (q : LayerState k)
    (b : Bool) : WindowCfg w (LayerState k) Bool :=
  { base with state := q, tape := fun j => if j = base.head then b else base.tape j }

/-- The superposition of the two head-symbol configurations in layer `j`, with amplitudes given
by `v`. -/
def layerCfgSuper {k w : ℕ} (base : WindowCfg w (LayerState k) Bool) (j : ℕ) (hj : j ≤ k)
    (v : Bool → ℂ) : QState (WindowCfg w (LayerState k) Bool) :=
  v false • Ket (layerCfg base (.layer ⟨j, by omega⟩) false) +
    v true • Ket (layerCfg base (.layer ⟨j, by omega⟩) true)

/-- Move the head one cell to the right and enter layer zero, using the window-bound hypothesis. -/
def layerWalkCfg {k w : ℕ} (src : WindowCfg w (LayerState k) Bool)
    (hedge : src.head.val < 2 * w) : WindowCfg w (LayerState k) Bool :=
  { src with head := ⟨src.head.val + 1, by omega⟩, state := .layer 0 }

/-- Place the head at `h'` and enter layer zero without changing the tape. -/
def layerWalk {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (h' : Fin (2 * w + 1)) : WindowCfg w (LayerState k) Bool :=
  { base with head := h', state := .layer 0 }

/-- The two layer-entry configurations agree when `h'` is the next head position. -/
theorem layerWalk_eq_layerWalkCfg {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (h' : Fin (2 * w + 1)) (hh : h'.val = base.head.val + 1)
    (hedge : base.head.val < 2 * w) :
    layerWalk base h' = layerWalkCfg base hedge := by
  have heq : h' = ⟨base.head.val + 1, by omega⟩ := Fin.ext hh
  simp only [layerWalk, layerWalkCfg]
  rw [heq]

/-- The equivalence between a one-wire Boolean register and its unique bit. -/
def reg1Bool : Reg 1 ≃ Bool where
  toFun x := x ⟨0, by omega⟩
  invFun b := fun _ => b
  left_inv x := by
    funext j
    have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
    rw [hj]
  right_inv b := rfl

/-- Reindex a matrix on one-wire registers as a matrix on Boolean bits. -/
def reg1Gate (U : Matrix (Reg 1) (Reg 1) ℂ) : Matrix Bool Bool ℂ :=
  fun b a => U (reg1Bool.symm b) (reg1Bool.symm a)

/-- Reindex a matrix on Boolean bits as a matrix on one-wire registers. -/
def reg1Gate' (U : Matrix Bool Bool ℂ) : Matrix (Reg 1) (Reg 1) ℂ :=
  fun i j => U (reg1Bool i) (reg1Bool j)

/-- The computational-basis amplitude function of the bit stored in a one-wire register. -/
def wireAmp (x : Reg 1) : Bool → ℂ := fun c => if c = x ⟨0, by omega⟩ then 1 else 0

/-- The chronological product of a list of single-qubit matrices, with the first list entry
acting first. -/
noncomputable def boolGateProd : List (Matrix Bool Bool ℂ) → Matrix Bool Bool ℂ
  | [] => 1
  | U :: l => boolGateProd l * U

/-- Replace wire zero of a register by `b`, leaving every other wire unchanged. -/
def setBit0 {n : ℕ} (x : Reg n) (b : Bool) : Reg n :=
  fun j => if j.val = 0 then b else x j

/-- Flip wire zero of a nonempty register. -/
def flip0 {n : ℕ} (hn : 0 < n) (x : Reg n) : Reg n := setBit0 x (!x ⟨0, hn⟩)

/-- Two registers agree at every wire other than wire zero. -/
abbrev AgreesOutside {n : ℕ} (x y : Reg n) : Prop :=
  ∀ j : Fin n, j.val ≠ 0 → y j = x j

/-- The complex-valued indicator that two registers agree outside wire zero. -/
def agreesOutside {n : ℕ} (x y : Reg n) : ℂ :=
  if AgreesOutside x y then 1 else 0

/-- Embed a single-qubit matrix on wire zero, with zero entries between registers that differ
elsewhere. -/
def embedReg1 {n : ℕ} (hn : 0 < n) (U : Matrix Bool Bool ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  fun y z => if AgreesOutside y z then U (y ⟨0, hn⟩) (z ⟨0, hn⟩) else 0

/-- A state has amplitudes `c` on wire zero and is fixed to the register `x` on every other
wire. -/
def FirstWireState {n : ℕ} (hn : 0 < n) (x : Reg n) (c : Bool → ℂ) (ψ : Reg n → ℂ) : Prop :=
  ∀ y : Reg n, ψ y = c (y ⟨0, hn⟩) * agreesOutside x y

/-- The equivalence that prepends a Boolean bit to a Boolean register of length `n`. -/
def finBoolCons (n : ℕ) : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) :=
  Fin.consEquiv (fun _ => Bool)

/-- Control states for walking to a target cell, executing its gate layers, and recording
acceptance or rejection. -/
inductive CellState (n k tgt : ℕ) where
  | walk (d : Fin (tgt + 1)) : CellState n k tgt
  | gate (j : Fin (k + 1)) : CellState n k tgt
  | acc : CellState n k tgt
  | rej : CellState n k tgt
  | meas2 : CellState n k tgt
  deriving DecidableEq, Fintype

/-- The control-state update for the target-cell machine, including its walk, gate sequence, and
read-bit branches. -/
def cellNext {n k tgt : ℕ} : CellState n k tgt → Bool → CellState n k tgt
  | .walk d, _ =>
      if h : d.val = tgt then .gate ⟨0, by omega⟩ else .walk ⟨d.val + 1, by omega⟩
  | .gate j, a =>
      if h : j.val < k then .gate ⟨j.val + 1, by omega⟩ else (if a then .acc else .rej)
  | .acc, _ => .meas2
  | .rej, _ => .walk ⟨0, by omega⟩
  | .meas2, a => if a then .acc else .rej

/-- The target-cell machine moves right during the walk phase and stays in place in all other
states. -/
def cellMove {n k tgt : ℕ} : CellState n k tgt → QtmMove
  | .walk _ => .right
  | _ => .stay

/-- The target-cell machine's symbol amplitudes, applying the target's gates and then a final
bit flip. -/
def cellAmp {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (htgt : tgt < n) :
    CellState n k tgt → Bool → Bool → ℂ
  | .gate j, a, b =>
      if h : j.val < k then V ⟨tgt, htgt⟩ ⟨j.val, h⟩ b a else (if b = !a then 1 else 0)
  | _, a, b => if b = a then 1 else 0

/-- The target-cell machine's local transition function, combining its control update, head
move, and symbol amplitudes. -/
def cellStep {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (htgt : tgt < n) :
    CellState n k tgt → Bool → QtmMove → CellState n k tgt → Bool → ℂ :=
  fun q a d q' b =>
    if d = cellMove q ∧ q' = cellNext q a then cellAmp V htgt q a b else 0

/-- Control states for a tour that serves every input cell through its gate layers, with
acceptance, rejection, and restart states. -/
inductive AllCellState (n k : ℕ) where
  | start : AllCellState n k
  | serve (i : Fin n) (j : Fin (k + 1)) : AllCellState n k
  | acc : AllCellState n k
  | rej : AllCellState n k
  | meas2 : AllCellState n k
  | restart : AllCellState n k
  deriving DecidableEq, Fintype

/-- Advance the all-cell tour through gate layers and cells, branching on the read bit after the
final cell. -/
def allCellNext {n k : ℕ} (hn : 0 < n) : AllCellState n k → Bool → AllCellState n k
  | .start, _ => .serve ⟨0, hn⟩ ⟨0, by omega⟩
  | .serve i j, a =>
      if h : j.val < k then .serve i ⟨j.val + 1, by omega⟩
      else if hi : i.val + 1 < n then .serve ⟨i.val + 1, by omega⟩ ⟨0, by omega⟩
      else (if a then .acc else .rej)
  | .acc, _ => .meas2
  | .rej, _ => .restart
  | .meas2, a => if a then .acc else .rej
  | .restart, _ => .start

/-- The all-cell tour's head move, advancing right on entry and between cells and staying during
gate execution. -/
def allCellMove {n k : ℕ} : AllCellState n k → QtmMove
  | .start => .right
  | .serve i j => if j.val < k then .stay else if i.val + 1 < n then .right else .stay
  | _ => .stay

/-- The all-cell tour's symbol amplitudes, applying each cell's gates and flipping the bit at
the final readout transition. -/
def allCellAmp {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) :
    AllCellState n k → Bool → Bool → ℂ
  | .start, a, b => if b = a then 1 else 0
  | .serve i j, a, b =>
      if h : j.val < k then V i ⟨j.val, h⟩ b a
      else if i.val + 1 < n then (if b = a then 1 else 0)
      else (if b = !a then 1 else 0)
  | _, a, b => if b = a then 1 else 0

/-- The all-cell tour's local transition function, supported on the prescribed control update
and head move. -/
def allCellStep {n k : ℕ} (hn : 0 < n) (V : Fin n → Fin k → Matrix Bool Bool ℂ) :
    AllCellState n k → Bool → QtmMove → AllCellState n k → Bool → ℂ :=
  fun q a d q' b =>
    if d = allCellMove q ∧ q' = allCellNext hn q a then allCellAmp V q a b else 0

/-- Replace the head symbol of an all-cell configuration by a specified read bit. -/
def allCellReadCfg {n k w : ℕ} (src : WindowCfg w (AllCellState n k) Bool) (a : Bool) :
    WindowCfg w (AllCellState n k) Bool :=
  { src with tape := fun j => if j = src.head then a else src.tape j }

/-- Construct an all-cell successor with the prescribed next control state, head position, and
written symbol. -/
def allCellSuccCfg {n k w : ℕ} (hn : 0 < n)
    (src : WindowCfg w (AllCellState n k) Bool) (a b : Bool) (h' : Fin (2 * w + 1)) :
    WindowCfg w (AllCellState n k) Bool :=
  WindowCfg.mk h' (allCellNext hn src.state a) (fun j => if j = src.head then b else src.tape j)

/-- Construct a serving configuration for cell `i` and layer `j`, with head `h` carrying bit
`b`. -/
def allCellServeCfg {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (h : Fin (2 * w + 1)) (i : Fin n) (j : Fin (k + 1)) (b : Bool) :
    WindowCfg w (AllCellState n k) Bool :=
  WindowCfg.mk h (.serve i j) (fun j => if j = h then b else base.tape j)

/-- The superposition of the two serving configurations at a fixed cell, layer, and head
position. -/
def allCellServeSuper {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (h : Fin (2 * w + 1)) (i : Fin n) (j : Fin (k + 1)) (v : Bool → ℂ) :
    QState (WindowCfg w (AllCellState n k) Bool) :=
  v false • Ket (allCellServeCfg base h i j false) +
    v true • Ket (allCellServeCfg base h i j true)

/-- The start-state configuration with the base head position and tape. -/
def allCellStartCfg {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool) :
    WindowCfg w (AllCellState n k) Bool :=
  WindowCfg.mk base.head (.start : AllCellState n k)
    (fun j => if j = base.head then base.tape base.head else base.tape j)

/-- The initial serving configuration at cell zero and layer zero, with head position `h'`. -/
def allCellStartStepCfg {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h' : Fin (2 * w + 1)) :
    WindowCfg w (AllCellState n k) Bool :=
  { base with head := h', state := .serve ⟨0, hn⟩ ⟨0, by omega⟩ }

/-- The configuration that starts layer zero at the next cell with head position `h'`. -/
def allCellAdvanceCfg {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : Fin n) (hi : i.val + 1 < n) (h' : Fin (2 * w + 1)) :
    WindowCfg w (AllCellState n k) Bool :=
  { base with head := h', state := .serve ⟨i.val + 1, by omega⟩ ⟨0, by omega⟩ }

/-- Replacing the read bit preserves the control state. -/
theorem allCellReadCfg_state {n k w : ℕ} (src : WindowCfg w (AllCellState n k) Bool)
    (a : Bool) : (allCellReadCfg src a).state = src.state := rfl

/-- Replacing the read bit preserves the head position. -/
theorem allCellReadCfg_head {n k w : ℕ} (src : WindowCfg w (AllCellState n k) Bool)
    (a : Bool) : (allCellReadCfg src a).head = src.head := rfl

/-- The read configuration carries `a` at its head position. -/
theorem allCellReadCfg_tape_at {n k w : ℕ} (src : WindowCfg w (AllCellState n k) Bool)
    (a : Bool) : (allCellReadCfg src a).tape (allCellReadCfg src a).head = a := by
  simp [allCellReadCfg]

/-- The read configuration's tape differs from the source only by writing `a` at the source
head. -/
theorem allCellReadCfg_tape {n k w : ℕ} (src : WindowCfg w (AllCellState n k) Bool)
    (a : Bool) (j : Fin (2 * w + 1)) :
    (allCellReadCfg src a).tape j = if j = src.head then a else src.tape j := rfl

/-- An all-cell successor writes `b` at the source head position. -/
theorem allCellSuccCfg_tape_at {n k w : ℕ} (hn : 0 < n)
    (src : WindowCfg w (AllCellState n k) Bool) (a b : Bool) (h' : Fin (2 * w + 1)) :
    (allCellSuccCfg hn src a b h').tape src.head = b := by
  have h : (allCellSuccCfg hn src a b h').tape src.head
      = (if src.head = src.head then b else src.tape src.head) := rfl
  rw [h, if_pos rfl]

/-- The successor tape writes `b` at the source head and preserves every other cell. -/
theorem allCellSuccCfg_tape {n k w : ℕ} (hn : 0 < n)
    (src : WindowCfg w (AllCellState n k) Bool) (a b : Bool) (h' : Fin (2 * w + 1))
    (j : Fin (2 * w + 1)) :
    (allCellSuccCfg hn src a b h').tape j = if j = src.head then b else src.tape j := rfl

/-- The serving configuration writes `b` at `h` and uses the base tape elsewhere. -/
theorem allCellServeCfg_tape {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (h : Fin (2 * w + 1)) (i : Fin n) (j : Fin (k + 1)) (b : Bool)
    (m : Fin (2 * w + 1)) :
    (allCellServeCfg base h i j b).tape m = if m = h then b else base.tape m := rfl

/-- The serving configuration has control state `serve i j`. -/
theorem allCellServeCfg_state {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (h : Fin (2 * w + 1)) (i : Fin n) (j : Fin (k + 1)) (b : Bool) :
    (allCellServeCfg base h i j b).state = (.serve i j : AllCellState n k) := rfl

/-- The serving configuration has head position `h`. -/
theorem allCellServeCfg_head {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (h : Fin (2 * w + 1)) (i : Fin n) (j : Fin (k + 1)) (b : Bool) :
    (allCellServeCfg base h i j b).head = h := rfl

/-- The symbol at the serving configuration's head is `b`. -/
theorem allCellServeCfg_tape_at {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (h : Fin (2 * w + 1)) (i : Fin n) (j : Fin (k + 1)) (b : Bool) :
    (allCellServeCfg base h i j b).tape (allCellServeCfg base h i j b).head = b := by
  rw [allCellServeCfg_head]
  rw [show (allCellServeCfg base h i j b).tape h
      = (if h = h then b else base.tape h) from rfl, if_pos rfl]

/-- The start configuration's tape is the base tape, expressed as an update by its existing head
symbol. -/
theorem allCellStartCfg_tape {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (m : Fin (2 * w + 1)) :
    (allCellStartCfg base).tape m = if m = base.head then base.tape base.head else base.tape m := rfl

/-- The start configuration has the base head position. -/
theorem allCellStartCfg_head {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool) :
    (allCellStartCfg base).head = base.head := rfl

/-- The start configuration has control state `start`. -/
theorem allCellStartCfg_state {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool) :
    (allCellStartCfg base).state = (.start : AllCellState n k) := rfl

/-- The start configuration preserves the base head symbol. -/
theorem allCellStartCfg_tape_at {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool) :
    (allCellStartCfg base).tape (allCellStartCfg base).head = base.tape base.head := by
  rw [allCellStartCfg_head]
  rw [show (allCellStartCfg base).tape base.head
      = (if base.head = base.head then base.tape base.head else base.tape base.head) from rfl,
    if_pos rfl]

/-- The first step configuration serves cell zero at layer zero. -/
theorem allCellStartStepCfg_state {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h' : Fin (2 * w + 1)) :
    (allCellStartStepCfg hn base h').state = (.serve ⟨0, hn⟩ ⟨0, by omega⟩ : AllCellState n k) := rfl

/-- The first step configuration has head position `h'`. -/
theorem allCellStartStepCfg_head {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h' : Fin (2 * w + 1)) :
    (allCellStartStepCfg hn base h').head = h' := rfl

/-- Entering the first serving state preserves the base tape. -/
theorem allCellStartStepCfg_tape {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h' : Fin (2 * w + 1))
    (m : Fin (2 * w + 1)) :
    (allCellStartStepCfg hn base h').tape m = base.tape m := rfl

/-- The advance configuration serves cell `i + 1` at layer zero. -/
theorem allCellAdvanceCfg_state {n k w : ℕ}
    (base : WindowCfg w (AllCellState n k) Bool)
    (i : Fin n) (hi : i.val + 1 < n) (h' : Fin (2 * w + 1)) :
    (allCellAdvanceCfg base i hi h').state
      = (.serve ⟨i.val + 1, by omega⟩ ⟨0, by omega⟩ : AllCellState n k) := rfl

/-- The advance configuration has head position `h'`. -/
theorem allCellAdvanceCfg_head {n k w : ℕ}
    (base : WindowCfg w (AllCellState n k) Bool)
    (i : Fin n) (hi : i.val + 1 < n) (h' : Fin (2 * w + 1)) :
    (allCellAdvanceCfg base i hi h').head = h' := rfl

/-- Advancing to the next cell preserves the base tape. -/
theorem allCellAdvanceCfg_tape {n k w : ℕ}
    (base : WindowCfg w (AllCellState n k) Bool)
    (i : Fin n) (hi : i.val + 1 < n) (h' : Fin (2 * w + 1))
    (m : Fin (2 * w + 1)) :
    (allCellAdvanceCfg base i hi h').tape m = base.tape m := rfl

/-- The successor control state is given by `allCellNext` applied to the source state and read
bit. -/
theorem allCellSuccCfg_state {n k w : ℕ} (hn : 0 < n)
    (src : WindowCfg w (AllCellState n k) Bool) (a b : Bool) (h' : Fin (2 * w + 1)) :
    (allCellSuccCfg hn src a b h').state = allCellNext hn src.state a := rfl

/-- The all-cell successor has the specified head position `h'`. -/
theorem allCellSuccCfg_head {n k w : ℕ} (hn : 0 < n)
    (src : WindowCfg w (AllCellState n k) Bool) (a b : Bool) (h' : Fin (2 * w + 1)) :
    (allCellSuccCfg hn src a b h').head = h' := rfl

/-- A successor of a serving configuration replaces its head bit by `b` and preserves the base
tape elsewhere. -/
theorem allCellSuccCfg_serve_tape {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (a b : Bool) (m : Fin (2 * w + 1)) :
    (allCellSuccCfg hn (allCellServeCfg base h i j a) a b h).tape m
      = if m = h then b else base.tape m := by
  have hh : (allCellServeCfg base h i j a).head = h := allCellServeCfg_head base h i j a
  have h1 : (allCellSuccCfg hn (allCellServeCfg base h i j a) a b h).tape m
      = (if m = (allCellServeCfg base h i j a).head then b
          else (allCellServeCfg base h i j a).tape m) := allCellSuccCfg_tape hn _ _ _ _ m
  rw [h1, hh]
  by_cases hm : m = h
  · simp only [if_pos hm]
  · simp only [if_neg hm]
    rw [allCellServeCfg_tape base h i j a m, if_neg hm]

/-- A successor of the start configuration that rewrites the existing head symbol preserves the
base tape. -/
theorem allCellSuccCfg_start_tape {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h' : Fin (2 * w + 1))
    (m : Fin (2 * w + 1)) :
    (allCellSuccCfg hn (allCellStartCfg base) (base.tape base.head) (base.tape base.head) h').tape m
      = base.tape m := by
  have hh : (allCellStartCfg base).head = base.head := allCellStartCfg_head base
  have h1 : (allCellSuccCfg hn (allCellStartCfg base) (base.tape base.head)
        (base.tape base.head) h').tape m
      = (if m = (allCellStartCfg base).head then base.tape base.head
          else (allCellStartCfg base).tape m) := allCellSuccCfg_tape hn _ _ _ _ m
  rw [h1, hh]
  by_cases hm : m = base.head
  · simp only [if_pos hm]
    rw [hm]
  · simp only [if_neg hm]
    rw [allCellStartCfg_tape base m, if_neg hm]

/-- A successor that rewrites a serving configuration's existing head symbol preserves the base
tape. -/
theorem allCellSuccCfg_advance_tape {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (h' : Fin (2 * w + 1)) (m : Fin (2 * w + 1)) :
    (allCellSuccCfg hn (allCellServeCfg base h i j (base.tape h)) (base.tape h)
        (base.tape h) h').tape m
      = base.tape m := by
  have hh : (allCellServeCfg base h i j (base.tape h)).head = h :=
    allCellServeCfg_head base h i j (base.tape h)
  have h1 : (allCellSuccCfg hn (allCellServeCfg base h i j (base.tape h)) (base.tape h)
        (base.tape h) h').tape m
      = (if m = (allCellServeCfg base h i j (base.tape h)).head then base.tape h
          else (allCellServeCfg base h i j (base.tape h)).tape m) :=
    allCellSuccCfg_tape hn _ _ _ _ m
  rw [h1, hh]
  by_cases hm : m = h
  · simp only [if_pos hm]
    rw [hm]
  · simp only [if_neg hm]
    rw [allCellServeCfg_tape base h i j (base.tape h) m, if_neg hm]

/-- The window position `w + 1 + i` corresponding to input cell `i`. -/
def allCellTourPos {n w : ℕ} (i : ℕ) (hi : i < n) (hw : n ≤ w) : Fin (2 * w + 1) :=
  ⟨w + 1 + i, by omega⟩

/-- Extend a Boolean function on `Fin i` by assigning the last coordinate the value `a`. -/
def Fin.extendLast {i : ℕ} (f : Fin i → Bool) (a : Bool) : Fin (i + 1) → Bool :=
  fun j => if h : j.val = i then a else f ⟨j.val, by omega⟩

/-- The tape obtained by writing a processed prefix into positions `w + 1` through `w + i` of
the base tape. -/
def allCellTourTape {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (f : Fin i → Bool) : Fin (2 * w + 1) → Bool :=
  fun m => if h : w + 1 ≤ m.val ∧ m.val ≤ w + i
    then f ⟨m.val - w - 1, by rcases h with ⟨h1, h2⟩; omega⟩
    else base.tape m

/-- Within the processed prefix, the tour tape reads the corresponding entry of `f`. -/
theorem allCellTourTape_of_in {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (f : Fin i → Bool) (m : Fin (2 * w + 1)) (h1 : w + 1 ≤ m.val) (h2 : m.val ≤ w + i) :
    allCellTourTape base i f m = f ⟨m.val - w - 1, by omega⟩ := by
  have h : w + 1 ≤ m.val ∧ m.val ≤ w + i := ⟨h1, h2⟩
  simp only [allCellTourTape]
  rw [dif_pos h]

/-- Outside the processed prefix, the tour tape agrees with the base tape. -/
theorem allCellTourTape_of_lt {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (f : Fin i → Bool) (m : Fin (2 * w + 1))
    (h : ¬ (w + 1 ≤ m.val ∧ m.val ≤ w + i)) :
    allCellTourTape base i f m = base.tape m := by
  simp only [allCellTourTape]
  rw [dif_neg h]

/-- Extending the processed prefix by `a` changes only position `w + 1 + i`. -/
theorem allCellTourTape_extend {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (f : Fin i → Bool) (a : Bool) (m : Fin (2 * w + 1)) :
    allCellTourTape base (i + 1) (Fin.extendLast f a) m
      = if m.val = w + 1 + i then a else allCellTourTape base i f m := by
  by_cases hin : w + 1 ≤ m.val ∧ m.val ≤ w + i
  · have hne : m.val ≠ w + 1 + i := by omega
    have h1 : w + 1 ≤ m.val := by omega
    have h2 : m.val ≤ w + (i + 1) := by omega
    have h3 : m.val - w - 1 ≠ i := by omega
    rw [allCellTourTape_of_in base (i + 1) (Fin.extendLast f a) m h1 h2]
    rw [if_neg hne]
    rw [allCellTourTape_of_in base i f m (by omega) (by omega)]
    simp [Fin.extendLast, h3]
  · by_cases heq : m.val = w + 1 + i
    · have h1 : w + 1 ≤ m.val := by omega
      have h2 : m.val ≤ w + (i + 1) := by omega
      have hsub : m.val - w - 1 = i := by omega
      rw [allCellTourTape_of_in base (i + 1) (Fin.extendLast f a) m h1 h2]
      rw [if_pos heq]
      simp [Fin.extendLast, hsub]
    · have h1 : ¬ (w + 1 ≤ m.val ∧ m.val ≤ w + (i + 1)) := by omega
      rw [allCellTourTape_of_lt base (i + 1) (Fin.extendLast f a) m h1]
      rw [if_neg heq]
      rw [allCellTourTape_of_lt base i f m hin]

/-- Construct a serving configuration at cell `i`, retaining the processed prefix and setting
the current cell to `b`. -/
def allCellTourCfg {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (f : Fin i → Bool) (b : Bool) :
    WindowCfg w (AllCellState n k) Bool :=
  WindowCfg.mk (allCellTourPos i hi hw) (.serve ⟨i, hi⟩ j)
    (fun m => if m = allCellTourPos i hi hw then b else allCellTourTape base i f m)

/-- The tour configuration's head is at the position corresponding to cell `i`. -/
theorem allCellTourCfg_head {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (f : Fin i → Bool) (b : Bool) :
    (allCellTourCfg base i hi hw j f b).head = allCellTourPos i hi hw := rfl

/-- The tour configuration serves cell `i` at layer `j`. -/
theorem allCellTourCfg_state {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (f : Fin i → Bool) (b : Bool) :
    (allCellTourCfg base i hi hw j f b).state = (.serve ⟨i, hi⟩ j : AllCellState n k) := rfl

/-- The tour configuration's tape writes `b` at its current cell and otherwise agrees with the
processed-prefix tape. -/
theorem allCellTourCfg_tape {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (f : Fin i → Bool) (b : Bool)
    (m : Fin (2 * w + 1)) :
    (allCellTourCfg base i hi hw j f b).tape m
      = if m = allCellTourPos i hi hw then b else allCellTourTape base i f m := rfl

/-- The tour configuration's head symbol is `b`. -/
theorem allCellTourCfg_tape_at {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (f : Fin i → Bool) (b : Bool) :
    (allCellTourCfg base i hi hw j f b).tape (allCellTourCfg base i hi hw j f b).head = b := by
  rw [allCellTourCfg_head]
  rw [allCellTourCfg_tape]
  rw [if_pos rfl]

/-- Layer zero as an element of `Fin (k + 1)`. -/
def allCellTourLayer0 (k : ℕ) : Fin (k + 1) := ⟨0, by omega⟩

/-- The final layer index `k` as an element of `Fin (k + 1)`. -/
def allCellTourLayerK (k : ℕ) : Fin (k + 1) := ⟨k, by omega⟩

/-- The window position `w + 2 + i` for the cell after `i`. -/
def allCellTourPosNext {n w : ℕ} (i : ℕ) (hnext : i + 1 < n) (hw : n ≤ w) :
    Fin (2 * w + 1) :=
  ⟨w + 2 + i, by omega⟩

/-- The natural-number value of the tour position is `w + 1 + i`. -/
theorem allCellTourPos_val {n w : ℕ} (i : ℕ) (hi : i < n) (hw : n ≤ w) :
    (allCellTourPos i hi hw).val = w + 1 + i := rfl

/-- The natural-number value of the next tour position is `w + 2 + i`. -/
theorem allCellTourPosNext_val {n w : ℕ} (i : ℕ) (hnext : i + 1 < n) (hw : n ≤ w) :
    (allCellTourPosNext i hnext hw).val = w + 2 + i := rfl

/-- The next-position construction agrees with the tour position of cell `i + 1`. -/
theorem allCellTourPosNext_eq {n w : ℕ} (i : ℕ) (hnext : i + 1 < n) (hw : n ≤ w) :
    allCellTourPosNext i hnext hw = allCellTourPos (i + 1) hnext hw := by
  apply Fin.ext
  simp only [allCellTourPos_val, allCellTourPosNext_val]
  omega

/-- The tour tape preserves the base symbol at the next cell beyond the processed prefix. -/
theorem allCellTourTape_at_next {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hnext : i + 1 < n) (hw : n ≤ w) (f : Fin i → Bool) :
    allCellTourTape base i f (allCellTourPos (i + 1) hnext hw)
      = base.tape (allCellTourPos (i + 1) hnext hw) := by
  have hval : w + i < (allCellTourPos (i + 1) hnext hw).val := by
    rw [allCellTourPos_val]
    omega
  rw [allCellTourTape_of_lt base i f _ (by omega)]

/-- A window index with value `w + 1 + i` equals the tour position of cell `i`. -/
theorem allCellTourPos_eq_of_val {n w : ℕ} (i : ℕ) (hi : i < n) (hw : n ≤ w)
    (m : Fin (2 * w + 1)) (h : m.val = w + 1 + i) : m = allCellTourPos i hi hw := by
  have h' : m.val = (allCellTourPos i hi hw).val := by
    rw [allCellTourPos_val]
    exact h
  exact Fin.ext h'

/-- Construct a final configuration whose acceptance state is selected by `a`, with current
symbol `b` and the processed prefix retained. -/
def allCellTourFinalCfg {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (f : Fin i → Bool) (a : Bool) (b : Bool) :
    WindowCfg w (AllCellState n k) Bool :=
  WindowCfg.mk (allCellTourPos i hi hw) (if a then (.acc : AllCellState n k) else .rej)
    (fun m => if m = allCellTourPos i hi hw then b else allCellTourTape base i f m)

/-- The equivalence between a Boolean prefix paired with its last bit and a Boolean register one
coordinate longer. -/
def allCellPrefixSuccEquiv (i : ℕ) : (Fin i → Bool) × Bool ≃ (Fin (i + 1) → Bool) where
  toFun p := Fin.extendLast p.1 p.2
  invFun g := (fun j => g ⟨j.val, by omega⟩, g ⟨i, by omega⟩)
  left_inv := by
    intro p
    obtain ⟨f, a⟩ := p
    apply Prod.ext
    · funext j
      have hj : j.val ≠ i := by omega
      simp [Fin.extendLast, hj]
    · simp [Fin.extendLast]
  right_inv := by
    intro g
    funext j
    by_cases hj : j.val = i
    · have hjeq : j = ⟨i, by omega⟩ := by
        apply Fin.ext
        exact hj
      rw [hjeq]
      simp [Fin.extendLast]
    · simp [Fin.extendLast, hj]

/-- Reindex a complex-valued sum over a Boolean prefix and one bit as a sum over the extended
register. -/
theorem fin_sum_extendLast {i : ℕ} (A : (Fin i → Bool) → Bool → ℂ) :
    (∑ f : Fin i → Bool, ∑ b : Bool, A f b)
      = ∑ f' : Fin (i + 1) → Bool,
          A ((allCellPrefixSuccEquiv i).symm f').1 ((allCellPrefixSuccEquiv i).symm f').2 := by
  rw [Equiv.sum_comp ((allCellPrefixSuccEquiv i).symm) (fun y => A y.1 y.2)]
  rw [Fintype.sum_prod_type]

/-- Reindex a sum in any additive commutative monoid over a Boolean prefix and one bit as a sum
over the extended register. -/
theorem fin_sum_extendLast_state {i : ℕ} {S : Type*} [AddCommMonoid S]
    (A : (Fin i → Bool) → Bool → S) :
    (∑ f : Fin i → Bool, ∑ b : Bool, A f b)
      = ∑ f' : Fin (i + 1) → Bool,
          A ((allCellPrefixSuccEquiv i).symm f').1 ((allCellPrefixSuccEquiv i).symm f').2 := by
  rw [Equiv.sum_comp ((allCellPrefixSuccEquiv i).symm) (fun y => A y.1 y.2)]
  rw [Fintype.sum_prod_type]

/-- Replace the bit at wire `i` by `b`. -/
def setBitI {n : ℕ} (i : Fin n) (x : Reg n) (b : Bool) : Reg n :=
  fun j => if j = i then b else x j

/-- Flip the bit at wire `i`. -/
def flipI {n : ℕ} (i : Fin n) (x : Reg n) : Reg n := setBitI i x (!x i)

/-- Two registers agree at every wire other than `i`. -/
abbrev AgreesOutsideI {n : ℕ} (i : Fin n) (x y : Reg n) : Prop :=
  ∀ j : Fin n, j ≠ i → y j = x j

/-- The complex-valued indicator that two registers agree outside wire `i`. -/
def agreesOutsideI {n : ℕ} (i : Fin n) (x y : Reg n) : ℂ :=
  if AgreesOutsideI i x y then 1 else 0

/-- Embed a single-qubit matrix on wire `i`, acting as the identity on the other wires. -/
def embedRegI {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  fun y z => if AgreesOutsideI i y z then U (y i) (z i) else 0

/-- A state has amplitudes `c` on wire `i` and is fixed to the register `x` on every other wire. -/
abbrev WireState {n : ℕ} (i : Fin n) (x : Reg n) (c : Bool → ℂ) (ψ : Reg n → ℂ) : Prop :=
  ∀ y : Reg n, ψ y = c (y i) * agreesOutsideI i x y

/-- The total measurement probability of registers whose bit at wire `i` is `true`. -/
noncomputable def AcceptProbAt {n : ℕ} (i : Fin n) (ψ : QState (Reg n)) : ℝ :=
  MeasureProb ψ (Finset.univ.filter fun y => y i = true)

/-- The specification that every unitary circuit on a nonempty register has a local quantum
Turing machine simulation satisfying the five conditions and matching acceptance probability
within the stated polynomial time bound. -/
def HeadStayLightconeSpec : Prop :=
  ∀ (n : ℕ) (C : Circuit (Reg n)) (hn : 0 < n), IsUnitaryCircuit C →
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (qacc : Q) (M : LocalQTM Q Bool)
      (w t : ℕ),
      0 < w ∧ 0 < t ∧ n ≤ w ∧ n ≤ t ∧ t ≤ (n + Size C + 2) ^ 6 ∧
      LocalQTMFiveConditions M ∧
      ∀ x : Reg n,
        (∑ c ∈ Finset.univ.filter (fun c => c.state = qacc),
          BornProb ((windowStep (t := w) M) ^ t *ᵥ
            Ket (initWindowCfg (t := w) M n x)) c) =
        AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) C (Ket x)) hn

/-- The ordered list of the `k` single-qubit matrices assigned to cell `i`. -/
def cellGates {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (i : Fin n) :
    List (Matrix Bool Bool ℂ) :=
  List.ofFn (fun j : Fin k => V i j)

/-- A state's amplitudes factor as the product of the specified single-wire amplitudes. -/
def TensorState {n : ℕ} (amps : Fin n → Bool → ℂ) (ψ : QState (Reg n)) : Prop :=
  ∀ y : Reg n, ψ y = ∏ j : Fin n, amps j (y j)

/-- Replace the single-wire amplitude function at wire `i` by `v`. -/
def ampsUpd {n : ℕ} (i : Fin n) (v : Bool → ℂ) (amps : Fin n → Bool → ℂ) :
    Fin n → Bool → ℂ :=
  fun j => if j = i then v else amps j

/-- The single-wire amplitudes obtained by applying each cell's complete gate list to its input
bit. -/
noncomputable def tourAmps {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n) :
    Fin n → Bool → ℂ :=
  fun j => boolGateProd (cellGates V j) *ᵥ (fun c => if c = x j then (1 : ℂ) else 0)

/-- The amplitudes after completing the cell gates on `S` and leaving all other cells in their
input basis states. -/
noncomputable def partialAmps {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (S : Finset (Fin n)) : Fin n → Bool → ℂ :=
  fun j => if j ∈ S then tourAmps V x j else (fun c => if c = x j then (1 : ℂ) else 0)

/-- The circuit applying cell `i`'s gate list to wire `i` of the full register. -/
def cellGateList {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (i : Fin n) :
    Circuit (Reg n) :=
  (cellGates V i).map (fun U => Step.gate (embedRegI i U))

/-- The circuit obtained by concatenating the cell circuits in increasing wire order. -/
def compositeCellCircuit {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) :
    Circuit (Reg n) :=
  (List.finRange n).flatMap (cellGateList V)

/-- Encode a fixed-gate operation as a Boolean list using gate tags and binary wire indices. -/
def dLambdaOpEnc {n : ℕ} : DLambdaOp n → List Bool
  | .hGate i => false :: false :: i.val.bits
  | .tGate i => false :: true :: i.val.bits
  | .tGateAdj i => false :: true :: false :: i.val.bits
  | .cnot i j => true :: (i.val.bits ++ [false] ++ j.val.bits)

/-- Encode a list of fixed-gate operations by concatenating their individual encodings. -/
def dLambdaOpsEnc {n : ℕ} (ops : List (DLambdaOp n)) : List Bool :=
  ops.flatMap dLambdaOpEnc

/-- Prefix the operation-list encoding by its unary length and a false delimiter. -/
def dLambdaOpsEnc' {n : ℕ} (ops : List (DLambdaOp n)) : List Bool :=
  (List.replicate ops.length true ++ [false]) ++ dLambdaOpsEnc ops

/-- The existence of one polynomial-time bit-tape machine that emits the size of each encoded
fixed-gate circuit. -/
def DLambdaBitTMUniformity : Prop :=
  ∃ (q c d : ℕ) (emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
    ∀ (n : ℕ) (ops : List (DLambdaOp n)),
      TM0EmitsPoly emitter c d (n.bits ++ [false] ++ dLambdaOpsEnc' ops)
        ((Size (dLambdaCircuit ops)).bits ++ [false])

/-- The finite set of all-cell window configurations whose control state is `acc`. -/
def tourAcceptSet {n k w : ℕ} : Finset (WindowCfg w (AllCellState n k) Bool) :=
  Finset.univ.filter fun c => c.state = (.acc : AllCellState n k)

/-- The odd repetition count `2 * ceil(log(1 / ε) / log(9 / 8)) + 1` used for amplification. -/
noncomputable def amplificationCopies (ε : ℝ) : ℕ :=
  2 * Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) + 1

end QtmUniform
end Qatlib.Concepts.CircuitImpl.Phi3Universal
