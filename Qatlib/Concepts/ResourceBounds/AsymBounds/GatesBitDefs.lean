/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.ResourceBounds.AsymBounds.EffectiveAccessDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open Matrix
open Qatlib.Concepts.ClassicalTape.TapeCompilation (BitMachineAfter)
open Qatlib.Concepts.ResourceBounds.AsymBounds (selfDelimitBits)

def parseSdnat : List Bool → ℕ
  | [] => 0
  | true :: rest => parseSdnat rest + 1
  | false :: rest => rest.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

def parseSdnat2 : List Bool → ℕ × ℕ :=
  fun input =>
    let k := (input.takeWhile (fun b => b = true)).length
    let first := (input.drop (k + 1)).take k |>.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0
    (first, parseSdnat (input.drop (2 * k + 1)))

def bitLengthTask (input : List Bool) : List Bool :=
  selfDelimitBits (parseSdnat input).bits.length

def gcdTask (input : List Bool) : List Bool :=
  selfDelimitBits ((parseSdnat2 input).1.gcd (parseSdnat2 input).2)

def addTask (input : List Bool) : List Bool :=
  selfDelimitBits ((parseSdnat2 input).1 + (parseSdnat2 input).2)

def mulTask (input : List Bool) : List Bool :=
  selfDelimitBits ((parseSdnat2 input).1 * (parseSdnat2 input).2)

inductive DynOp where

  | alloc (w : ℕ)

  | releaseClean (w : ℕ)

  | releaseDirty (w : ℕ)

  | resetWire (w : ℕ)

  | uncomputeWire (w : ℕ)

  | fixedGate (g : FiniteGateCode)

  | oracleQuery (ws : List ℕ)

def dynOpBitCost : DynOp → ℕ
  | .alloc _ => 1
  | .releaseClean _ => 2
  | .releaseDirty _ => 4
  | .resetWire _ => 3
  | .uncomputeWire _ => 3
  | .fixedGate _ => 1
  | .oracleQuery ws => 1 + ws.length

def opsGates : List DynOp → List FiniteGateCode
  | [] => []
  | .fixedGate g :: rest => g :: opsGates rest
  | _ :: rest => opsGates rest

def DynOp.isOracleQuery : DynOp → Bool
  | .oracleQuery _ => true
  | _ => false

def DynOp.isReleaseDirty : DynOp → Bool
  | .releaseDirty _ => true
  | _ => false

def opAt : List DynOp → ℕ → Option DynOp
  | [], _ => none
  | op :: _, 0 => some op
  | _ :: rest, k + 1 => opAt rest k

structure DynAccount where

  gateCount : ℕ

  queryCount : ℕ

  bitCost : ℕ

  allocCount : ℕ

  releaseCount : ℕ

  dirtyDiscardCount : ℕ

  maxLive : ℕ

  peakWorkspace : ℕ

def dynInitial (base : ℕ) : DynAccount × List ℕ :=
  (⟨0, 0, 0, 0, 0, 0, base, 0⟩, List.range base)

def dynStep (base : ℕ) (st : DynAccount × List ℕ) (op : DynOp) : DynAccount × List ℕ :=
  let a := st.1
  let live := st.2
  match op with
  | .alloc w =>
    let live' := w :: live
    (⟨a.gateCount, a.queryCount, a.bitCost + dynOpBitCost op, a.allocCount + 1,
        a.releaseCount, a.dirtyDiscardCount, max a.maxLive live'.length,
        max a.peakWorkspace (live'.length - base)⟩, live')
  | .releaseClean w =>
    (⟨a.gateCount, a.queryCount, a.bitCost + dynOpBitCost op, a.allocCount,
        a.releaseCount + 1, a.dirtyDiscardCount, a.maxLive, a.peakWorkspace⟩, live.erase w)
  | .releaseDirty w =>
    (⟨a.gateCount, a.queryCount, a.bitCost + dynOpBitCost op, a.allocCount,
        a.releaseCount + 1, a.dirtyDiscardCount + 1, a.maxLive, a.peakWorkspace⟩,
      live.erase w)
  | .resetWire _ =>
    (⟨a.gateCount, a.queryCount, a.bitCost + dynOpBitCost op, a.allocCount,
        a.releaseCount, a.dirtyDiscardCount, a.maxLive, a.peakWorkspace⟩, live)
  | .uncomputeWire _ =>
    (⟨a.gateCount, a.queryCount, a.bitCost + dynOpBitCost op, a.allocCount,
        a.releaseCount, a.dirtyDiscardCount, a.maxLive, a.peakWorkspace⟩, live)
  | .fixedGate _ =>
    (⟨a.gateCount + 1, a.queryCount, a.bitCost + dynOpBitCost op, a.allocCount,
        a.releaseCount, a.dirtyDiscardCount, a.maxLive, a.peakWorkspace⟩, live)
  | .oracleQuery _ =>
    (⟨a.gateCount, a.queryCount + 1, a.bitCost + dynOpBitCost op, a.allocCount,
        a.releaseCount, a.dirtyDiscardCount, a.maxLive, a.peakWorkspace⟩, live)

def dynAccount (base : ℕ) (ops : List DynOp) : DynAccount :=
  (ops.foldl (dynStep base) (dynInitial base)).1

def dynFinalLive (base : ℕ) (ops : List DynOp) : List ℕ :=
  (ops.foldl (dynStep base) (dynInitial base)).2

def dynLegalOps (base : ℕ) : List DynOp → List ℕ → Bool
  | [], _ => true
  | .alloc w :: rest, live =>
      decide (base ≤ w) && !(live.contains w) && dynLegalOps base rest (w :: live)
  | .releaseClean w :: rest, live =>
      decide (base ≤ w && live.contains w) && dynLegalOps base rest (live.erase w)
  | .releaseDirty w :: rest, live =>
      decide (base ≤ w && live.contains w) && dynLegalOps base rest (live.erase w)
  | .resetWire w :: rest, live =>
      decide (base ≤ w && live.contains w) && dynLegalOps base rest live
  | .uncomputeWire w :: rest, live =>
      decide (base ≤ w && live.contains w) && dynLegalOps base rest live
  | .fixedGate _ :: rest, live => dynLegalOps base rest live
  | .oracleQuery ws :: rest, live =>
      decide (ws.all (fun w => base ≤ w && live.contains w)) && dynLegalOps base rest live

def dynLegal (base : ℕ) (ops : List DynOp) : Bool :=
  dynLegalOps base ops (List.range base)

def maskDead {N : ℕ} (x : Reg N) (live : Fin N → Bool) : Reg N :=
  fun i => if live i = true then x i else false

def acceptanceMassMasked {N : ℕ} (ψ : QState (Reg N)) (accept : Reg N → Bool)
    (live : Fin N → Bool) : ℝ :=
  ∑ x : Reg N, if accept (maskDead x live) = true then ‖ψ x‖ ^ 2 else 0

def phaseFactor (φ : ℝ) : ℂ := Complex.exp (φ * Complex.I)

end Qatlib.Concepts.ResourceBounds.AsymBounds

end
