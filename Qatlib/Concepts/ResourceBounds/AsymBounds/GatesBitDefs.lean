/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.ResourceBounds.AsymBounds.EffectiveAccessDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Bit tasks and dynamic resource accounting

This module defines bit-string tasks for integer parsing, bit length, greatest common divisor,
addition, and multiplication. It also introduces `DynOp` and an accounting interpreter that
tracks gate and query counts, bit charges, allocation and release counts, and peak live-wire
usage. Circuit and bit-computation models are treated in [KitaevShenVyalyi2002].

`dynLegalOps` checks allocation freshness and live-workspace requirements. The module
additionally defines masking of inactive wires and the resulting acceptance mass, together with
a complex phase factor.

## Main statements

* `dynStep`: updates the resource account and live-wire list.
* `dynAccount`: accumulates resources for a dynamic operation list.
* `dynLegal`: checks operations from the initial wire set.
* `acceptanceMassMasked`: acceptance mass after masking inactive wires.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

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

/-- Recursively counts leading true bits and, after a false separator, adds the binary-fold
value of the remaining bits. -/
def parseSdnat : List Bool → ℕ
  | [] => 0
  | true :: rest => parseSdnat rest + 1
  | false :: rest => rest.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

/-- Extracts a first binary value using the leading true-run length and parses the remaining
suffix with `parseSdnat`. -/
def parseSdnat2 : List Bool → ℕ × ℕ :=
  fun input =>
    let k := (input.takeWhile (fun b => b = true)).length
    let first := (input.drop (k + 1)).take k |>.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0
    (first, parseSdnat (input.drop (2 * k + 1)))

/-- Returns the self-delimiting encoding of the bit-list length of `parseSdnat input`. -/
def bitLengthTask (input : List Bool) : List Bool :=
  selfDelimitBits (parseSdnat input).bits.length

/-- Returns the self-delimiting encoding of the greatest common divisor of the two parsed
values. -/
def gcdTask (input : List Bool) : List Bool :=
  selfDelimitBits ((parseSdnat2 input).1.gcd (parseSdnat2 input).2)

/-- Returns the self-delimiting encoding of the sum of the two parsed values. -/
def addTask (input : List Bool) : List Bool :=
  selfDelimitBits ((parseSdnat2 input).1 + (parseSdnat2 input).2)

/-- Returns the self-delimiting encoding of the product of the two parsed values. -/
def mulTask (input : List Bool) : List Bool :=
  selfDelimitBits ((parseSdnat2 input).1 * (parseSdnat2 input).2)

/-- Dynamic operations for wire allocation, clean or dirty release, reset, uncomputation, fixed
gates, and oracle queries. -/
inductive DynOp where

  | alloc (w : ℕ)

  | releaseClean (w : ℕ)

  | releaseDirty (w : ℕ)

  | resetWire (w : ℕ)

  | uncomputeWire (w : ℕ)

  | fixedGate (g : FiniteGateCode)

  | oracleQuery (ws : List ℕ)

/-- Assigns a bit charge to each dynamic operation, with an oracle-query charge of one plus its
wire-list length. -/
def dynOpBitCost : DynOp → ℕ
  | .alloc _ => 1
  | .releaseClean _ => 2
  | .releaseDirty _ => 4
  | .resetWire _ => 3
  | .uncomputeWire _ => 3
  | .fixedGate _ => 1
  | .oracleQuery ws => 1 + ws.length

/-- Extracts the fixed-gate codes from a dynamic operation list in their original order. -/
def opsGates : List DynOp → List FiniteGateCode
  | [] => []
  | .fixedGate g :: rest => g :: opsGates rest
  | _ :: rest => opsGates rest

/-- Tests whether a dynamic operation is an oracle query. -/
def DynOp.isOracleQuery : DynOp → Bool
  | .oracleQuery _ => true
  | _ => false

/-- Tests whether a dynamic operation is a dirty wire release. -/
def DynOp.isReleaseDirty : DynOp → Bool
  | .releaseDirty _ => true
  | _ => false

/-- Returns the dynamic operation at a zero-based index, or `none` when the index is out of
range. -/
def opAt : List DynOp → ℕ → Option DynOp
  | [], _ => none
  | op :: _, 0 => some op
  | _ :: rest, k + 1 => opAt rest k

/-- Resource counters for gates, queries, bit charges, allocations, releases, dirty discards,
and peak live and workspace sizes. -/
structure DynAccount where

  gateCount : ℕ

  queryCount : ℕ

  bitCost : ℕ

  allocCount : ℕ

  releaseCount : ℕ

  dirtyDiscardCount : ℕ

  maxLive : ℕ

  peakWorkspace : ℕ

/-- Initializes a dynamic account with `base` live wires and zero work counters and workspace
peak. -/
def dynInitial (base : ℕ) : DynAccount × List ℕ :=
  (⟨0, 0, 0, 0, 0, 0, base, 0⟩, List.range base)

/-- Updates the account and live-wire list for one operation, charging its bit cost and updating
peak usage on allocation. -/
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

/-- Returns the resource account obtained by folding the dynamic interpreter over the operation
list. -/
def dynAccount (base : ℕ) (ops : List DynOp) : DynAccount :=
  (ops.foldl (dynStep base) (dynInitial base)).1

/-- Returns the final live-wire list obtained by the dynamic accounting interpreter. -/
def dynFinalLive (base : ℕ) (ops : List DynOp) : List ℕ :=
  (ops.foldl (dynStep base) (dynInitial base)).2

/-- Checks freshness of allocations and membership of referenced workspace wires while updating
the live-wire list through releases. -/
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

/-- Checks dynamic-operation legality starting with the base wires `List.range base`. -/
def dynLegal (base : ℕ) (ops : List DynOp) : Bool :=
  dynLegalOps base ops (List.range base)

/-- Replaces every inactive wire of a bit register by false. -/
def maskDead {N : ℕ} (x : Reg N) (live : Fin N → Bool) : Reg N :=
  fun i => if live i = true then x i else false

/-- Sums squared amplitudes over basis states whose masked registers satisfy the acceptance
predicate. -/
def acceptanceMassMasked {N : ℕ} (ψ : QState (Reg N)) (accept : Reg N → Bool)
    (live : Fin N → Bool) : ℝ :=
  ∑ x : Reg N, if accept (maskDead x live) = true then ‖ψ x‖ ^ 2 else 0

/-- The complex phase `exp (iφ)` associated with a real angle. -/
def phaseFactor (φ : ℝ) : ℂ := Complex.exp (φ * Complex.I)

end Qatlib.Concepts.ResourceBounds.AsymBounds

end
