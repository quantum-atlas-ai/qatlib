/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExt
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Call

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.EmitterCore
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ValidatorSemantics
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Turing

def bitNat (b : Bool) : ℕ := if b then 1 else 0

def carryStep (c xb yb : Bool) : Bool × Bool :=
  let s := (if xb then 1 else 0) + (if yb then 1 else 0) + (if c then 1 else 0)
  (s % 2 == 1, 2 ≤ s)

structure AddState where

  carry : Bool

  xs : Bits

  ys : Bits

  os : Bits

def addTurn (s : AddState) : AddState :=
  let xb := s.xs.head?.getD false
  let yb := s.ys.head?.getD false
  let (sb, cb) := carryStep s.carry xb yb
  { carry := cb, xs := s.xs.tail, ys := s.ys.tail, os := sb :: s.os }

def addTurns : Nat → AddState → AddState
  | 0, s => s
  | k+1, s => addTurns k (addTurn s)

def carryAddAux (n : ℕ) (c : Bool) (x y : Bits) : List Bool × Bool :=
  let s := addTurns n ⟨c, x, y, []⟩
  (List.reverse s.os, s.carry)

def carryAdd (c : Bool) (x y : Bits) : Bits :=
  (carryAddAux (max x.length y.length) c x y).1
    ++ (if (carryAddAux (max x.length y.length) c x y).2 then [true] else [])

def bitAdd (x y : Bits) : Bits := carryAdd false x y

def carryAddPositions (x y : Bits) : ℕ := max x.length y.length

def shiftLeft (b : Bits) (i : ℕ) : Bits := List.replicate i false ++ b

def msbValue (b : Bits) : ℕ := binaryValue b.reverse

def bitMulAux (x : Bits) : Bits → Bits → Bits
  | [], acc => acc
  | y :: ys, acc =>
      let acc' := shiftLeft acc 1
      let acc'' := if y then carryAdd false acc' x else acc'
      bitMulAux x ys acc''

def bitMul (x y : Bits) : Bits := bitMulAux x y.reverse []

def bitSize (b : Bits) : ℕ := b.length

structure RatEnc where

  num : ℤ

  den : ℕ

  den_pos : 0 < den

def RatEnc.toRat (e : RatEnc) : ℚ := e.num / e.den

def RatEnc.toReal (e : RatEnc) : ℝ := (e.toRat : ℝ)

def RatEnc.size (e : RatEnc) : ℕ := e.num.natAbs.size + e.den.size + 2

def RatEnc.ofNat (n : ℕ) : RatEnc := ⟨(n : ℤ), 1, by norm_num⟩

def RatEnc.fixed (m : ℕ) (e : ℕ) : RatEnc :=
  ⟨(m : ℤ), 2 ^ e, by positivity⟩

structure NativeName where

  eval : ℕ → RatEnc

  value : ℝ

  errAt : ℕ → ℚ

  descBits : ℕ

  sizeSpec : ∀ p : ℕ, (eval p).size ≤ descBits + 2 * p + 4

  errSpec : ∀ p : ℕ, |(eval p).toReal - value| ≤ (errAt p : ℝ)

  errBudget : ∀ p : ℕ, 0 ≤ errAt p ∧ errAt p * 2 ^ p ≤ 1

def NativeName.errReal (N : NativeName) (p : ℕ) : ℝ := (N.errAt p : ℝ)

def NativeName.read (N : NativeName) (p : ℕ) : RatEnc := N.eval p

inductive AddLabel where

  | loop

  | done
  deriving DecidableEq, Fintype

structure AddVar where

  carry : Bool

  xbit : Option Bool

  ybit : Option Bool
  deriving DecidableEq

def AddVar.init : AddVar := ⟨false, none, none⟩

def addStacks (x y out : Bits) : Fin 3 → List Bool :=
  fun i => if i = 0 then x else if i = 1 then y else out

def addProgram (l : AddLabel) : TM2.Stmt (fun _ : Fin 3 => Bool) AddLabel AddVar :=
  match l with
  | .loop =>
      .peek 0 (fun v x => { v with xbit := x }) (
        .peek 1 (fun v y => { v with ybit := y }) (
          .branch (fun v => v.xbit.isSome || v.ybit.isSome)
            (.pop 0 (fun v _ => v) (
              .pop 1 (fun v _ => v) (
                .push 2 (fun v => (carryStep v.carry (v.xbit.getD false) (v.ybit.getD false)).1) (
                  .load (fun v => { v with carry := (carryStep v.carry (v.xbit.getD false) (v.ybit.getD false)).2, xbit := none, ybit := none }) (
                    .goto (fun _ => .loop))))))
            (.branch (fun v => v.carry)
              (.push 2 (fun _ => true) (.halt))
              (.halt))))
  | .done => .halt

def addStart (x y : Bits) : TM2.Cfg (fun _ : Fin 3 => Bool) AddLabel AddVar :=
  ⟨some .loop, AddVar.init, addStacks x y []⟩

def stackHeight {Λ : Type} {σ : Type}
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) Λ σ) : ℕ := ∑ k : Fin 3, (c.stk k).length

def addTicks (x y : Bits) : ℕ := carryAddPositions x y + 1

def addClockBound (x y : Bits) : ℕ :=
  (carryAddPositions x y + 1) * (4 * (x.length + y.length + carryAddPositions x y) + 14)

def addSpaceBound (x y : Bits) : ℕ := 2 * (carryAddPositions x y + 1)

def NativeAddRun (x y : Bits) : Prop :=
  ∃ (cfg : TM2.Cfg (fun _ : Fin 3 => Bool) AddLabel AddVar) (ticks : ℕ),
    stackRun addProgram ticks (addStart x y) = some cfg ∧
    cfg.l = none ∧
    binaryValue (List.reverse (cfg.stk 2)) = binaryValue x + binaryValue y ∧
    ticks ≤ addTicks x y ∧
    stackRunClock addProgram ticks (addStart x y) ≤ addClockBound x y ∧
    (∀ s : ℕ, s ≤ ticks →
      match stackRun addProgram s (addStart x y) with
      | some c => stackHeight c ≤ addSpaceBound x y
      | none => True)

inductive NativeParamKind where

  | phase

  | rotation

  | prepareCoeff

  | spectralGap
  deriving DecidableEq, Fintype

structure NativeParam where

  kind : NativeParamKind

  name : NativeName

  marginBits : ℕ

structure NativeWord where

  slots : List (List NativeParam)

  amp : List ℕ

  phaseBits : ℕ

structure NativeParams where

  paramCount : ℕ

  ampTotal : ℕ

  errUnits : ℕ

  epsBits : ℕ
  deriving DecidableEq

def nativeSlotError : List NativeParam → ℕ → ℚ
  | [], _ => 0
  | p :: ps, k => p.name.errAt k + nativeSlotError ps k

def nativeSlotKindError : List NativeParam → ℕ → NativeParamKind → ℚ
  | [], _, _ => 0
  | p :: ps, k, kd =>
      (if p.kind = kd then p.name.errAt k else 0) + nativeSlotKindError ps k kd

def nativeWordErrorUnitsAux : List (List NativeParam × ℕ) → ℕ
  | [] => 0
  | (s, a) :: rest => a * s.length + nativeWordErrorUnitsAux rest

def nativeWordErrorActualAux : List (List NativeParam × ℕ) → ℕ → ℚ
  | [], _ => 0
  | (s, a) :: rest, k => (a : ℚ) * nativeSlotError s k + nativeWordErrorActualAux rest k

def nativeKindErrorActualAux : List (List NativeParam × ℕ) → ℕ → NativeParamKind → ℚ
  | [], _, _ => 0
  | (s, a) :: rest, k, kd =>
      (a : ℚ) * nativeSlotKindError s k kd + nativeKindErrorActualAux rest k kd

def nativeWordErrorUnits (w : NativeWord) : ℕ :=
  nativeWordErrorUnitsAux (w.slots.zip w.amp)

def nativeWordErrorActual (w : NativeWord) (k : ℕ) : ℚ :=
  nativeWordErrorActualAux (w.slots.zip w.amp) k

def nativeKindErrorActual (w : NativeWord) (k : ℕ) (kd : NativeParamKind) : ℚ :=
  nativeKindErrorActualAux (w.slots.zip w.amp) k kd

def nativeMarginBits (w : NativeWord) : ℕ :=
  w.slots.foldl (fun acc s => max acc (s.foldl (fun a p => max a p.marginBits) 0)) 0

def nativeGapError (w : NativeWord) (k : ℕ) : ℚ :=
  nativeKindErrorActual w k .spectralGap

def NativeWord.publicParams (w : NativeWord) : NativeParams :=
  { paramCount := w.slots.foldl (fun acc s => acc + s.length) 0
    ampTotal := w.amp.foldl (fun acc a => acc + a) 0
    errUnits := nativeWordErrorUnits w
    epsBits := w.phaseBits }

def precisionChoice (p : NativeParams) : ℕ := p.errUnits + p.epsBits + 2

def nativeWordError (w : NativeWord) (k : ℕ) : ℚ :=
  (nativeWordErrorUnits w) / ((2 : ℚ) ^ k)

def nativeParamError (p : NativeParam) (k : ℕ) : ℚ := p.name.errAt k

def nativeReadCost (w : NativeWord) (k : ℕ) : ℕ :=
  w.slots.foldl
    (fun acc s => acc + s.foldl (fun a p => a + p.name.descBits + 2 * k + 4) 0) 0

def OffGrid (lam : ℚ) (t : ℕ) : Prop := ∀ i : ℕ, i < 2 ^ t → lam ≠ i / 2 ^ t

def NativeSamplerLaw (m : ℕ) (p : (Fin m → Bool) → ℝ) : Prop :=
  (∀ w : Fin m → Bool, p w = 1 / (2 : ℝ) ^ m) ∧
  (0 ≤ 1 / (2 : ℝ) ^ m) ∧
  (∑ w : Fin m → Bool, p w = 1)

def LegalSlot (addrWidth slot : ℕ) : Prop := slot < 2 ^ addrWidth

def natToBitsAux : ℕ → Bits
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: natToBitsAux ((n + 1) / 2)

def natToBits (n : ℕ) : Bits := natToBitsAux n

def bitGcd (x y : Bits) : Bits := natToBits (Nat.gcd (binaryValue x) (binaryValue y))

def bitModMul (x y m : Bits) : Bits :=
  natToBits ((binaryValue x * binaryValue y) % binaryValue m)

def bitModPow (x e m : Bits) : Bits :=
  natToBits ((binaryValue x) ^ (binaryValue e) % binaryValue m)

end Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)

def runSteps {w L : ℕ} (c : AccessContract L) : List (ProbInstr w L) → ProbState w → ProbState w
  | [], s => s
  | i :: is, s => runSteps c is (probStep c s i)

def nativeForwardContract (L : ℕ) (g : Fin L → ℕ → ℕ) : AccessContract L where
  supplied := fun _ f => decide (f = .forward)
  impl := fun s f => if f = .forward then some (g s) else none

def nativeModPowProgram : ProbProgram 5 3 where
  steps :=
    [ ProbInstr.oracle (0 : Fin 3) .forward (0 : Fin 5) (1 : Fin 5),
      ProbInstr.oracle (1 : Fin 3) .forward (0 : Fin 5) (2 : Fin 5),
      ProbInstr.oracle (2 : Fin 3) .forward (0 : Fin 5) (3 : Fin 5),
      ProbInstr.arith .modexp [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)],
      ProbInstr.emit (4 : Fin 5) ]

def nativeModPowContract (a e m : ℕ) : AccessContract 3 where
  supplied := fun _ f => decide (f = .forward)
  impl := fun s f =>
    if f = .forward then
      some (fun _ => match s.val with
        | 0 => a
        | 1 => e
        | _ => m)
    else none

def nativeGcdProgram : ProbProgram 4 2 where
  steps :=
    [ ProbInstr.oracle (0 : Fin 2) .forward (0 : Fin 4) (1 : Fin 4),
      ProbInstr.oracle (1 : Fin 2) .forward (0 : Fin 4) (2 : Fin 4),
      ProbInstr.arith .gcd [(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)],
      ProbInstr.emit (3 : Fin 4) ]

def nativeGcdContract (x y : ℕ) : AccessContract 2 where
  supplied := fun _ f => decide (f = .forward)
  impl := fun s f =>
    if f = .forward then
      some (fun _ => match s.val with
        | 0 => x
        | _ => y)
    else none

def nativeSamplerSteps : (m : ℕ) → List (ProbInstr 1 1)
  | 0 => []
  | m + 1 => ProbInstr.fairCoin (0 : Fin 1) :: ProbInstr.emit (0 : Fin 1) :: nativeSamplerSteps m

def nativeSamplerProgram (m : ℕ) : ProbProgram 1 1 where
  steps := nativeSamplerSteps m

def nativeSamplerOut (m : ℕ) (r : Fin m → Bool) : List ℕ :=
  List.ofFn (fun i : Fin m => if r i then 1 else 0)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs (NumericalKind)

def nativeParamKind : NativeParamKind → NumericalKind
  | .phase => .phase
  | .rotation => .rotation
  | .prepareCoeff => .prepareCoeff
  | .spectralGap => .spectralGap

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
