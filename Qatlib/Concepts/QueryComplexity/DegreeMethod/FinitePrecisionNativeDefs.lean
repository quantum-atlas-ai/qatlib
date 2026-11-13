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

/-!
# Native arithmetic and precision data

This module defines binary addition and multiplication, rational encodings `RatEnc`, and
approximation names `NativeName` with explicit size and error specifications. The three-stack
addition program `addProgram` is paired with the bounded-run specification `NativeAddRun`.

The structures `NativeWord` and `NativeParams` expose parameter kinds, amplification weights,
precision choices, and reading costs. Forward-access arithmetic programs and a Boolean sampling
program supply concrete finite computations in the framework of [KitaevShenVyalyi2002].

## Main statements

* `carryAdd` and `bitMul`: arithmetic on little-endian bit lists.
* `NativeName`: rational approximations with certified size and error bounds.
* `nativeWordErrorActual` and `precisionChoice`: weighted error accounting and the public
  precision rule.
* `nativeModPowProgram`, `nativeGcdProgram`, and `nativeSamplerProgram`: arithmetic and sampling
  programs.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

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

/-- The natural number associated with a Boolean bit, equal to one for true and zero for false. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- The sum bit and outgoing carry obtained by adding two Boolean bits and an incoming carry. -/
def carryStep (c xb yb : Bool) : Bool × Bool :=
  let s := (if xb then 1 else 0) + (if yb then 1 else 0) + (if c then 1 else 0)
  (s % 2 == 1, 2 ≤ s)

/-- The state of binary addition, consisting of a carry, two remaining input lists, and an
output accumulator. -/
structure AddState where

  carry : Bool

  xs : Bits

  ys : Bits

  os : Bits

/-- One binary addition turn that consumes the input heads, treating absent bits as false, and
prepends the resulting sum bit to the output accumulator. -/
def addTurn (s : AddState) : AddState :=
  let xb := s.xs.head?.getD false
  let yb := s.ys.head?.getD false
  let (sb, cb) := carryStep s.carry xb yb
  { carry := cb, xs := s.xs.tail, ys := s.ys.tail, os := sb :: s.os }

/-- Iterates `addTurn` for a specified number of turns. -/
def addTurns : Nat → AddState → AddState
  | 0, s => s
  | k+1, s => addTurns k (addTurn s)

/-- Runs a fixed number of addition turns and returns the reversed output accumulator together
with the outgoing carry. -/
def carryAddAux (n : ℕ) (c : Bool) (x y : Bits) : List Bool × Bool :=
  let s := addTurns n ⟨c, x, y, []⟩
  (List.reverse s.os, s.carry)

/-- Adds two bit lists and an incoming carry, retaining a final true carry as an additional most
significant bit. -/
def carryAdd (c : Bool) (x y : Bits) : Bits :=
  (carryAddAux (max x.length y.length) c x y).1
    ++ (if (carryAddAux (max x.length y.length) c x y).2 then [true] else [])

/-- Binary addition of two bit lists with initial carry false. -/
def bitAdd (x y : Bits) : Bits := carryAdd false x y

/-- The number of input positions processed by carry addition, equal to the maximum of the input
lengths. -/
def carryAddPositions (x y : Bits) : ℕ := max x.length y.length

/-- Shifts a little-endian bit list left by prefixing a specified number of false bits. -/
def shiftLeft (b : Bits) (i : ℕ) : Bits := List.replicate i false ++ b

/-- The natural value of a bit list read with its most significant bit first. -/
def msbValue (b : Bits) : ℕ := binaryValue b.reverse

/-- Processes multiplier bits from most significant to least significant by doubling the
accumulator and conditionally adding the multiplicand. -/
def bitMulAux (x : Bits) : Bits → Bits → Bits
  | [], acc => acc
  | y :: ys, acc =>
      let acc' := shiftLeft acc 1
      let acc'' := if y then carryAdd false acc' x else acc'
      bitMulAux x ys acc''

/-- Binary multiplication of two little-endian bit lists using `bitMulAux` on the reversed
multiplier. -/
def bitMul (x y : Bits) : Bits := bitMulAux x y.reverse []

/-- The number of bits in a bit list. -/
def bitSize (b : Bits) : ℕ := b.length

/-- A rational encoding consisting of an integer numerator and a strictly positive natural
denominator. -/
structure RatEnc where

  num : ℤ

  den : ℕ

  den_pos : 0 < den

/-- The rational value obtained by dividing the encoded numerator by the denominator. -/
def RatEnc.toRat (e : RatEnc) : ℚ := e.num / e.den

/-- The real value obtained by coercing the decoded rational encoding. -/
def RatEnc.toReal (e : RatEnc) : ℝ := (e.toRat : ℝ)

/-- The sum of the binary sizes of the numerator's absolute value and the denominator, with two
additional bits. -/
def RatEnc.size (e : RatEnc) : ℕ := e.num.natAbs.size + e.den.size + 2

/-- Encodes a natural number as an integer numerator with denominator one. -/
def RatEnc.ofNat (n : ℕ) : RatEnc := ⟨(n : ℤ), 1, by norm_num⟩

/-- Encodes the dyadic rational `m / 2 ^ e` with numerator `m` and denominator `2 ^ e`. -/
def RatEnc.fixed (m : ℕ) (e : ℕ) : RatEnc :=
  ⟨(m : ℤ), 2 ^ e, by positivity⟩

/-- A real value represented by rational approximations indexed by precision, with an
encoding-size bound and nonnegative error bounds at most the corresponding dyadic unit. -/
structure NativeName where

  eval : ℕ → RatEnc

  value : ℝ

  errAt : ℕ → ℚ

  descBits : ℕ

  sizeSpec : ∀ p : ℕ, (eval p).size ≤ descBits + 2 * p + 4

  errSpec : ∀ p : ℕ, |(eval p).toReal - value| ≤ (errAt p : ℝ)

  errBudget : ∀ p : ℕ, 0 ≤ errAt p ∧ errAt p * 2 ^ p ≤ 1

/-- The real coercion of a native name's rational error bound at the requested precision. -/
def NativeName.errReal (N : NativeName) (p : ℕ) : ℝ := (N.errAt p : ℝ)

/-- The rational encoding returned by a native name at the requested precision. -/
def NativeName.read (N : NativeName) (p : ℕ) : RatEnc := N.eval p

/-- The loop and done control labels for the native binary addition machine. -/
inductive AddLabel where

  | loop

  | done
  deriving DecidableEq, Fintype

/-- The finite local state of the addition machine, containing a carry and optional bits read
from each input stack. -/
structure AddVar where

  carry : Bool

  xbit : Option Bool

  ybit : Option Bool
  deriving DecidableEq

/-- The initial local addition state with false carry and no stored input bits. -/
def AddVar.init : AddVar := ⟨false, none, none⟩

/-- The three-stack assignment placing the two input bit lists at indices zero and one and the
output accumulator at index two. -/
def addStacks (x y out : Bits) : Fin 3 → List Bool :=
  fun i => if i = 0 then x else if i = 1 then y else out

/-- The three-stack binary addition program that reads and consumes input heads, pushes sum
bits, and halts after writing any final carry. -/
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

/-- The initial addition-machine configuration with both input bit lists, empty output, and the
initial local state. -/
def addStart (x y : Bits) : TM2.Cfg (fun _ : Fin 3 => Bool) AddLabel AddVar :=
  ⟨some .loop, AddVar.init, addStacks x y []⟩

/-- The sum of the lengths of the three stacks in a machine configuration. -/
def stackHeight {Λ : Type} {σ : Type}
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) Λ σ) : ℕ := ∑ k : Fin 3, (c.stk k).length

/-- The addition turn allowance, equal to the maximum input length plus one. -/
def addTicks (x y : Bits) : ℕ := carryAddPositions x y + 1

/-- The addition clock allowance, equal to the turn allowance times `4 * (x.length + y.length +
carryAddPositions x y) + 14`. -/
def addClockBound (x y : Bits) : ℕ :=
  (carryAddPositions x y + 1) * (4 * (x.length + y.length + carryAddPositions x y) + 14)

/-- The addition stack-space allowance, equal to twice the maximum input length plus two. -/
def addSpaceBound (x y : Bits) : ℕ := 2 * (carryAddPositions x y + 1)

/-- The existence of a halted native addition run whose reversed output represents the input sum
and whose turns, clock cost, and intermediate stack heights satisfy the specified bounds. -/
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

/-- The four kinds of native numerical parameters: phase, rotation, preparation coefficient, and
spectral gap. -/
inductive NativeParamKind where

  | phase

  | rotation

  | prepareCoeff

  | spectralGap
  deriving DecidableEq, Fintype

/-- A native numerical parameter with its kind, approximation name, and required margin bit
count. -/
structure NativeParam where

  kind : NativeParamKind

  name : NativeName

  marginBits : ℕ

/-- A list of parameter slots with a list of amplification weights and a target error bit count. -/
structure NativeWord where

  slots : List (List NativeParam)

  amp : List ℕ

  phaseBits : ℕ

/-- The public aggregate data for a native word: parameter count, total amplification, error
units, and target error bits. -/
structure NativeParams where

  paramCount : ℕ

  ampTotal : ℕ

  errUnits : ℕ

  epsBits : ℕ
  deriving DecidableEq

/-- The sum of the named error bounds of all parameters in a slot at the requested precision. -/
def nativeSlotError : List NativeParam → ℕ → ℚ
  | [], _ => 0
  | p :: ps, k => p.name.errAt k + nativeSlotError ps k

/-- The sum of the named error bounds in a slot restricted to parameters of a specified kind. -/
def nativeSlotKindError : List NativeParam → ℕ → NativeParamKind → ℚ
  | [], _, _ => 0
  | p :: ps, k, kd =>
      (if p.kind = kd then p.name.errAt k else 0) + nativeSlotKindError ps k kd

/-- The sum of each slot's parameter count multiplied by its paired amplification weight. -/
def nativeWordErrorUnitsAux : List (List NativeParam × ℕ) → ℕ
  | [] => 0
  | (s, a) :: rest => a * s.length + nativeWordErrorUnitsAux rest

/-- The sum of slot error bounds multiplied by their paired amplification weights at the
requested precision. -/
def nativeWordErrorActualAux : List (List NativeParam × ℕ) → ℕ → ℚ
  | [], _ => 0
  | (s, a) :: rest, k => (a : ℚ) * nativeSlotError s k + nativeWordErrorActualAux rest k

/-- The amplification-weighted sum of slot errors restricted to a specified parameter kind. -/
def nativeKindErrorActualAux : List (List NativeParam × ℕ) → ℕ → NativeParamKind → ℚ
  | [], _, _ => 0
  | (s, a) :: rest, k, kd =>
      (a : ℚ) * nativeSlotKindError s k kd + nativeKindErrorActualAux rest k kd

/-- The error-unit count obtained by pairing the word's slots with its amplification weights. -/
def nativeWordErrorUnits (w : NativeWord) : ℕ :=
  nativeWordErrorUnitsAux (w.slots.zip w.amp)

/-- The weighted error bound computed from the paired slots and amplification weights of a
native word at the requested precision. -/
def nativeWordErrorActual (w : NativeWord) (k : ℕ) : ℚ :=
  nativeWordErrorActualAux (w.slots.zip w.amp) k

/-- The weighted error bound of a native word restricted to one parameter kind at the requested
precision. -/
def nativeKindErrorActual (w : NativeWord) (k : ℕ) (kd : NativeParamKind) : ℚ :=
  nativeKindErrorActualAux (w.slots.zip w.amp) k kd

/-- The maximum margin bit count among all parameters in the word, with default zero. -/
def nativeMarginBits (w : NativeWord) : ℕ :=
  w.slots.foldl (fun acc s => max acc (s.foldl (fun a p => max a p.marginBits) 0)) 0

/-- The weighted spectral-gap error contribution of a native word at the requested precision. -/
def nativeGapError (w : NativeWord) (k : ℕ) : ℚ :=
  nativeKindErrorActual w k .spectralGap

/-- The public parameter count, total amplification, error-unit count, and target error bits
extracted from a native word. -/
def NativeWord.publicParams (w : NativeWord) : NativeParams :=
  { paramCount := w.slots.foldl (fun acc s => acc + s.length) 0
    ampTotal := w.amp.foldl (fun acc a => acc + a) 0
    errUnits := nativeWordErrorUnits w
    epsBits := w.phaseBits }

/-- The precision selected from public parameters, equal to the error-unit count plus the target
error bits plus two. -/
def precisionChoice (p : NativeParams) : ℕ := p.errUnits + p.epsBits + 2

/-- The uniform word error estimate obtained by dividing the error-unit count by `2 ^ k`. -/
def nativeWordError (w : NativeWord) (k : ℕ) : ℚ :=
  (nativeWordErrorUnits w) / ((2 : ℚ) ^ k)

/-- The error bound supplied by a native parameter's name at precision `k`. -/
def nativeParamError (p : NativeParam) (k : ℕ) : ℚ := p.name.errAt k

/-- The sum of the parameter encoding-size allowances `descBits + 2 * k + 4` over all slots of a
native word. -/
def nativeReadCost (w : NativeWord) (k : ℕ) : ℕ :=
  w.slots.foldl
    (fun acc s => acc + s.foldl (fun a p => a + p.name.descBits + 2 * k + 4) 0) 0

/-- The condition that a rational value differs from every point `i / 2 ^ t` with `i < 2 ^ t`. -/
def OffGrid (lam : ℚ) (t : ℕ) : Prop := ∀ i : ℕ, i < 2 ^ t → lam ≠ i / 2 ^ t

/-- The uniform probability law on length-`m` Boolean vectors, with value `1 / 2 ^ m`,
nonnegative common mass, and total mass one. -/
def NativeSamplerLaw (m : ℕ) (p : (Fin m → Bool) → ℝ) : Prop :=
  (∀ w : Fin m → Bool, p w = 1 / (2 : ℝ) ^ m) ∧
  (0 ≤ 1 / (2 : ℝ) ^ m) ∧
  (∑ w : Fin m → Bool, p w = 1)

/-- The condition that a slot index is less than `2 ^ addrWidth`. -/
def LegalSlot (addrWidth slot : ℕ) : Prop := slot < 2 ^ addrWidth

/-- Recursively encodes a natural number in little-endian binary by recording parity and
dividing by two. -/
def natToBitsAux : ℕ → Bits
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: natToBitsAux ((n + 1) / 2)

/-- The little-endian bit-list encoding of a natural number. -/
def natToBits (n : ℕ) : Bits := natToBitsAux n

/-- The bit-list encoding of the greatest common divisor of the decoded input values. -/
def bitGcd (x y : Bits) : Bits := natToBits (Nat.gcd (binaryValue x) (binaryValue y))

/-- The bit-list encoding of the product of the decoded inputs reduced modulo the decoded
modulus. -/
def bitModMul (x y m : Bits) : Bits :=
  natToBits ((binaryValue x * binaryValue y) % binaryValue m)

/-- The bit-list encoding of the decoded base raised to the decoded exponent and reduced modulo
the decoded modulus. -/
def bitModPow (x e m : Bits) : Bits :=
  natToBits ((binaryValue x) ^ (binaryValue e) % binaryValue m)

end Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)

/-- Executes a list of probabilistic instructions recursively under an access contract,
threading the program state. -/
def runSteps {w L : ℕ} (c : AccessContract L) : List (ProbInstr w L) → ProbState w → ProbState w
  | [], s => s
  | i :: is, s => runSteps c is (probStep c s i)

/-- An access contract supplying the specified slot functions for forward access only. -/
def nativeForwardContract (L : ℕ) (g : Fin L → ℕ → ℕ) : AccessContract L where
  supplied := fun _ f => decide (f = .forward)
  impl := fun s f => if f = .forward then some (g s) else none

/-- The five-register program that reads a base, exponent, and modulus through three
forward-access slots, computes the modular power, and emits it. -/
def nativeModPowProgram : ProbProgram 5 3 where
  steps :=
    [ ProbInstr.oracle (0 : Fin 3) .forward (0 : Fin 5) (1 : Fin 5),
      ProbInstr.oracle (1 : Fin 3) .forward (0 : Fin 5) (2 : Fin 5),
      ProbInstr.oracle (2 : Fin 3) .forward (0 : Fin 5) (3 : Fin 5),
      ProbInstr.arith .modexp [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)],
      ProbInstr.emit (4 : Fin 5) ]

/-- The forward access contract whose three slots return the specified base, exponent, and
modulus independently of the address. -/
def nativeModPowContract (a e m : ℕ) : AccessContract 3 where
  supplied := fun _ f => decide (f = .forward)
  impl := fun s f =>
    if f = .forward then
      some (fun _ => match s.val with
        | 0 => a
        | 1 => e
        | _ => m)
    else none

/-- The four-register program that reads two inputs through forward-access slots, computes their
greatest common divisor, and emits it. -/
def nativeGcdProgram : ProbProgram 4 2 where
  steps :=
    [ ProbInstr.oracle (0 : Fin 2) .forward (0 : Fin 4) (1 : Fin 4),
      ProbInstr.oracle (1 : Fin 2) .forward (0 : Fin 4) (2 : Fin 4),
      ProbInstr.arith .gcd [(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)],
      ProbInstr.emit (3 : Fin 4) ]

/-- The forward access contract whose two slots return the specified natural inputs
independently of the address. -/
def nativeGcdContract (x y : ℕ) : AccessContract 2 where
  supplied := fun _ f => decide (f = .forward)
  impl := fun s f =>
    if f = .forward then
      some (fun _ => match s.val with
        | 0 => x
        | _ => y)
    else none

/-- A sequence of `m` fair-coin instructions, each followed by emission of the sampled bit from
register zero. -/
def nativeSamplerSteps : (m : ℕ) → List (ProbInstr 1 1)
  | 0 => []
  | m + 1 => ProbInstr.fairCoin (0 : Fin 1) :: ProbInstr.emit (0 : Fin 1) :: nativeSamplerSteps m

/-- The probabilistic program consisting of `m` repetitions of fair-coin sampling and emission. -/
def nativeSamplerProgram (m : ℕ) : ProbProgram 1 1 where
  steps := nativeSamplerSteps m

/-- The output list encoding a finite Boolean vector as natural numbers zero and one. -/
def nativeSamplerOut (m : ℕ) (r : Fin m → Bool) : List ℕ :=
  List.ofFn (fun i : Fin m => if r i then 1 else 0)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs (NumericalKind)

/-- Maps each native parameter kind to its corresponding numerical kind in the finite-precision
core interface. -/
def nativeParamKind : NativeParamKind → NumericalKind
  | .phase => .phase
  | .rotation => .rotation
  | .prepareCoeff => .prepareCoeff
  | .spectralGap => .spectralGap

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
