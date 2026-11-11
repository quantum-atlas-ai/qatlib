/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
import Qatlib.Concepts.HspRecovery.BackendAudit.CountedCharacterTableDecoder
import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecovery
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic words and Fourier recovery records

This module defines arithmetic-register states, instruction words, and resource ledgers for
modular arithmetic. It also supplies label-based decoding, acceptance records, and repeated
recovery attempts for finite abelian Fourier sampling, in the algorithmic setting of
[Kitaev1995].

`arithGateFn` describes the classical register action of each instruction; rotation instructions
leave these registers unchanged and carry their angles separately through `rotAngle`. The
recovery records count label reads, gcd reductions, and checks, while `cyclicGoodSample` records
exact equality of the decoded set with a specified subgroup.

## Main statements

* `modexpWord`: controlled constant multiplications indexed by the nonzero bits of an exponent.
* `arithLedger`: instruction counts together with shots and width.
* `recoveryRun`: repeated decoding attempts stopping at the first accepted receipt.

## References

* [Kitaev, 1995][Kitaev1995]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open Qatlib.Concepts.HspRecovery.ReductionCore.InPlace
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib
open Matrix
open scoped Classical BigOperators

/-- The arithmetic register type containing data and addend residues, a carry bit, and `N`
control bits. -/
abbrev ArithState (N : ℕ) := (ZMod N × ZMod N) × (Bool × (Fin N → Bool))

namespace ArithState

/-- The data residue stored in an arithmetic state. -/
def data {N : ℕ} (s : ArithState N) : ZMod N := s.1.1

/-- The addend residue stored in an arithmetic state. -/
def addend {N : ℕ} (s : ArithState N) : ZMod N := s.1.2

/-- The carry bit stored in an arithmetic state. -/
def carry {N : ℕ} (s : ArithState N) : Bool := s.2.1

/-- The control-bit function stored in an arithmetic state. -/
def ctrl {N : ℕ} (s : ArithState N) : Fin N → Bool := s.2.2

end ArithState

/-- Arithmetic instruction syntax for addition, subtraction, carry toggles, controlled variants,
constant multiplication, and rotations. -/
inductive ArithGate (N : ℕ) where

  | add : ArithGate N

  | sub : ArithGate N

  | carry : ArithGate N

  | cadd : Fin N → ArithGate N

  | csub : Fin N → ArithGate N

  | mulConst : ZMod N → ArithGate N

  | cmulConst : Fin N → ZMod N → ArithGate N

  | rot : ℤ → ℕ → ArithGate N
  deriving DecidableEq, Repr

/-- Test whether the sum of the canonical residue representatives reaches or exceeds the
modulus. -/
def carryOut {N : ℕ} (d a : ZMod N) : Bool := decide (N ≤ d.val + a.val)

/-- The classical register action of an arithmetic instruction, with rotation instructions
acting as the identity on these registers. -/
def arithGateFn {N : ℕ} : ArithGate N → ArithState N → ArithState N
  | .add, s => ((s.1.1 + s.1.2, s.1.2), s.2.1, s.2.2)
  | .sub, s => ((s.1.1 - s.1.2, s.1.2), s.2.1, s.2.2)
  | .carry, s => ((s.1.1, s.1.2), Bool.xor s.2.1 (carryOut s.1.1 s.1.2), s.2.2)
  | .cadd i, s => if s.2.2 i then ((s.1.1 + s.1.2, s.1.2), s.2.1, s.2.2) else s
  | .csub i, s => if s.2.2 i then ((s.1.1 - s.1.2, s.1.2), s.2.1, s.2.2) else s
  | .mulConst k, s => ((k * s.1.1, s.1.2), s.2.1, s.2.2)
  | .cmulConst i k, s => if s.2.2 i then ((k * s.1.1, s.1.2), s.2.1, s.2.2) else s
  | .rot _ _, s => s

/-- Execute a list of arithmetic instructions from left to right on an arithmetic state. -/
def arithProgramFn {N : ℕ} : List (ArithGate N) → ArithState N → ArithState N
  | [], s => s
  | g :: gs, s => arithProgramFn gs (arithGateFn g s)

/-- Reverse additions and rotation angles and invert unit multiplication constants, leaving
nonunit multiplication constants unchanged. -/
noncomputable def arithGateInv {N : ℕ} : ArithGate N → ArithGate N
  | .add => .sub
  | .sub => .add
  | .carry => .carry
  | .cadd i => .csub i
  | .csub i => .cadd i
  | .mulConst k => .mulConst (if h : IsUnit k then k⁻¹ else k)
  | .cmulConst i k => .cmulConst i (if h : IsUnit k then k⁻¹ else k)
  | .rot a t => .rot (-a) t

/-- The real rotation angle `2*π*num/2^t` specified by an integer numerator and a dyadic
denominator. -/
noncomputable def rotAngle (num : ℤ) (t : ℕ) : ℝ :=
  2 * Real.pi * (num : ℝ) / (2 ^ t : ℝ)

/-- Every nonzero bit position of an exponent less than `2^N` is less than `N`. -/
theorem bitIndex_lt {e N : ℕ} (h : e < 2 ^ N) {i : ℕ} (hi : i ∈ e.bitIndices) :
    i < N := by
  have h1 : 2 ^ i ≤ e := Nat.two_pow_le_of_mem_bitIndices hi
  have h2 : 2 ^ i < 2 ^ N := lt_of_le_of_lt h1 h
  exact (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h2

/-- Convert a natural index to `Fin N` by reduction modulo the positive width. -/
def bitIndexFin {N : ℕ} (hN : 0 < N) (i : ℕ) : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩

/-- The control indices and constants `a^(2^i)` associated with the nonzero bit positions of the
exponent. -/
def modexpFactors {N : ℕ} (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N) :
    List (Fin N × ZMod N) :=
  (e.bitIndices).map fun i => (bitIndexFin hN i, a ^ (2 ^ i))

/-- The controlled constant-multiplication word obtained from the binary factors of the
exponent. -/
def modexpWord {N : ℕ} (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N) :
    List (ArithGate N) :=
  (modexpFactors hN a e h).map fun p => .cmulConst p.1 p.2

/-- A resource record containing total and per-kind arithmetic instruction counts, shots, and
register width. -/
structure ArithLedger (N : ℕ) where

  gates : ℕ

  adds : ℕ

  subs : ℕ

  carries : ℕ

  cadds : ℕ

  csubs : ℕ

  mulConsts : ℕ

  cmulConsts : ℕ

  rots : ℕ

  shots : ℕ

  width : ℕ

/-- Count the instructions in a word satisfying a Boolean classifier. -/
def countKind {N : ℕ} (gs : List (ArithGate N)) (kind : ArithGate N → Bool) : ℕ :=
  gs.foldl (fun c g => if kind g then c + 1 else c) 0

/-- Test whether an arithmetic instruction is an unconditional addition. -/
def isAdd {N : ℕ} : ArithGate N → Bool | .add => true | _ => false

/-- Test whether an arithmetic instruction is an unconditional subtraction. -/
def isSub {N : ℕ} : ArithGate N → Bool | .sub => true | _ => false

/-- Test whether an arithmetic instruction is a carry toggle. -/
def isCarry {N : ℕ} : ArithGate N → Bool | .carry => true | _ => false

/-- Test whether an arithmetic instruction is a controlled addition. -/
def isCadd {N : ℕ} : ArithGate N → Bool | .cadd _ => true | _ => false

/-- Test whether an arithmetic instruction is a controlled subtraction. -/
def isCsub {N : ℕ} : ArithGate N → Bool | .csub _ => true | _ => false

/-- Test whether an arithmetic instruction is an unconditional constant multiplication. -/
def isMulConst {N : ℕ} : ArithGate N → Bool | .mulConst _ => true | _ => false

/-- Test whether an arithmetic instruction is a controlled constant multiplication. -/
def isCmulConst {N : ℕ} : ArithGate N → Bool | .cmulConst _ _ => true | _ => false

/-- Test whether an arithmetic instruction is a rotation. -/
def isRot {N : ℕ} : ArithGate N → Bool | .rot _ _ => true | _ => false

/-- Build the total and per-kind instruction counts of an arithmetic word, together with the
supplied shot count and width `N`. -/
def arithLedger {N : ℕ} (gs : List (ArithGate N)) (shots : ℕ) : ArithLedger N where
  gates := gs.length
  adds := countKind gs fun g => match g with | .add => true | _ => false
  subs := countKind gs fun g => match g with | .sub => true | _ => false
  cadds := countKind gs fun g => match g with | .cadd _ => true | _ => false
  carries := countKind gs fun g => match g with | .carry => true | _ => false
  csubs := countKind gs fun g => match g with | .csub _ => true | _ => false
  mulConsts := countKind gs fun g => match g with | .mulConst _ => true | _ => false
  cmulConsts := countKind gs fun g => match g with | .cmulConst _ _ => true | _ => false
  rots := countKind gs fun g => match g with | .rot _ _ => true | _ => false
  shots := shots
  width := N

/-- Fold gcd over the labels in one coordinate, starting from the supplied integer `d`. -/
def independentLabelGcd {m : ℕ} (d : ℕ) (L : List (Fin m → ℕ)) (r : Fin m) : ℕ :=
  L.foldl (fun g l => Nat.gcd g (l r)) d

/-- Decode each Smith coordinate by dividing its coefficient by the gcd of that coefficient with
the sampled coordinate labels. -/
def independentDecode {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : Fin m → ℕ :=
  fun r => p.coeff r / independentLabelGcd (p.coeff r) L r

/-- An acceptance result carrying coordinate generators, or a rejection result. -/
inductive RecoveryVerdict (m : ℕ) where

  | accepted (generators : Fin m → ℕ)

  | rejected
  deriving DecidableEq, Repr

/-- The verdict, decoded generators, and operation counts for one recovery attempt. -/
structure RecoveryReceipt (m : ℕ) where

  verdict : RecoveryVerdict m

  generators : Fin m → ℕ

  labelReads : ℕ

  gcdReductions : ℕ

  verificationChecks : ℕ

  groupEnumeration : ℕ

/-- Decode a label list and accept exactly when every decoded coordinate is greater than one,
recording label, gcd, and check counts with zero group enumeration. -/
def recoveryAttempt {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : RecoveryReceipt m where
  generators := independentDecode p L
  verdict :=
    if ∀ r : Fin m, 1 < independentDecode p L r then
      RecoveryVerdict.accepted (independentDecode p L)
    else RecoveryVerdict.rejected
  labelReads := m * L.length
  gcdReductions := m * L.length
  verificationChecks := L.length * m
  groupEnumeration := 0

/-- The first accepted recovery receipt, if any, together with the number of rounds and
accumulated operation counts. -/
structure RecoveryRun (m : ℕ) where

  accepted : Option (RecoveryReceipt m)

  rounds : ℕ

  labelReads : ℕ

  gcdReductions : ℕ

  verificationChecks : ℕ

  groupEnumeration : ℕ

/-- Try successive label lists until an attempt is accepted or the lists are exhausted,
accumulating the attempted rounds and operation counts. -/
def recoveryRun {m n : ℕ} (p : NormalizedSmithData m n)
    (Ls : List (List (FactorLabel p))) : RecoveryRun m :=
  let rec go : List (List (FactorLabel p)) → ℕ → RecoveryRun m
    | [], rounds =>
        { accepted := none, rounds := rounds, labelReads := 0, gcdReductions := 0,
          verificationChecks := 0, groupEnumeration := 0 }
    | L :: rest, rounds =>
        let a := recoveryAttempt p L
        match a.verdict with
        | .accepted _ =>
            { accepted := some a, rounds := rounds + 1, labelReads := a.labelReads,
              gcdReductions := a.gcdReductions,
              verificationChecks := a.verificationChecks,
              groupEnumeration := a.groupEnumeration }
        | .rejected =>
            let r := go rest (rounds + 1)
            { accepted := r.accepted, rounds := r.rounds,
              labelReads := a.labelReads + r.labelReads,
              gcdReductions := a.gcdReductions + r.gcdReductions,
              verificationChecks := a.verificationChecks + r.verificationChecks,
              groupEnumeration := a.groupEnumeration + r.groupEnumeration }
  go Ls 0

/-- A record of measured labels and a separate shot count. -/
structure FourierRun (G : Type*) where

  measured : List G

  shots : ℕ

/-- The proposition that the cyclic decoded set equals the specified subgroup. -/
def cyclicGoodSample {N : ℕ} (hN : 0 < N) (xs : List (ZMod N))
    (H : AddSubgroup (ZMod N)) : Prop :=
  (cyclicDecodedSet hN xs : Set (ZMod N)) = (H : Set (ZMod N))

/-- The proposition that the cyclic decoded set differs from the specified subgroup. -/
def cyclicRejectionEvent {N : ℕ} (hN : 0 < N) (xs : List (ZMod N))
    (H : AddSubgroup (ZMod N)) : Prop :=
  (cyclicDecodedSet hN xs : Set (ZMod N)) ≠ (H : Set (ZMod N))

/-- The empty list of cyclic samples. -/
def cyclicZeroSample {N : ℕ} (hN : 0 < N) : List (ZMod N) := []

end Qatlib.Concepts.SpectralFilter.PhaseReadout
