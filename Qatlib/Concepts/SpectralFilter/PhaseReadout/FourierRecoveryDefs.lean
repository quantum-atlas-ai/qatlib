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

abbrev ArithState (N : ℕ) := (ZMod N × ZMod N) × (Bool × (Fin N → Bool))

namespace ArithState

def data {N : ℕ} (s : ArithState N) : ZMod N := s.1.1

def addend {N : ℕ} (s : ArithState N) : ZMod N := s.1.2

def carry {N : ℕ} (s : ArithState N) : Bool := s.2.1

def ctrl {N : ℕ} (s : ArithState N) : Fin N → Bool := s.2.2

end ArithState

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

def carryOut {N : ℕ} (d a : ZMod N) : Bool := decide (N ≤ d.val + a.val)

def arithGateFn {N : ℕ} : ArithGate N → ArithState N → ArithState N
  | .add, s => ((s.1.1 + s.1.2, s.1.2), s.2.1, s.2.2)
  | .sub, s => ((s.1.1 - s.1.2, s.1.2), s.2.1, s.2.2)
  | .carry, s => ((s.1.1, s.1.2), Bool.xor s.2.1 (carryOut s.1.1 s.1.2), s.2.2)
  | .cadd i, s => if s.2.2 i then ((s.1.1 + s.1.2, s.1.2), s.2.1, s.2.2) else s
  | .csub i, s => if s.2.2 i then ((s.1.1 - s.1.2, s.1.2), s.2.1, s.2.2) else s
  | .mulConst k, s => ((k * s.1.1, s.1.2), s.2.1, s.2.2)
  | .cmulConst i k, s => if s.2.2 i then ((k * s.1.1, s.1.2), s.2.1, s.2.2) else s
  | .rot _ _, s => s

def arithProgramFn {N : ℕ} : List (ArithGate N) → ArithState N → ArithState N
  | [], s => s
  | g :: gs, s => arithProgramFn gs (arithGateFn g s)

noncomputable def arithGateInv {N : ℕ} : ArithGate N → ArithGate N
  | .add => .sub
  | .sub => .add
  | .carry => .carry
  | .cadd i => .csub i
  | .csub i => .cadd i
  | .mulConst k => .mulConst (if h : IsUnit k then k⁻¹ else k)
  | .cmulConst i k => .cmulConst i (if h : IsUnit k then k⁻¹ else k)
  | .rot a t => .rot (-a) t

noncomputable def rotAngle (num : ℤ) (t : ℕ) : ℝ :=
  2 * Real.pi * (num : ℝ) / (2 ^ t : ℝ)

theorem bitIndex_lt {e N : ℕ} (h : e < 2 ^ N) {i : ℕ} (hi : i ∈ e.bitIndices) :
    i < N := by
  have h1 : 2 ^ i ≤ e := Nat.two_pow_le_of_mem_bitIndices hi
  have h2 : 2 ^ i < 2 ^ N := lt_of_le_of_lt h1 h
  exact (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h2

def bitIndexFin {N : ℕ} (hN : 0 < N) (i : ℕ) : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩

def modexpFactors {N : ℕ} (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N) :
    List (Fin N × ZMod N) :=
  (e.bitIndices).map fun i => (bitIndexFin hN i, a ^ (2 ^ i))

def modexpWord {N : ℕ} (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N) :
    List (ArithGate N) :=
  (modexpFactors hN a e h).map fun p => .cmulConst p.1 p.2

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

def countKind {N : ℕ} (gs : List (ArithGate N)) (kind : ArithGate N → Bool) : ℕ :=
  gs.foldl (fun c g => if kind g then c + 1 else c) 0

def isAdd {N : ℕ} : ArithGate N → Bool | .add => true | _ => false

def isSub {N : ℕ} : ArithGate N → Bool | .sub => true | _ => false

def isCarry {N : ℕ} : ArithGate N → Bool | .carry => true | _ => false

def isCadd {N : ℕ} : ArithGate N → Bool | .cadd _ => true | _ => false

def isCsub {N : ℕ} : ArithGate N → Bool | .csub _ => true | _ => false

def isMulConst {N : ℕ} : ArithGate N → Bool | .mulConst _ => true | _ => false

def isCmulConst {N : ℕ} : ArithGate N → Bool | .cmulConst _ _ => true | _ => false

def isRot {N : ℕ} : ArithGate N → Bool | .rot _ _ => true | _ => false

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

def independentLabelGcd {m : ℕ} (d : ℕ) (L : List (Fin m → ℕ)) (r : Fin m) : ℕ :=
  L.foldl (fun g l => Nat.gcd g (l r)) d

def independentDecode {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : Fin m → ℕ :=
  fun r => p.coeff r / independentLabelGcd (p.coeff r) L r

inductive RecoveryVerdict (m : ℕ) where

  | accepted (generators : Fin m → ℕ)

  | rejected
  deriving DecidableEq, Repr

structure RecoveryReceipt (m : ℕ) where

  verdict : RecoveryVerdict m

  generators : Fin m → ℕ

  labelReads : ℕ

  gcdReductions : ℕ

  verificationChecks : ℕ

  groupEnumeration : ℕ

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

structure RecoveryRun (m : ℕ) where

  accepted : Option (RecoveryReceipt m)

  rounds : ℕ

  labelReads : ℕ

  gcdReductions : ℕ

  verificationChecks : ℕ

  groupEnumeration : ℕ

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

structure FourierRun (G : Type*) where

  measured : List G

  shots : ℕ

def cyclicGoodSample {N : ℕ} (hN : 0 < N) (xs : List (ZMod N))
    (H : AddSubgroup (ZMod N)) : Prop :=
  (cyclicDecodedSet hN xs : Set (ZMod N)) = (H : Set (ZMod N))

def cyclicRejectionEvent {N : ℕ} (hN : 0 < N) (xs : List (ZMod N))
    (H : AddSubgroup (ZMod N)) : Prop :=
  (cyclicDecodedSet hN xs : Set (ZMod N)) ≠ (H : Set (ZMod N))

def cyclicZeroSample {N : ℕ} (hN : 0 < N) : List (ZMod N) := []

end Qatlib.Concepts.SpectralFilter.PhaseReadout
