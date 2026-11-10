/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Qatlib.Concepts.DyadicProgram.DyadicContract.DyadicMpsProgram
import Qatlib.Concepts.TensorNetwork.GaugeInvariance
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

set_option autoImplicit false

open Qatlib.Concepts.DyadicProgram.DyadicContract

open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Concepts.DyadicOverlap.OverlapContract

open Matrix
open scoped BigOperators ComplexConjugate
open Qatlib.Concepts.DyadicProgram.DyadicContract (GI add mul decode scalar run initial dot row)
open Qatlib.Concepts.MpsAdaptation.MpsTransfer (mpsAmplitude)

def conjGI (z : GI) : GI := (z.1, -z.2)

def transferEntry {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) : GI :=
  (List.ofFn fun s : Fin d => mul (conjGI (A s a a')) (B s b b')).foldl add ((0, 0) : GI)

def toIdx {Da Db : ℕ} (a : Fin Da) (b : Fin Db) : Fin (Da * Db) :=
  finProdFinEquiv (a, b)

def ofIdx {Da Db : ℕ} (i : Fin (Da * Db)) : Fin Da × Fin Db :=
  finProdFinEquiv.symm i

def transferMat {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI) :
    Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI :=
  fun i j => transferEntry A B (ofIdx i).1 (ofIdx j).1 (ofIdx i).2 (ofIdx j).2

def transferList {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    List (Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI) :=
  List.ofFn fun j : Fin n => transferMat (A j) (B j)

def overlapProgram {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) : GI :=
  if h : 0 < Da * Db then scalar h (transferList A B) else ((1, 0) : GI)

noncomputable def decodeTensor {n d D : ℕ} (p : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) GI) :
    Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i s a a' => decode p (A i s a a')

inductive IntOp where
  | mul | add | sub | neg | keep
  deriving DecidableEq

structure Ev where

  op : IntOp

  a : ℤ

  b : ℤ

  r : ℤ
  deriving DecidableEq

def Ev.wf (e : Ev) : Prop :=
  match e.op with
  | .mul => e.r = e.a * e.b
  | .add => e.r = e.a + e.b
  | .sub => e.r = e.a - e.b
  | .neg => e.r = -e.a
  | .keep => e.r = e.a

def logWF (L : List Ev) : Prop := ∀ e ∈ L, Ev.wf e

def mulEv (x y : GI) : List Ev :=
  [⟨.mul, x.1, y.1, x.1 * y.1⟩,
   ⟨.mul, x.2, y.2, x.2 * y.2⟩,
   ⟨.sub, x.1 * y.1, x.2 * y.2, x.1 * y.1 - x.2 * y.2⟩,
   ⟨.mul, x.1, y.2, x.1 * y.2⟩,
   ⟨.mul, x.2, y.1, x.2 * y.1⟩,
   ⟨.add, x.1 * y.2, x.2 * y.1, x.1 * y.2 + x.2 * y.1⟩]

def addEv (x y : GI) : List Ev :=
  [⟨.add, x.1, y.1, x.1 + y.1⟩,
   ⟨.add, x.2, y.2, x.2 + y.2⟩]

def negEv (x : GI) : List Ev :=
  [⟨.keep, x.1, 0, x.1⟩,
   ⟨.neg, x.2, 0, -x.2⟩]

def transferEntryEv {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) : GI × List Ev :=
  (List.ofFn fun s : Fin d => (A s a a', B s b b')).foldl
    (fun (acc : GI × List Ev) (pair : GI × GI) =>
      let ca := conjGI pair.1
      let m := mul ca pair.2
      (add acc.1 m, acc.2 ++ negEv pair.1 ++ mulEv ca pair.2 ++ addEv acc.1 m))
    (((0, 0) : GI), [])

def transferMatEv {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI) : List Ev :=
  (List.ofFn fun i : Fin (Da * Db) =>
    (List.ofFn fun j : Fin (Da * Db) =>
      (transferEntryEv A B (ofIdx i).1 (ofIdx j).1 (ofIdx i).2 (ofIdx j).2).2).flatten).flatten

def constructionEv {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) : List Ev :=
  (List.ofFn fun j : Fin n => transferMatEv (A j) (B j)).flatten

def dotEv {D : ℕ} (v : Fin D → GI) (A : Matrix (Fin D) (Fin D) GI) (j : Fin D) :
    GI × List Ev :=
  (List.ofFn fun i : Fin D => (v i, A i j)).foldl
    (fun (acc : GI × List Ev) (pair : GI × GI) =>
      let m := mul pair.1 pair.2
      (add acc.1 m, acc.2 ++ mulEv pair.1 pair.2 ++ addEv acc.1 m))
    (((0, 0) : GI), [])

def rowEv {D : ℕ} (v : Fin D → GI) (A : Matrix (Fin D) (Fin D) GI) : List Ev :=
  (List.ofFn fun j : Fin D => (dotEv v A j).2).flatten

def runEv {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) : List Ev :=
  (As.foldl
    (fun (acc : (Fin D → GI) × List Ev) A => (row acc.1 A, acc.2 ++ rowEv acc.1 A))
    (initial D, [])).2

def overlapLog {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) : List Ev :=
  constructionEv A B ++ runEv (transferList A B)

def overlapTrace {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) : GI × List Ev :=
  (overlapProgram A B, overlapLog A B)

def BoundedGI (B : ℕ) (z : GI) : Prop := z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B

def Ev.bounded (B : ℕ) (e : Ev) : Prop :=
  e.a.natAbs ≤ B ∧ e.b.natAbs ≤ B ∧ e.r.natAbs ≤ B

def logBounded (B : ℕ) (L : List Ev) : Prop := ∀ e ∈ L, Ev.bounded B e

def constructionBound (n d Da Db : ℕ) : ℕ := 12 * n * d * (Da * Db) ^ 2

def rowBound (n Da Db : ℕ) : ℕ := 12 * n * (Da * Db) ^ 2

def eventBound (n d Da Db : ℕ) : ℕ := 12 * n * (d + 1) * (Da * Db) ^ 2

def widthBound (n d D w : ℕ) : ℕ :=
  n * (2 * w + 2 + 2 * Nat.log 2 (D + 1) + Nat.log 2 (d + 1))

def magnitudeBound (n d D w : ℕ) : ℕ := 2 ^ widthBound n d D w

def prodITensors : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) GI :=
  fun _ s _ _ => if (s : ℕ) = 0 then ((1, 0) : GI) else ((0, 1) : GI)

def zeroTensors : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) GI :=
  fun _ _ _ _ => ((0, 0) : GI)

def bellTensors : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) GI :=
  fun i s a b =>
    if (i : ℕ) = 0 then (if (s : ℕ) = (b : ℕ) then ((1, 0) : GI) else ((0, 0) : GI))
    else (if (s : ℕ) = (a : ℕ) then ((1, 0) : GI) else ((0, 0) : GI))

def orthoA : Fin 1 → Fin 2 → Matrix (Fin 1) (Fin 1) GI :=
  fun _ s _ _ => if (s : ℕ) = 0 then ((1, 0) : GI) else ((0, 0) : GI)

def orthoB : Fin 1 → Fin 2 → Matrix (Fin 1) (Fin 1) GI :=
  fun _ s _ _ => if (s : ℕ) = 0 then ((0, 0) : GI) else ((1, 0) : GI)

def zeroPhysicalTensors : Fin 1 → Fin 0 → Matrix (Fin 1) (Fin 1) GI :=
  fun _ _ _ _ => ((0, 0) : GI)

def emptyTensors : Fin 0 → Fin 2 → Matrix (Fin 1) (Fin 1) GI :=
  fun i => Fin.elim0 i

def consumerProductI : Prop :=
  overlapProgram prodITensors prodITensors = ((4, 0) : GI) ∧
    decode (2 * 0 * 2) (overlapProgram prodITensors prodITensors) = (4 : ℂ) ∧
    (∑ x : Fin 2 → Fin 2,
      (Complex.normSq (mpsAmplitude (decodeTensor 0 prodITensors) x) : ℂ)) = 4

def consumerZeroInput : Prop :=
  overlapProgram zeroTensors zeroTensors = ((0, 0) : GI) ∧
    decode (2 * 0 * 2) (overlapProgram zeroTensors zeroTensors) = (0 : ℂ) ∧
    (∑ x : Fin 2 → Fin 2,
      (Complex.normSq (mpsAmplitude (decodeTensor 0 zeroTensors) x) : ℂ)) = 0

def consumerBell : Prop :=
  overlapProgram bellTensors bellTensors = ((2, 0) : GI) ∧
    decode (2 * 0 * 2) (overlapProgram bellTensors bellTensors) = (2 : ℂ) ∧
    (∑ x : Fin 2 → Fin 2,
      (Complex.normSq (mpsAmplitude (decodeTensor 0 bellTensors) x) : ℂ)) = 2

def consumerOrthogonal : Prop :=
  overlapProgram orthoA orthoB = ((0, 0) : GI) ∧
    decode (2 * 0 * 1) (overlapProgram orthoA orthoB) = (0 : ℂ) ∧
    (∑ x : Fin 1 → Fin 2,
      conj (mpsAmplitude (decodeTensor 0 orthoA) x)
        * mpsAmplitude (decodeTensor 0 orthoB) x) = 0

def consumerEmptyChain : Prop :=
  overlapProgram emptyTensors emptyTensors = ((1, 0) : GI) ∧
    decode (2 * 0 * 0) (overlapProgram emptyTensors emptyTensors) = (1 : ℂ) ∧
    (∑ x : Fin 0 → Fin 2,
      (Complex.normSq (mpsAmplitude (decodeTensor 0 emptyTensors) x) : ℂ)) = 1

def consumerZeroPhysical : Prop :=
  overlapProgram zeroPhysicalTensors zeroPhysicalTensors = ((0, 0) : GI) ∧
    decode (2 * 0 * 1) (overlapProgram zeroPhysicalTensors zeroPhysicalTensors) = (0 : ℂ) ∧
    (∑ x : Fin 1 → Fin 0,
      (Complex.normSq (mpsAmplitude (decodeTensor 0 zeroPhysicalTensors) x) : ℂ)) = 0

def clause1Statement : Prop :=
  ∀ (n d Da Db p : ℕ) [NeZero Da] [NeZero Db]
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI),
    decode (2 * p * n) (overlapProgram A B)
      = ∑ x : Fin n → Fin d,
          conj (mpsAmplitude (decodeTensor p A) x) * mpsAmplitude (decodeTensor p B) x
    ∧ (n = 0 → overlapProgram A B = ((1, 0) : GI))
    ∧ (d = 0 → n ≠ 0 → overlapProgram A B = ((0, 0) : GI))

def clause2Statement : Prop :=
  (∀ (n d D p : ℕ) [NeZero D] (A : Fin n → Fin d → Matrix (Fin D) (Fin D) GI),
    (decode (2 * p * n) (overlapProgram A A)).im = 0
    ∧ 0 ≤ (decode (2 * p * n) (overlapProgram A A)).re
    ∧ decode (2 * p * n) (overlapProgram A A)
        = ∑ x : Fin n → Fin d, (Complex.normSq (mpsAmplitude (decodeTensor p A) x) : ℂ)
    ∧ (overlapProgram A A).2 = 0
    ∧ 0 ≤ (overlapProgram A A).1
    ∧ (n = 0 → overlapProgram A A = ((1, 0) : GI))
    ∧ (d = 0 → n ≠ 0 → overlapProgram A A = ((0, 0) : GI)))
  ∧ consumerProductI
  ∧ consumerZeroInput
  ∧ consumerBell
  ∧ consumerOrthogonal
  ∧ consumerEmptyChain
  ∧ consumerZeroPhysical

def clause3Statement : Prop :=
  ∀ (n d Da Db w : ℕ) [NeZero Da] [NeZero Db]
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI),
    (hA : ∀ (i : Fin n) (s : Fin d) (a a' : Fin Da),
      (A i s a a').1.natAbs ≤ 2 ^ w ∧ (A i s a a').2.natAbs ≤ 2 ^ w) →
    (hB : ∀ (i : Fin n) (s : Fin d) (b b' : Fin Db),
      (B i s b b').1.natAbs ≤ 2 ^ w ∧ (B i s b b').2.natAbs ≤ 2 ^ w) →
    (overlapTrace A B).1 = overlapProgram A B
    ∧ logWF (overlapTrace A B).2
    ∧ (constructionEv A B).length ≤ constructionBound n d Da Db
    ∧ (runEv (transferList A B)).length ≤ rowBound n Da Db
    ∧ (overlapTrace A B).2.length ≤ eventBound n d Da Db
    ∧ (∀ D : ℕ, Da ≤ D → Db ≤ D →
        (constructionEv A B).length ≤ 12 * n * d * D ^ 4
        ∧ (runEv (transferList A B)).length ≤ 12 * n * D ^ 4)
    ∧ (∀ D : ℕ, Da ≤ D → Db ≤ D →
        logBounded (magnitudeBound n d D w) (overlapTrace A B).2
        ∧ (∀ (i : Fin n) (a a' : Fin Da) (b b' : Fin Db),
            BoundedGI (magnitudeBound n d D w) (transferEntry (A i) (B i) a a' b b'))
        ∧ (∀ j : Fin (Da * Db), BoundedGI (magnitudeBound n d D w) (run (transferList A B) j))
        ∧ BoundedGI (magnitudeBound n d D w) (overlapProgram A B))
    ∧ (n = 0 → overlapTrace A B = (((1, 0) : GI), []))
    ∧ (d = 0 → n ≠ 0 → overlapProgram A B = ((0, 0) : GI))

end Qatlib.Concepts.DyadicOverlap.OverlapContract
