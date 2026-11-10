/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianDefs
import Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianSieve
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge
import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawDihe
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve

open Qatlib
open scoped Classical BigOperators ENNReal

structure ActualHalfWidthRecord (N : ℕ) where

  label : ZMod N

  width : ℕ
  deriving DecidableEq

noncomputable def actualFreshRecord {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w : ℕ) : PMF (ActualHalfWidthRecord N) :=
  (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => ⟨q.1, w⟩)

noncomputable def actualHalfWidthRecords {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w : ℕ) : ℕ → PMF (List (ActualHalfWidthRecord N))
  | 0 => pure []
  | i + 1 =>
    (actualFreshRecord f w).bind fun r =>
      (actualHalfWidthRecords f w i).map fun L =>
        r :: L

noncomputable def actualLabelLaw {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) :
    PMF (ZMod N) :=
  (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => q.1)

noncomputable def actualHalfWidthRecordLaw {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w : ℕ) (i : ℕ) : PMF (List (ActualHalfWidthRecord N)) :=
  actualHalfWidthRecords f w i

def combineActualRecords {N : ℕ} (a : ℕ) (r₁ r₂ : ActualHalfWidthRecord N) :
    ActualHalfWidthRecord N :=
  ⟨r₁.label - r₂.label, (r₁.width + r₂.width) / a⟩

noncomputable def actualLayerCombineLaw {N : ℕ} (a : ℕ) :
    List (ActualHalfWidthRecord N × ActualHalfWidthRecord N) →
      PMF (List (ActualHalfWidthRecord N))
  | [] => pure []
  | (r₁, r₂) :: ps =>
    (PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (actualLayerCombineLaw a ps).map fun tail =>
        if b = 1 then combineActualRecords a r₁ r₂ :: tail else tail

noncomputable def actualLayerCombine {N : ℕ} (a q : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    PMF (List (ActualHalfWidthRecord N)) :=
  actualLayerCombineLaw a
    (pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L)

noncomputable def actualLayeredCombine {N : ℕ} (a q : ℕ) :
    ℕ → List (ActualHalfWidthRecord N) → PMF (List (ActualHalfWidthRecord N))
  | 0, L => pure L
  | j + 1, L => (actualLayeredCombine a q j L).bind (actualLayerCombine a q)

noncomputable def actualCombinedRun {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    PMF (List (ActualHalfWidthRecord N)) :=
  (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q m)

def actualIdealLabel (N : ℕ) : ZMod N :=
  if N % 2 = 0 then ((N / 2 : ℕ) : ZMod N) else (0 : ZMod N)

def isActualIdealHit {N : ℕ} (r : ActualHalfWidthRecord N) : Prop :=
  r.label = actualIdealLabel N

def hasIdealHit {N : ℕ} (L : List (ActualHalfWidthRecord N)) : Prop :=
  ∃ r ∈ L, isActualIdealHit r

noncomputable def actualIdealHitEvent {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    PMF Bool :=
  (actualCombinedRun f a q w L0 m).map
    (fun L => decide (hasIdealHit L))

noncomputable def actualIdealHitMass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    ℝ≥0∞ :=
  actualIdealHitEvent f a q w L0 m true

noncomputable def actualFailureMass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    ℝ≥0∞ :=
  1 - actualIdealHitMass f a q w L0 m

def massIndicator (p : Prop) : ℝ≥0∞ := if p then 1 else 0

noncomputable def idealMissWeight {N : ℕ} (L : List (ActualHalfWidthRecord N)) :
    ℝ≥0∞ :=
  massIndicator (¬ hasIdealHit L)

noncomputable def actualMissMass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (w L0 : ℕ) :
    ℝ≥0∞ :=
  ∑' L : List (ActualHalfWidthRecord N),
    (actualHalfWidthRecords f w L0) L * idealMissWeight L

noncomputable def actualMissProbOne {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (w : ℕ) :
    ℝ≥0∞ :=
  ∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
    massIndicator (¬ isActualIdealHit r)

noncomputable def actualFreshIdealHitMass (N L0 : ℕ) : ℝ :=
  1 - (1 - 1 / (N : ℝ)) ^ L0

noncomputable def actualFreshFailureMass (N L0 : ℕ) : ℝ :=
  (1 - 1 / (N : ℝ)) ^ L0

def descentFold (stage : PMF (Option (List Bool)) → PMF (Option (List Bool)))
    (k : ℕ) : PMF (Option (List Bool)) :=
  (List.range k).foldl (fun acc _ => stage acc) (PMF.pure (some ([] : List Bool)))

def extendOpt (bs : List Bool) : Option Bool → Option (List Bool)
  | none => none
  | some b => some (bs ++ [b])

noncomputable def descentExtend (inner : PMF (Option Bool)) (bs : List Bool) :
    PMF (Option (List Bool)) :=
  inner.map (extendOpt bs)

noncomputable def stageOpt (inner : List Bool → PMF (Option Bool)) :
    Option (List Bool) → PMF (Option (List Bool))
  | none => PMF.pure none
  | some bs => descentExtend (inner bs) bs

noncomputable def descentStage (inner : List Bool → PMF (Option Bool))
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  st.bind (stageOpt inner)

noncomputable def idealDescentStage (n : ℕ) (s : ZMod (2 ^ n))
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  descentStage
    (fun bs => (dihedralSieveRun (n - bs.length) (descentDepth (n - bs.length))
        (descentSlope n bs.length s)).1) st

noncomputable def actualDescentStage {n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S)
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  descentStage
    (fun bs => dihedralSieveActual (n - bs.length) (descentDepth (n - bs.length))
      (f ∘ descentEmbedding n bs)) st

structure RepTransportWitness {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (family : IrrepFamily N Label) where

  toLabel : ZMod N → Label

  toRowNat : ZMod N × Bool → ℕ

  stages : StagedPmfBridge (recordStages N S) 2

  row_lt : ∀ k : ZMod N, ∀ t : Bool,
    toRowNat (k, t) < dimFixed (family.irrep (toLabel k)) s

  joint : ∀ V : Label, ∀ row : Fin (dimFixed (family.irrep V) s),
    repJointMass (family.irrep V) row.val =
      ∑' q : ZMod N × Bool × S,
        if toLabel q.1 = V ∧ toRowNat (q.1, q.2.1) = row.val then
          ENNReal.toReal (actualRecordFiniteLaw f q) else 0

  labelMass : ∀ V : Label,
    repLabelMass (family.irrep V) s =
      ∑' q : ZMod N × Bool × S,
        if toLabel q.1 = V then
          ENNReal.toReal (actualRecordFiniteLaw f q) else 0

  stage0 : stages.law 0 = actualRecordFiniteLaw f

  stage1 : ∀ k : ZMod N, ∀ t : Bool,
    ENNReal.toReal (stages.law 1 (k, t)) = 1 / (2 * N)

  stage2 : ∀ k : ZMod N, ENNReal.toReal (stages.law 2 k) = 1 / N

  extraction : ∀ k : ZMod N, ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
    ∀ t : Bool, ∀ z : S,
      dihedralRecordJoint N f ((k, t), z) = γ z * dihedralQubitState N s k t

def RepTransportTarget (N : ℕ) [NeZero N] : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg N → S) (s : ZMod N), DihedralReflectionHides N f s →
    ∀ (Label : Type) [Fintype Label] [DecidableEq Label]
      (family : IrrepFamily N Label),
      ∃ w : RepTransportWitness f s family,
        w.stages.law 0 = actualRecordFiniteLaw f ∧
        (∀ k : ZMod N, ∀ t : Bool,
          ENNReal.toReal (w.stages.law 1 (k, t)) = 1 / (2 * N)) ∧
        (∀ k : ZMod N, ENNReal.toReal (w.stages.law 2 k) = 1 / N) ∧
        (QueryCount (dihedralRecordCircuit (N := N) (S := S)) = 1) ∧
        (GateCount (dihedralRecordCircuit (N := N) (S := S)) = 1)

noncomputable def actualStageLaw {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (a q w L0 : ℕ) : ℕ → PMF (List (ActualHalfWidthRecord N)) :=
  fun j => (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q j)

noncomputable def sieveKeptRecordCount (m L0 : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), L0 / 2 ^ j

def lowPart {n : ℕ} (x : ZMod (2 ^ n)) : ℕ := x.val % 2 ^ (n - 1)

def highPart {n : ℕ} (x : ZMod (2 ^ n)) : ℕ := x.val / 2 ^ (n - 1)

def borrowBit {n : ℕ} (x y : ZMod (2 ^ n)) : Fin 2 :=
  if lowPart y < lowPart x then 1 else 0

structure DecLabel (n R : ℕ) where

  val : ZMod (2 ^ n)

  sup : Finset (Fin R)

  off : Fin 2
  deriving DecidableEq

def devPairWith (fuel : ℕ) (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (L : List α) : List (α × α) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match L with
      | [] => []
      | r :: rest =>
          match rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) with
          | none => devPairWith fuel n label w t rest
          | some r' => (r, r') :: devPairWith fuel n label w t (rest.erase r')

structure DecShadow (n R : ℕ) where

  low : ℕ

  sup : Finset (Fin R)

  off : Fin 2
  deriving DecidableEq

def decShadow {n R : ℕ} (x : DecLabel n R) : DecShadow n R :=
  ⟨lowPart x.val, x.sup, x.off⟩

def shadowLabel {n R : ℕ} (s : DecShadow n R) : ZMod (2 ^ n) :=
  ((s.low % 2 ^ n : ℕ) : ZMod (2 ^ n))

def shChild {n R : ℕ} (p : DecShadow n R × DecShadow n R) : DecShadow n R :=
  ⟨(p.2.low + 2 ^ (n - 1) - p.1.low) % 2 ^ (n - 1),
    p.2.sup ∪ p.1.sup,
    p.2.off + p.1.off + if p.2.low < p.1.low then 1 else 0⟩

def shFresh {n R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1))) : List (DecShadow n R) :=
  List.ofFn fun i : Fin R => ⟨(low i).val, {i}, 0⟩

noncomputable def shTapeLayer (n m j : ℕ) {R : ℕ} (tape : List (Fin 2))
    (L : List (DecShadow n R)) : List (DecShadow n R) :=
  List.filterMap (fun p => if p.2 = 1 then some (shChild (p.1.1, p.1.2)) else none)
    ((sievePairWith n (fun s : DecShadow n R => shadowLabel s)
      (sieveWindowWidth n m j) (m * j) L).zip tape)

noncomputable def shSkel {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) : List (DecShadow n R) :=
  List.foldl (fun L j => shTapeLayer n m j.val (tape j) L) (shFresh low) (List.finRange m)

end Qatlib.Concepts.HspRecovery.OpenSieve
