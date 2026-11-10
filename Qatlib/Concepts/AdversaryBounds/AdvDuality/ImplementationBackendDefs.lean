/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.OfFn
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Foundations.IntervalArith.IntervalOps.RationalIntervalArithmeticDefs
import Qatlib.Concepts.ResourceBounds.AsymBounds.EffectiveAccessDefs
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped BigOperators
open Qatlib.Foundations.IntervalArith.IntervalOps (Interval Valid Contains unit roundDown rounded width)
open Qatlib.Concepts.ResourceBounds.AsymBounds (selfDelimitBits)
open Qatlib.Concepts.ResourceBounds.AsymBounds (SparseAccessData sparseValueOracle)

structure DyadicWeights where

  num : List ℕ

  bits : ℕ
  deriving DecidableEq, Repr

def DyadicWeights.decodeQ (w : DyadicWeights) (j : Fin w.num.length) : ℚ :=
  (w.num.get j : ℚ) / (2:ℚ) ^ w.bits

def DyadicWeights.decode (w : DyadicWeights) (j : Fin w.num.length) : ℝ :=
  ((w.decodeQ j : ℚ) : ℝ)

def coeffDomainCheck (w : DyadicWeights) (γ κ : ℚ) : Bool :=
  (decide (0 < γ)) && (decide (0 < κ)) && (decide (w.num.sum = 2 ^ w.bits)) &&
    (w.num.all fun z => decide (z = 0) || decide (γ ≤ (z:ℚ) / 2 ^ w.bits)) &&
    (w.num.all fun z => decide ((z:ℚ) / 2 ^ w.bits ≤ κ * γ))

structure CoeffPremises (w : DyadicWeights) (γ κ : ℚ) : Prop where

  gap_pos : 0 < γ

  cond_pos : 0 < κ

  normalized : w.num.sum = 2 ^ w.bits

  normalizedReal : ∑ j : Fin w.num.length, w.decode j = 1

  gap : ∀ j : Fin w.num.length, w.decode j = 0 ∨ (γ : ℝ) ≤ w.decode j

  conditioned : ∀ j : Fin w.num.length, w.decode j ≤ (κ : ℝ) * γ

def zeroWeights (m bits : ℕ) : DyadicWeights :=
  ⟨List.replicate m 0, bits⟩

def unitWeights (m bits i : ℕ) : DyadicWeights :=
  ⟨List.replicate i 0 ++ [2 ^ bits] ++ List.replicate (m - i) 0, bits⟩

def equalWeights (m bits : ℕ) : DyadicWeights :=
  ⟨List.replicate m (2 ^ bits / m), bits⟩

structure DyadicComplex where

  reNum : ℤ

  imNum : ℤ

  bits : ℕ
  deriving DecidableEq, Repr

noncomputable def DyadicComplex.decode (c : DyadicComplex) : ℂ :=
  ((c.reNum : ℚ) / (2:ℚ) ^ c.bits : ℂ) + Complex.I * ((c.imNum : ℚ) / (2:ℚ) ^ c.bits : ℂ)

structure DyadicAngle where

  num : ℕ

  k : ℕ
  deriving DecidableEq, Repr

def DyadicAngle.decodeQ (a : DyadicAngle) : ℚ := (a.num : ℚ) / (2:ℚ) ^ a.k

def DyadicAngle.decode (a : DyadicAngle) : ℝ := ((a.decodeQ : ℚ) : ℝ)

def admitAngle (num k : ℕ) : Option DyadicAngle :=
  if num < 2 ^ k then some ⟨num, k⟩ else none

def evalAngle (a : DyadicAngle) (p : ℕ) : Interval :=
  rounded a.decodeQ p

def invAngle (a : DyadicAngle) : DyadicAngle := ⟨2 ^ a.k - a.num, a.k⟩

def evalAngleCost (a : DyadicAngle) (p : ℕ) : ℕ :=
  (selfDelimitBits a.num ++ selfDelimitBits a.k).length + a.k + p

def selfDelimitReadCost (n : ℕ) : ℕ := (selfDelimitBits n).length

noncomputable def fiberDist {m : ℕ} (a b : QState (Fin m)) : ℝ := dist a b

noncomputable def errorBudget (L : ℕ) (δ : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range L, Real.sqrt (δ i)

noncomputable def prepareTarget (w : DyadicWeights) : QState (Fin w.num.length) :=
  fun j => ((Real.sqrt (w.decode j) : ℝ) : ℂ)

def IsPrepareC {J : Type*} [Fintype J] [DecidableEq J] (P : Matrix J J ℂ) (c : J → ℂ)
    (j₀ : J) : Prop :=
  P ∈ Matrix.unitaryGroup J ℂ ∧ P *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = c

def ThresholdFiniteDigitCore : Prop :=
  ∀ (w : DyadicWeights) (γ κ : ℚ), coeffDomainCheck w γ κ = false ∨ CoeffPremises w γ κ

def ThresholdPhaseInverseCore : Prop :=
  (∀ num k, admitAngle num k = none ↔ 2 ^ k ≤ num) ∧
    (∀ (a : DyadicAngle) (p : ℕ),
      Valid (evalAngle a p) ∧ Contains (evalAngle a p) a.decode ∧ width (evalAngle a p) = unit p) ∧
    (∀ (a : DyadicAngle) (p : ℕ),
      (selfDelimitBits a.num ++ selfDelimitBits a.k).length ≤ evalAngleCost a p) ∧
    (∀ (a : DyadicAngle), a.num < 2 ^ a.k →
      DyadicAngle.decodeQ (invAngle a) = 1 - DyadicAngle.decodeQ a)

def ThresholdPrepareTransport : Prop :=
  (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y|) ∧
    (∀ (m : ℕ) (a b : QState (Fin m)) (d : ℝ), 0 ≤ d →
      (∀ j, ‖a j - b j‖ ≤ Real.sqrt d) → fiberDist a b ≤ Real.sqrt d) ∧
    (∀ (m L : ℕ) (f : ℕ → QState (Fin m)) (δ : ℕ → ℝ),
      (∀ i, fiberDist (f (i + 1)) (f i) ≤ Real.sqrt (δ i)) →
      fiberDist (f L) (f 0) ≤ errorBudget L δ)

def ThresholdUnitPrepareConsumer : Prop :=
  (∀ (J : Type) [Fintype J] [DecidableEq J] (j₀ : J),
      IsPrepare (1 : Matrix J J ℂ) (fun j => if j = j₀ then (1:ℝ) else 0) j₀) ∧
    (∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (U : J → Matrix I I ℂ) (j₀ : J) (ψ : QState I),
      (fun i' => (LCUWorkspace U (1 : Matrix J J ℂ) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) ψ) (j₀, i'))
        = U j₀ *ᵥ ψ)

def ThresholdComplexPrepareResidual : Prop :=
  (∀ (w : DyadicWeights) (γ κ : ℚ), coeffDomainCheck w γ κ = true →
    (hlen : 0 < w.num.length) →
    ∃ P : Matrix (Fin w.num.length) (Fin w.num.length) ℂ,
      IsPrepare P (fun j => w.decode j) ⟨0, hlen⟩) ∧
    (∀ (n : ℕ) (t : Reg n → DyadicComplex) (p : ℕ),
      ∃ gs : List (LocalQFTGate n),
        gs.length ≤ 2 ^ p * (n + 1) ∧
        dist (localProgramMatrix gs *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) : QState (Reg n)))
          (fun x => (t x).decode) ≤ 1 / (2:ℝ) ^ p) ∧
    (∀ (N b : ℕ) (d : SparseAccessData N b) (ε : ℝ), 0 < ε →
      ∃ C : Circuit (Fin N × Bool),
        QueryCount C ≤ 2 ∧
        ∀ ψ : QState (Fin N × Bool),
          dist (Run 1 C ψ) (sparseValueOracle d *ᵥ ψ) ≤ ε) ∧
    (∀ (a : DyadicAngle) (p : ℕ),
      ∃ cost : ℕ, evalAngleCost a p ≤ cost ∧ cost ≤ (a.k + p + 3) ^ 2)

def ThresholdClaim : Prop :=
  ThresholdFiniteDigitCore ∧ ThresholdPhaseInverseCore ∧ ThresholdPrepareTransport ∧
    ThresholdUnitPrepareConsumer ∧ ThresholdComplexPrepareResidual

abbrev RegId := ℕ

inductive OracleCap where
  | forward
  | controlled
  | inverse
  deriving DecidableEq, Repr

inductive MemEvent where

  | alloc (r : RegId) (sz : ℕ)

  | uncompute (r : RegId)

  | release (r : RegId)

  | address (r : RegId)

  | read (r : RegId) (addr : ℕ)

  | write (r : RegId) (addr : ℕ)

  | output (r : RegId)

  | persist (r : RegId) (sz : ℕ)

  | oracle (cap : OracleCap)

  | approx (ε : ℚ)
  deriving DecidableEq, Repr

structure MemState where

  sizes : RegId → ℕ

  liveSet : Finset RegId

  persistent : ℕ

def initMem : MemState := ⟨fun _ => 0, ∅, 0⟩

def MemState.live (s : MemState) : ℕ := s.persistent + ∑ r ∈ s.liveSet, s.sizes r

def step (s : MemState) : MemEvent → MemState
  | .alloc r sz => ⟨Function.update s.sizes r sz, insert r s.liveSet, s.persistent⟩
  | .uncompute _ => s
  | .release r => ⟨s.sizes, s.liveSet.erase r, s.persistent⟩
  | .address _ => s
  | .read _ _ => s
  | .write _ _ => s
  | .output _ => s
  | .persist _ sz => ⟨s.sizes, s.liveSet, s.persistent + sz⟩
  | .oracle _ => s
  | .approx _ => s

def runMem (s : MemState) : List MemEvent → MemState :=
  List.foldl step s

def peak (s : MemState) : List MemEvent → ℕ
  | [] => s.live
  | e :: es => max s.live (peak (step s e) es)

def MemEvent.oracleClass : MemEvent → Option OracleCap
  | .oracle cap => some cap
  | _ => none

def countCap (cap : OracleCap) : List MemEvent → ℕ
  | [] => 0
  | e :: es => (if e.oracleClass = some cap then 1 else 0) + countCap cap es

structure PaidQueries where

  forward : ℕ

  controlled : ℕ

  inverse : ℕ
  deriving DecidableEq, Repr

def PaidQueries.covers (p u : PaidQueries) : Prop :=
  u.forward ≤ p.forward ∧ u.controlled ≤ p.controlled ∧ u.inverse ≤ p.inverse

def usage (es : List MemEvent) : PaidQueries :=
  ⟨countCap .forward es, countCap .controlled es, countCap .inverse es⟩

def errOf : List MemEvent → ℚ
  | [] => 0
  | .approx ε :: es => ε + errOf es
  | _ :: es => errOf es

def eventTime : MemEvent → ℕ
  | .alloc _ sz => 1 + sz
  | .uncompute _ => 1
  | .release _ => 1
  | .address _ => 1
  | .read _ _ => 1
  | .write _ _ => 1
  | .output _ => 1
  | .persist _ sz => 1 + sz
  | .oracle _ => 1
  | .approx _ => 1

structure Resources where

  time : ℕ

  peakSpace : ℕ

  addresses : ℕ

  reads : ℕ

  writes : ℕ

  outputs : ℕ

  forward : ℕ

  controlled : ℕ

  inverse : ℕ
  deriving DecidableEq, Repr

def countEvent (p : MemEvent → Bool) : List MemEvent → ℕ
  | [] => 0
  | e :: es => (if p e then 1 else 0) + countEvent p es

def account (s : MemState) (es : List MemEvent) : Resources where
  time := (es.map eventTime).sum
  peakSpace := peak s es
  addresses := countEvent (fun e => if e matches .address _ then true else false) es
  reads := countEvent (fun e => if e matches .read _ _ then true else false) es
  writes := countEvent (fun e => if e matches .write _ _ then true else false) es
  outputs := countEvent (fun e => if e matches .output _ then true else false) es
  forward := countCap .forward es
  controlled := countCap .controlled es
  inverse := countCap .inverse es

structure ImplRun where

  init : MemState

  events : List MemEvent

  err : ℚ

  err_le : err ≤ errOf events

def ImplRun.state (r : ImplRun) : MemState := runMem r.init r.events

def ImplRun.peak (r : ImplRun) : ℕ :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.peak r.init r.events

def ImplRun.resources (r : ImplRun) : Resources := account r.init r.events

def readEntry (r : RegId) (b : ℕ) : List MemEvent :=
  (List.range b).map fun i => .read r i

def Clause11MemoryCore : Prop :=
  (∀ (s : MemState) (a b : List MemEvent), runMem s (a ++ b) = runMem (runMem s a) b) ∧
    (∀ (s : MemState) (a b : List MemEvent),
      peak s (a ++ b) = max (peak s a) (peak (runMem s a) b)) ∧
    (∀ (s : MemState) (r : RegId) (sz : ℕ), r ∉ s.liveSet →
      (step s (.alloc r sz)).live = s.live + sz) ∧
    (∀ (s : MemState) (r : RegId), r ∈ s.liveSet →
      (step s (.release r)).live = s.live - s.sizes r) ∧
    (∀ (s : MemState) (r : RegId), (step s (.uncompute r)).live = s.live) ∧
    (∀ (s : MemState) (es : List MemEvent), s.live ≤ peak s es ∧ (runMem s es).live ≤ peak s es)

def Clause11OraclePayment : Prop :=
  (∀ (p u : PaidQueries), p.covers u → u.controlled ≤ p.controlled) ∧
    (∀ (q : ℕ), ¬((⟨q, 0, 0⟩ : PaidQueries).covers ⟨0, 1, 0⟩)) ∧
    (∀ (es : List MemEvent) (p : PaidQueries), p.covers (usage es) →
      countCap .controlled es ≤ p.controlled ∧ countCap .inverse es ≤ p.inverse) ∧
    (∀ (cap : OracleCap) (a b : List MemEvent),
      countCap cap (a ++ b) = countCap cap a + countCap cap b)

def Clause11OneRunBinding : Prop :=
  (∀ (a b : List MemEvent), errOf (a ++ b) = errOf a + errOf b) ∧
    (∀ (s : MemState) (a b : List MemEvent),
      (account s (a ++ b)).time = (account s a).time + (account (runMem s a) b).time) ∧
    (∀ (r r' : ImplRun), r.init = r'.init → r.events = r'.events →
      r.state = r'.state ∧ r.peak = r'.peak ∧ r.resources = r'.resources) ∧
    (∀ (r : RegId) (b : ℕ), (List.range b).length = countEvent
      (fun e => if e matches .read _ _ then true else false) (readEntry r b))

def Clause11GenerationResidual : Prop :=
  (∃ (q C D : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
    0 < C ∧ 1 ≤ D ∧
    ∀ (a b : ℕ),
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))),
        s ≤ C * (1 + (selfDelimitBits a ++ selfDelimitBits b).length + a + b) ^ D ∧
        BitMachineAfter M ((selfDelimitBits a ++ selfDelimitBits b).map some) s = some cfg ∧
        Turing.TM0.step M cfg = none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i =
          ((selfDelimitBits (Nat.gcd a b)).map some).getD i none)) ∧
    (∀ (n p : ℕ),
      ∃ es : List MemEvent,
        countEvent (fun e => if e matches .read _ _ then true else false) es = n * n * p ∧
        countEvent (fun e => if e matches .write _ _ then true else false) es = n * n * p ∧
        (account initMem es).time ≤ 4 * n * n * p ∧
        (account initMem es).peakSpace ≤ 2 * n * p + n)

def Clause11Claim : Prop :=
  Clause11MemoryCore ∧ Clause11OraclePayment ∧ Clause11OneRunBinding ∧ Clause11GenerationResidual

end Qatlib.Concepts.AdversaryBounds.AdvDuality
