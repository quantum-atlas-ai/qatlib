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

/-!
# Dyadic Encodings and Implementation Contracts

This file defines finite dyadic coefficient and angle encodings, their decodings, and the
contracts used to connect coefficient checks to unitary state preparation. `DyadicWeights`,
`CoeffPremises`, and `IsPrepareC` separate finite numerical data from normalization and
preparation requirements. The unitary and controlled-operation terminology follows the standard
quantum circuit framework of [NielsenChuang2010].

`MemEvent` and `MemState` give an explicit event-based model for live memory, persistent memory,
access counts, and separately charged oracle capabilities. `ThresholdClaim` and `Clause11Claim`
package requirements as propositions, including the additional preparation, approximation, and
generation conditions stated by `ThresholdComplexPrepareResidual` and
`Clause11GenerationResidual`.

## Main statements

* `coeffDomainCheck` checks normalization, coefficient gaps, and conditioning bounds on finite
  dyadic data.
- `ThresholdClaim` groups the coefficient, phase, and preparation contracts.
* `account` computes time, peak memory, access counts, and oracle-capability counts from a
  trace.
- `Clause11Claim` groups the memory, oracle-payment, run-binding, and generation contracts.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010], Quantum Computation and Quantum Information.
-/

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

/-- A finite list of natural numerators sharing the denominator `2 ^ bits`. Normalization is
imposed separately. -/
structure DyadicWeights where

  num : List ℕ

  bits : ℕ
  deriving DecidableEq, Repr

/-- Decode a numerator of a dyadic weight list as a rational with denominator `2 ^ bits`. -/
def DyadicWeights.decodeQ (w : DyadicWeights) (j : Fin w.num.length) : ℚ :=
  (w.num.get j : ℚ) / (2:ℚ) ^ w.bits

/-- Decode a dyadic weight as a real number by casting its rational value. -/
def DyadicWeights.decode (w : DyadicWeights) (j : Fin w.num.length) : ℝ :=
  ((w.decodeQ j : ℚ) : ℝ)

/-- Check positivity of the gap and conditioning parameters, integer normalization, a gap for
nonzero weights, and the upper bound `κ * γ`. -/
def coeffDomainCheck (w : DyadicWeights) (γ κ : ℚ) : Bool :=
  (decide (0 < γ)) && (decide (0 < κ)) && (decide (w.num.sum = 2 ^ w.bits)) &&
    (w.num.all fun z => decide (z = 0) || decide (γ ≤ (z:ℚ) / 2 ^ w.bits)) &&
    (w.num.all fun z => decide ((z:ℚ) / 2 ^ w.bits ≤ κ * γ))

/-- Positivity, normalization, gap, and conditioning premises for dyadic weights, including both
integer and real normalization. -/
structure CoeffPremises (w : DyadicWeights) (γ κ : ℚ) : Prop where

  gap_pos : 0 < γ

  cond_pos : 0 < κ

  normalized : w.num.sum = 2 ^ w.bits

  normalizedReal : ∑ j : Fin w.num.length, w.decode j = 1

  gap : ∀ j : Fin w.num.length, w.decode j = 0 ∨ (γ : ℝ) ≤ w.decode j

  conditioned : ∀ j : Fin w.num.length, w.decode j ≤ (κ : ℝ) * γ

/-- Construct `m` zero numerators with the specified dyadic denominator exponent. -/
def zeroWeights (m bits : ℕ) : DyadicWeights :=
  ⟨List.replicate m 0, bits⟩

/-- Construct a full-mass numerator `2 ^ bits` preceded by `i` zeros and followed by `m - i`
zeros. -/
def unitWeights (m bits i : ℕ) : DyadicWeights :=
  ⟨List.replicate i 0 ++ [2 ^ bits] ++ List.replicate (m - i) 0, bits⟩

/-- Construct `m` equal numerators using the natural-number quotient `2 ^ bits / m`. -/
def equalWeights (m bits : ℕ) : DyadicWeights :=
  ⟨List.replicate m (2 ^ bits / m), bits⟩

/-- A complex dyadic encoding with signed real and imaginary numerators and a shared
power-of-two denominator. -/
structure DyadicComplex where

  reNum : ℤ

  imNum : ℤ

  bits : ℕ
  deriving DecidableEq, Repr

/-- Decode the signed dyadic real and imaginary components as a complex number. -/
noncomputable def DyadicComplex.decode (c : DyadicComplex) : ℂ :=
  ((c.reNum : ℚ) / (2:ℚ) ^ c.bits : ℂ) + Complex.I * ((c.imNum : ℚ) / (2:ℚ) ^ c.bits : ℂ)

/-- A dyadic angle encoding consisting of a natural numerator and a denominator exponent. The
structure itself imposes no range condition. -/
structure DyadicAngle where

  num : ℕ

  k : ℕ
  deriving DecidableEq, Repr

/-- Decode a dyadic angle as the rational `num / 2 ^ k`. -/
def DyadicAngle.decodeQ (a : DyadicAngle) : ℚ := (a.num : ℚ) / (2:ℚ) ^ a.k

/-- Decode a dyadic angle as a real number by casting its rational value. -/
def DyadicAngle.decode (a : DyadicAngle) : ℝ := ((a.decodeQ : ℚ) : ℝ)

/-- Return the dyadic encoding when `num < 2 ^ k`, and return `none` otherwise. -/
def admitAngle (num k : ℕ) : Option DyadicAngle :=
  if num < 2 ^ k then some ⟨num, k⟩ else none

/-- Enclose the rational decoding of an angle in the interval obtained by dyadic rounding at
precision `p`. -/
def evalAngle (a : DyadicAngle) (p : ℕ) : Interval :=
  rounded a.decodeQ p

/-- Construct the complementary angle encoding by replacing the numerator with the natural
subtraction `2 ^ k - num`. -/
def invAngle (a : DyadicAngle) : DyadicAngle := ⟨2 ^ a.k - a.num, a.k⟩

/-- Charge the lengths of the self-delimiting numerator and exponent encodings, plus the
exponent and requested precision. -/
def evalAngleCost (a : DyadicAngle) (p : ℕ) : ℕ :=
  (selfDelimitBits a.num ++ selfDelimitBits a.k).length + a.k + p

/-- The number of bits in the self-delimiting encoding of a natural number. -/
def selfDelimitReadCost (n : ℕ) : ℕ := (selfDelimitBits n).length

/-- The finite-product supremum distance between two complex state vectors. -/
noncomputable def fiberDist {m : ℕ} (a b : QState (Fin m)) : ℝ := dist a b

/-- The sum of `sqrt (δ i)` over the first `L` indices, used to accumulate successive distance
bounds. -/
noncomputable def errorBudget (L : ℕ) (δ : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range L, Real.sqrt (δ i)

/-- The state vector whose amplitudes are the nonnegative square roots of the decoded dyadic
weights. -/
noncomputable def prepareTarget (w : DyadicWeights) : QState (Fin w.num.length) :=
  fun j => ((Real.sqrt (w.decode j) : ℝ) : ℂ)

/-- The proposition that a unitary matrix maps the chosen basis vector to the specified complex
amplitude vector. -/
def IsPrepareC {J : Type*} [Fintype J] [DecidableEq J] (P : Matrix J J ℂ) (c : J → ℂ)
    (j₀ : J) : Prop :=
  P ∈ Matrix.unitaryGroup J ℂ ∧ P *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = c

/-- The contract that the coefficient-domain checker either rejects its input or yields all
coefficient premises. -/
def ThresholdFiniteDigitCore : Prop :=
  ∀ (w : DyadicWeights) (γ κ : ℚ), coeffDomainCheck w γ κ = false ∨ CoeffPremises w γ κ

/-- The conjunction of angle-range rejection, sound interval evaluation, input-reading cost
coverage, and complementary-angle decoding requirements. -/
def ThresholdPhaseInverseCore : Prop :=
  (∀ num k, admitAngle num k = none ↔ 2 ^ k ≤ num) ∧
    (∀ (a : DyadicAngle) (p : ℕ),
      Valid (evalAngle a p) ∧ Contains (evalAngle a p) a.decode ∧ width (evalAngle a p) = unit p) ∧
    (∀ (a : DyadicAngle) (p : ℕ),
      (selfDelimitBits a.num ++ selfDelimitBits a.k).length ≤ evalAngleCost a p) ∧
    (∀ (a : DyadicAngle), a.num < 2 ^ a.k →
      DyadicAngle.decodeQ (invAngle a) = 1 - DyadicAngle.decodeQ a)

/-- The contract combining square-root stability, transport of coordinatewise errors to supremum
distance, and accumulation of successive distances. -/
def ThresholdPrepareTransport : Prop :=
  (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y|) ∧
    (∀ (m : ℕ) (a b : QState (Fin m)) (d : ℝ), 0 ≤ d →
      (∀ j, ‖a j - b j‖ ≤ Real.sqrt d) → fiberDist a b ≤ Real.sqrt d) ∧
    (∀ (m L : ℕ) (f : ℕ → QState (Fin m)) (δ : ℕ → ℝ),
      (∀ i, fiberDist (f (i + 1)) (f i) ≤ Real.sqrt (δ i)) →
      fiberDist (f L) (f 0) ≤ errorBudget L δ)

/-- The contract that identity preparation realizes a single-label weight distribution and that
its selected LCU corner applies the selected matrix. -/
def ThresholdUnitPrepareConsumer : Prop :=
  (∀ (J : Type) [Fintype J] [DecidableEq J] (j₀ : J),
      IsPrepare (1 : Matrix J J ℂ) (fun j => if j = j₀ then (1:ℝ) else 0) j₀) ∧
    (∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (U : J → Matrix I I ℂ) (j₀ : J) (ψ : QState I),
      (fun i' => (LCUWorkspace U (1 : Matrix J J ℂ) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) ψ) (j₀, i'))
        = U j₀ *ᵥ ψ)

/-- The contract requiring preparation of accepted dyadic weights, local-gate approximation of
complex targets, sparse-value-oracle simulation, and a quadratic angle-evaluation cost
bound. -/
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

/-- The conjunction of the finite-digit, phase-inverse, preparation-error transport,
unit-preparation consumer, and complex-preparation contracts. -/
def ThresholdClaim : Prop :=
  ThresholdFiniteDigitCore ∧ ThresholdPhaseInverseCore ∧ ThresholdPrepareTransport ∧
    ThresholdUnitPrepareConsumer ∧ ThresholdComplexPrepareResidual

/-- Natural-number identifiers for registers in a memory-event trace. -/
abbrev RegId := ℕ

/-- The three separately accounted oracle capabilities: forward, controlled, and inverse access. -/
inductive OracleCap where
  | forward
  | controlled
  | inverse
  deriving DecidableEq, Repr

/-- Events for register allocation, uncomputation, release, addressing, reading, writing,
output, persistence, oracle access, and rational approximation-error recording. -/
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

/-- A memory-accounting state containing register sizes, the finite set of live registers, and a
persistent-memory count. -/
structure MemState where

  sizes : RegId → ℕ

  liveSet : Finset RegId

  persistent : ℕ

/-- The empty memory state, with zero register sizes, no live registers, and no persistent
memory. -/
def initMem : MemState := ⟨fun _ => 0, ∅, 0⟩

/-- The persistent-memory count plus the sizes of all currently live registers. -/
def MemState.live (s : MemState) : ℕ := s.persistent + ∑ r ∈ s.liveSet, s.sizes r

/-- Update the memory state for one event: allocation changes a register size and live set,
release removes a live identifier, and persistence increases the persistent count. -/
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

/-- Execute a list of memory events by folding the single-event transition from the initial
state. -/
def runMem (s : MemState) : List MemEvent → MemState :=
  List.foldl step s

/-- The maximum live-memory count over the initial state and every successive state in a
memory-event trace. -/
def peak (s : MemState) : List MemEvent → ℕ
  | [] => s.live
  | e :: es => max s.live (peak (step s e) es)

/-- Extract the capability of an oracle event, returning `none` for every other event. -/
def MemEvent.oracleClass : MemEvent → Option OracleCap
  | .oracle cap => some cap
  | _ => none

/-- Count oracle events with the specified capability in a trace. -/
def countCap (cap : OracleCap) : List MemEvent → ℕ
  | [] => 0
  | e :: es => (if e.oracleClass = some cap then 1 else 0) + countCap cap es

/-- Separate natural-number budgets for forward, controlled, and inverse oracle queries. -/
structure PaidQueries where

  forward : ℕ

  controlled : ℕ

  inverse : ℕ
  deriving DecidableEq, Repr

/-- Componentwise comparison stating that each query-usage count is bounded by the corresponding
paid budget. -/
def PaidQueries.covers (p u : PaidQueries) : Prop :=
  u.forward ≤ p.forward ∧ u.controlled ≤ p.controlled ∧ u.inverse ≤ p.inverse

/-- Collect the forward, controlled, and inverse oracle-event counts of a trace. -/
def usage (es : List MemEvent) : PaidQueries :=
  ⟨countCap .forward es, countCap .controlled es, countCap .inverse es⟩

/-- Sum the rational values recorded by approximation events, ignoring all other events. -/
def errOf : List MemEvent → ℚ
  | [] => 0
  | .approx ε :: es => ε + errOf es
  | _ :: es => errOf es

/-- The time charge for one event: one plus its size for allocation or persistence, and one for
every other event. -/
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

/-- Resource totals for time, peak space, address/read/write/output events, and the three oracle
capabilities. -/
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

/-- Count the events in a trace for which the given Boolean predicate is true. -/
def countEvent (p : MemEvent → Bool) : List MemEvent → ℕ
  | [] => 0
  | e :: es => (if p e then 1 else 0) + countEvent p es

/-- Compute total time, peak live memory, access-event counts, and separate oracle-capability
counts for a trace from an initial memory state. -/
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

/-- An implementation run consisting of an initial memory state, an event trace, and a rational
error value bounded above by the sum of recorded errors. -/
structure ImplRun where

  init : MemState

  events : List MemEvent

  err : ℚ

  err_le : err ≤ errOf events

/-- The final memory state obtained by executing an implementation run's events from its initial
state. -/
def ImplRun.state (r : ImplRun) : MemState := runMem r.init r.events

/-- The peak live-memory count along an implementation run. -/
def ImplRun.peak (r : ImplRun) : ℕ :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.peak r.init r.events

/-- The resource totals obtained by accounting for an implementation run's initial state and
event trace. -/
def ImplRun.resources (r : ImplRun) : Resources := account r.init r.events

/-- The trace of read events for the first `b` addresses in a register, starting at zero. -/
def readEntry (r : RegId) (b : ℕ) : List MemEvent :=
  (List.range b).map fun i => .read r i

/-- The conjunction of trace-composition laws, allocation and release formulas, uncompute
invariance, and bounds on endpoint memory by peak usage. -/
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

/-- The contract enforcing separate controlled and inverse query budgets, excluding payment of
controlled queries by forward-only budgets, and requiring additivity of capability counts. -/
def Clause11OraclePayment : Prop :=
  (∀ (p u : PaidQueries), p.covers u → u.controlled ≤ p.controlled) ∧
    (∀ (q : ℕ), ¬((⟨q, 0, 0⟩ : PaidQueries).covers ⟨0, 1, 0⟩)) ∧
    (∀ (es : List MemEvent) (p : PaidQueries), p.covers (usage es) →
      countCap .controlled es ≤ p.controlled ∧ countCap .inverse es ≤ p.inverse) ∧
    (∀ (cap : OracleCap) (a b : List MemEvent),
      countCap cap (a ++ b) = countCap cap a + countCap cap b)

/-- The conjunction of error and time additivity, resource determinacy from the initial state
and trace, and the entry-read count law. -/
def Clause11OneRunBinding : Prop :=
  (∀ (a b : List MemEvent), errOf (a ++ b) = errOf a + errOf b) ∧
    (∀ (s : MemState) (a b : List MemEvent),
      (account s (a ++ b)).time = (account s a).time + (account (runMem s a) b).time) ∧
    (∀ (r r' : ImplRun), r.init = r'.init → r.events = r'.events →
      r.state = r'.state ∧ r.peak = r'.peak ∧ r.resources = r'.resources) ∧
    (∀ (r : RegId) (b : ℕ), (List.range b).length = countEvent
      (fun e => if e matches .read _ _ then true else false) (readEntry r b))

/-- The contract requiring a halting binary GCD machine with the stated polynomial bound in
encoded length and input values, together with traces satisfying prescribed read/write
counts and time/space bounds. -/
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

/-- The conjunction of the memory, oracle-payment, single-run binding, and generation contracts. -/
def Clause11Claim : Prop :=
  Clause11MemoryCore ∧ Clause11OraclePayment ∧ Clause11OneRunBinding ∧ Clause11GenerationResidual

end Qatlib.Concepts.AdversaryBounds.AdvDuality
