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

/-!
# Actual sieve records and decorated skeletons

This module defines record distributions obtained from actual dihedral measurements,
probabilistic combining layers, ideal-hit events, and optional bit-list descent.
`RepTransportWitness` packages the representation-label mass identities, marginal laws, and
qubit factorization used to connect those measurements to the representation description of
[Kuperberg2005].

Decorated labels track supports and top-bit offsets through a sieve skeleton. Their shadows
retain low parts, supports, and offsets while discarding the top-bit inputs.

## Main statements

* `actualCombinedRun`: the law of fresh actual records followed by combining layers.
* `RepTransportTarget`: the representation transport specification.
* `descentStage`: one optional bit-learning stage.
* `DecLabel` and `DecShadow`: decorated labels and their low-part shadows.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- A sieve record consisting of a label in `ZMod N` and a natural-number width. -/
structure ActualHalfWidthRecord (N : ℕ) where

  label : ZMod N

  width : ℕ
  deriving DecidableEq

/-- The law of one actual measured record after retaining its label and assigning the fixed
width `w`. -/
noncomputable def actualFreshRecord {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w : ℕ) : PMF (ActualHalfWidthRecord N) :=
  (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => ⟨q.1, w⟩)

/-- The law of a list of independently sampled fresh actual records, each with width `w`. -/
noncomputable def actualHalfWidthRecords {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w : ℕ) : ℕ → PMF (List (ActualHalfWidthRecord N))
  | 0 => pure []
  | i + 1 =>
    (actualFreshRecord f w).bind fun r =>
      (actualHalfWidthRecords f w i).map fun L =>
        r :: L

/-- The label marginal of the actual finite record measurement law. -/
noncomputable def actualLabelLaw {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) :
    PMF (ZMod N) :=
  (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => q.1)

/-- The law of `i` fresh actual records with common width `w`. -/
noncomputable def actualHalfWidthRecordLaw {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w : ℕ) (i : ℕ) : PMF (List (ActualHalfWidthRecord N)) :=
  actualHalfWidthRecords f w i

/-- Combine records by subtracting their labels and taking the natural-number quotient of their
summed widths by `a`. -/
def combineActualRecords {N : ℕ} (a : ℕ) (r₁ r₂ : ActualHalfWidthRecord N) :
    ActualHalfWidthRecord N :=
  ⟨r₁.label - r₂.label, (r₁.width + r₂.width) / a⟩

/-- Independently retain each pair's combined child with probability one half, preserving the
order of retained children. -/
noncomputable def actualLayerCombineLaw {N : ℕ} (a : ℕ) :
    List (ActualHalfWidthRecord N × ActualHalfWidthRecord N) →
      PMF (List (ActualHalfWidthRecord N))
  | [] => pure []
  | (r₁, r₂) :: ps =>
    (PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (actualLayerCombineLaw a ps).map fun tail =>
        if b = 1 then combineActualRecords a r₁ r₂ :: tail else tail

/-- Pair records using modular window agreement and apply the probabilistic child-retention law
to those pairs. -/
noncomputable def actualLayerCombine {N : ℕ} (a q : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    PMF (List (ActualHalfWidthRecord N)) :=
  actualLayerCombineLaw a
    (pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L)

/-- Iterate the actual combining layer a specified number of times, starting from the given
record list. -/
noncomputable def actualLayeredCombine {N : ℕ} (a q : ℕ) :
    ℕ → List (ActualHalfWidthRecord N) → PMF (List (ActualHalfWidthRecord N))
  | 0, L => pure L
  | j + 1, L => (actualLayeredCombine a q j L).bind (actualLayerCombine a q)

/-- Sample `L0` fresh actual records and perform `m` combining layers with parameters `a` and
`q`. -/
noncomputable def actualCombinedRun {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    PMF (List (ActualHalfWidthRecord N)) :=
  (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q m)

/-- The distinguished label is `N / 2` for even `N` and zero for odd `N`. -/
def actualIdealLabel (N : ℕ) : ZMod N :=
  if N % 2 = 0 then ((N / 2 : ℕ) : ZMod N) else (0 : ZMod N)

/-- An actual record is an ideal hit when its label equals `actualIdealLabel`. -/
def isActualIdealHit {N : ℕ} (r : ActualHalfWidthRecord N) : Prop :=
  r.label = actualIdealLabel N

/-- A record list contains an ideal hit when one of its members satisfies `isActualIdealHit`. -/
def hasIdealHit {N : ℕ} (L : List (ActualHalfWidthRecord N)) : Prop :=
  ∃ r ∈ L, isActualIdealHit r

/-- The Boolean law recording whether the final actual record list contains an ideal hit. -/
noncomputable def actualIdealHitEvent {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    PMF Bool :=
  (actualCombinedRun f a q w L0 m).map
    (fun L => decide (hasIdealHit L))

/-- The probability that the actual combining run produces a list containing an ideal hit. -/
noncomputable def actualIdealHitMass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    ℝ≥0∞ :=
  actualIdealHitEvent f a q w L0 m true

/-- One minus the ideal-hit mass of the actual combining run, in the extended nonnegative reals. -/
noncomputable def actualFailureMass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    ℝ≥0∞ :=
  1 - actualIdealHitMass f a q w L0 m

/-- The extended nonnegative real indicator of a proposition, equal to one when it holds and
zero otherwise. -/
def massIndicator (p : Prop) : ℝ≥0∞ := if p then 1 else 0

/-- The indicator that a record list contains no ideal hit. -/
noncomputable def idealMissWeight {N : ℕ} (L : List (ActualHalfWidthRecord N)) :
    ℝ≥0∞ :=
  massIndicator (¬ hasIdealHit L)

/-- The total mass of fresh actual record lists containing no ideal hit. -/
noncomputable def actualMissMass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (w L0 : ℕ) :
    ℝ≥0∞ :=
  ∑' L : List (ActualHalfWidthRecord N),
    (actualHalfWidthRecords f w L0) L * idealMissWeight L

/-- The mass of a single fresh actual record missing the distinguished ideal label. -/
noncomputable def actualMissProbOne {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (w : ℕ) :
    ℝ≥0∞ :=
  ∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
    massIndicator (¬ isActualIdealHit r)

/-- The real-valued expression `1 - (1 - 1 / N) ^ L0` for at least one ideal label among uniform
independent records. -/
noncomputable def actualFreshIdealHitMass (N L0 : ℕ) : ℝ :=
  1 - (1 - 1 / (N : ℝ)) ^ L0

/-- The real-valued expression `(1 - 1 / N) ^ L0` for missing an ideal label in all uniform
independent records. -/
noncomputable def actualFreshFailureMass (N L0 : ℕ) : ℝ :=
  (1 - 1 / (N : ℝ)) ^ L0

/-- Iterate a transformation of optional bit-list laws `k` times, starting at the successful
empty list. -/
def descentFold (stage : PMF (Option (List Bool)) → PMF (Option (List Bool)))
    (k : ℕ) : PMF (Option (List Bool)) :=
  (List.range k).foldl (fun acc _ => stage acc) (PMF.pure (some ([] : List Bool)))

/-- Append a successful optional bit to the supplied list, propagating failure as `none`. -/
def extendOpt (bs : List Bool) : Option Bool → Option (List Bool)
  | none => none
  | some b => some (bs ++ [b])

/-- Push an optional bit law forward by appending its successful bit to `bs` and propagating
failure. -/
noncomputable def descentExtend (inner : PMF (Option Bool)) (bs : List Bool) :
    PMF (Option (List Bool)) :=
  inner.map (extendOpt bs)

/-- Extend a successful bit list according to its associated inner law, keeping a failed input
at `none`. -/
noncomputable def stageOpt (inner : List Bool → PMF (Option Bool)) :
    Option (List Bool) → PMF (Option (List Bool))
  | none => PMF.pure none
  | some bs => descentExtend (inner bs) bs

/-- Apply one bit-learning stage to an optional bit-list distribution by binding it to
`stageOpt`. -/
noncomputable def descentStage (inner : List Bool → PMF (Option Bool))
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  st.bind (stageOpt inner)

/-- Extend the learned bits using the ideal sieve at the remaining width and the corresponding
descent slope. -/
noncomputable def idealDescentStage (n : ℕ) (s : ZMod (2 ^ n))
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  descentStage
    (fun bs => (dihedralSieveRun (n - bs.length) (descentDepth (n - bs.length))
        (descentSlope n bs.length s)).1) st

/-- Extend the learned bits using the actual sieve oracle restricted through the corresponding
descent embedding. -/
noncomputable def actualDescentStage {n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S)
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  descentStage
    (fun bs => dihedralSieveActual (n - bs.length) (descentDepth (n - bs.length))
      (f ∘ descentEmbedding n bs)) st

/-- A witness transporting actual records to representation labels and fixed-subspace rows, with
matching masses, staged marginals, and qubit factorization. -/
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

/-- The specification that every reflection-hiding oracle has a representation transport witness
with the stated uniform marginals and one-query, one-gate record circuit. -/
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

/-- The actual record-list law after `j` combining layers from `L0` fresh records. -/
noncomputable def actualStageLaw {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (a q w L0 : ℕ) : ℕ → PMF (List (ActualHalfWidthRecord N)) :=
  fun j => (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q j)

/-- The sum of the initial record budget divided by `2 ^ j` over stages zero through `m`. -/
noncomputable def sieveKeptRecordCount (m L0 : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), L0 / 2 ^ j

/-- The representative of a label reduced modulo `2 ^ (n - 1)`. -/
def lowPart {n : ℕ} (x : ZMod (2 ^ n)) : ℕ := x.val % 2 ^ (n - 1)

/-- The quotient of a label representative by `2 ^ (n - 1)`. -/
def highPart {n : ℕ} (x : ZMod (2 ^ n)) : ℕ := x.val / 2 ^ (n - 1)

/-- The bit indicating that subtracting the low part of `x` from that of `y` requires a borrow. -/
def borrowBit {n : ℕ} (x y : ZMod (2 ^ n)) : Fin 2 :=
  if lowPart y < lowPart x then 1 else 0

/-- A label modulo `2 ^ n` decorated with a finite support of original samples and an offset in
`Fin 2`. -/
structure DecLabel (n R : ℕ) where

  val : ZMod (2 ^ n)

  sup : Finset (Fin R)

  off : Fin 2
  deriving DecidableEq

/-- A fuel-bounded greedy pairing procedure that pairs each head with the first available label
agreeing in the prescribed bit window. -/
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

/-- The shadow data of a decorated label: a natural-number low part, a finite sample support,
and a bit offset. -/
structure DecShadow (n R : ℕ) where

  low : ℕ

  sup : Finset (Fin R)

  off : Fin 2
  deriving DecidableEq

/-- Forget a decorated label's high part while retaining its low part, support, and offset. -/
def decShadow {n R : ℕ} (x : DecLabel n R) : DecShadow n R :=
  ⟨lowPart x.val, x.sup, x.off⟩

/-- Reconstruct a label modulo `2 ^ n` from a shadow's low component. -/
def shadowLabel {n R : ℕ} (s : DecShadow n R) : ZMod (2 ^ n) :=
  ((s.low % 2 ^ n : ℕ) : ZMod (2 ^ n))

/-- Form a shadow child by modular low-part subtraction, support union, and addition of parent
offsets and the borrow indicator. -/
def shChild {n R : ℕ} (p : DecShadow n R × DecShadow n R) : DecShadow n R :=
  ⟨(p.2.low + 2 ^ (n - 1) - p.1.low) % 2 ^ (n - 1),
    p.2.sup ∪ p.1.sup,
    p.2.off + p.1.off + if p.2.low < p.1.low then 1 else 0⟩

/-- Construct fresh shadow labels with the given low parts, singleton supports, and zero
offsets. -/
def shFresh {n R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1))) : List (DecShadow n R) :=
  List.ofFn fun i : Fin R => ⟨(low i).val, {i}, 0⟩

/-- Pair shadow labels by their reconstructed window keys and retain the children selected by
ones on the tape. -/
noncomputable def shTapeLayer (n m j : ℕ) {R : ℕ} (tape : List (Fin 2))
    (L : List (DecShadow n R)) : List (DecShadow n R) :=
  List.filterMap (fun p => if p.2 = 1 then some (shChild (p.1.1, p.1.2)) else none)
    ((sievePairWith n (fun s : DecShadow n R => shadowLabel s)
      (sieveWindowWidth n m j) (m * j) L).zip tape)

/-- Fold the shadow tape layers over fresh shadows to obtain the shadow sieve skeleton. -/
noncomputable def shSkel {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) : List (DecShadow n R) :=
  List.foldl (fun L j => shTapeLayer n m j.val (tape j) L) (shFresh low) (List.finRange m)

end Qatlib.Concepts.HspRecovery.OpenSieve
