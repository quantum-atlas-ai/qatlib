/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol

/-!
# Party plans and finite-message guessing

`PartyPlan` assigns owners and communication partners to finite network nodes. Local records,
EPR supplies, consumed-slot lists, and cost ledgers express locality and resource accounting,
including the split between preshared and fresh pairs in teleportation
[BennettEtAl1993Teleportation].

The module also develops complete message trees, redundant encodings, instrument reindexing, and
finite-message guessing protocols. It proves no-signalling and guessing bounds, constructs
conditional-unitary instruments, and establishes reference-system identities in the framework of
[Watrous2018].

## Main statements

* `consumedSlots_nodup` and `presharedUsed_le_available`: distinct slots and the conditional
  supply bound.
* `cost_entanglement_split`: preshared and fresh resources partition teleportation steps.
* `MessageGuessProtocol.messageCount_bound`: guessing success bounded by message count times the
  largest allowed prior weight.
* `conditionalUnitaryInstrument_reference`: preservation of the reference marginal in total.
* `qudit_correction_reference_total`: corrected teleportation sums to the identity with a
  reference.
* `counterWords_not_prefixFree`: the six-word encoding fails prefix freeness.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasurementNetworkLOCCDefs

open Matrix
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-- Party identifiers, represented by natural numbers. -/
abbrev Party := ℕ

/-- Finite sets of party identifiers. -/
abbrev PartySet := Finset ℕ

/-- Party-labelled measurement, classical-transmission, and teleportation actions, with a flag
recording preshared teleportation resources. -/
inductive PartyAction where

  | measure (owner : Party) (outcome : ℕ)

  | transmit (sender receiver : Party) (bits : List Bool)

  | teleport (owner partner : Party) (preshared : Bool)
  deriving DecidableEq

/-- The acting party of a local action, taking the sender as owner for a transmission. -/
def PartyAction.owner : PartyAction → Party
  | .measure o _ => o
  | .transmit s _ _ => s
  | .teleport o _ _ => o

/-- An assignment of parties to every node of a finite network, including communication
endpoints and whether teleportation uses a preshared pair. -/
inductive PartyPlan : {D E : ℕ} → FiniteNetwork D E → Type where
  | done {D : ℕ} : PartyPlan (.done D)
  | measure {D M E : ℕ} {s : ℕ} {I : Instrument (Fin s) D M}
      {next : Fin s → FiniteNetwork M E}
      (owner : Party) (rest : ∀ o, PartyPlan (next o)) :
      PartyPlan (.measure s I next)
  | send {D E : ℕ} {bits : List Bool} {next : FiniteNetwork D E}
      (sender : Party) (receiver : Party) (rest : PartyPlan next) :
      PartyPlan (.send bits next)
  | teleport {n E : ℕ} {hn : NeZero n} {width : ℕ} {fits : n ≤ 2 ^ width}
      {next : Fin n × Fin n → FiniteNetwork n E}
      (owner : Party) (partner : Party) (preshared : Bool)
      (rest : ∀ o, PartyPlan (next o)) :
      PartyPlan (.teleport hn width fits next)

/-- The party-labelled action list selected by a network transcript. -/
def PartyPlan.actions {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P) :
    P.Transcript → List PartyAction :=
  match pl with
  | @done _ => fun _ => []
  | @measure _ _ _ _ _ _ owner rest =>
      fun t => .measure owner t.1.val :: (rest t.1).actions t.2
  | @send _ _ bits _ sender receiver rest =>
      fun t => .transmit sender receiver bits :: rest.actions t
  | @teleport _ _ _ _ _ _ owner partner preshared rest =>
      fun t => .teleport owner partner preshared :: (rest t.1).actions t.2

/-- The finite set of parties occurring anywhere in a party plan, including all outcome
continuations. -/
def PartyPlan.actors {D E : ℕ} {P : FiniteNetwork D E} : PartyPlan P → PartySet
  | .done => ∅
  | @measure _ _ _ _ _ _ owner rest => {owner} ∪ Finset.univ.sup (fun o => (rest o).actors)
  | @send _ _ _ _ sender receiver rest => {sender, receiver} ∪ rest.actors
  | @teleport _ _ _ _ _ _ owner partner preshared rest =>
      {owner, partner} ∪ Finset.univ.sup (fun o => (rest o).actors)

/-- The transcript action list filtered to actions owned by party `p`. -/
def PartyPlan.localRecord {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (p : Party) (t : P.Transcript) : List PartyAction :=
  (pl.actions t).filter (fun a => decide (a.owner = p))

/-- Every action in `p`'s local record is owned by `p`. -/
theorem localRecord_owner {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (p : Party) (t : P.Transcript) (a : PartyAction) (ha : a ∈ pl.localRecord p t) :
    a.owner = p := by
  have ha' := (List.mem_filter.mp ha).2
  exact of_decide_eq_true ha'

/-- Every action in a local record occurs in the complete transcript action list. -/
theorem localRecord_mem {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (p : Party) (t : P.Transcript) (a : PartyAction) (ha : a ∈ pl.localRecord p t) :
    a ∈ pl.actions t :=
  (List.mem_filter.mp ha).1

/-- Every transcript action occurs in the local record of its owner. -/
theorem actions_localRecord {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (a : PartyAction) (ha : a ∈ pl.actions t) :
    a ∈ pl.localRecord a.owner t := by
  apply List.mem_filter.mpr
  constructor
  · exact ha
  · simp

/-- The number of instrument events in an event list. -/
def countInstrumentEvents : List NetworkEvent → ℕ
  | [] => 0
  | .instrument _ _ :: es => 1 + countInstrumentEvents es
  | _ :: es => countInstrumentEvents es

/-- The number of teleportation events in an event list. -/
def countTeleportEvents : List NetworkEvent → ℕ
  | [] => 0
  | .teleport _ _ _ :: es => 1 + countTeleportEvents es
  | _ :: es => countTeleportEvents es

/-- The number of transmission events in an event list. -/
def countTransmitEvents : List NetworkEvent → ℕ
  | [] => 0
  | .transmit _ :: es => 1 + countTransmitEvents es
  | _ :: es => countTransmitEvents es

/-- The number of measurement actions in a party-action list. -/
def countMeasureActions : List PartyAction → ℕ
  | [] => 0
  | .measure _ _ :: as => 1 + countMeasureActions as
  | _ :: as => countMeasureActions as

/-- The number of teleportation actions in a party-action list. -/
def countTeleportActions : List PartyAction → ℕ
  | [] => 0
  | .teleport _ _ _ :: as => 1 + countTeleportActions as
  | _ :: as => countTeleportActions as

/-- The number of transmission actions in a party-action list. -/
def countTransmitActions : List PartyAction → ℕ
  | [] => 0
  | .transmit _ _ _ :: as => 1 + countTransmitActions as
  | _ :: as => countTransmitActions as

/-- The number of teleportation actions with owner `p` and partner `q`. -/
def countPairTeleport (p q : Party) : List PartyAction → ℕ
  | [] => 0
  | .teleport o p' _ :: as =>
      (if o = p ∧ p' = q then 1 else 0) + countPairTeleport p q as
  | _ :: as => countPairTeleport p q as

/-- The number of teleportation actions from owner `p` to partner `q` marked as using a
preshared pair. -/
def countPairPreshared (p q : Party) : List PartyAction → ℕ
  | [] => 0
  | .teleport o p' presh :: as =>
      (if o = p ∧ p' = q ∧ presh = true then 1 else 0) + countPairPreshared p q as
  | _ :: as => countPairPreshared p q as

/-- The number of teleportation actions from owner `p` to partner `q` marked as using a fresh
pair. -/
def countPairFresh (p q : Party) : List PartyAction → ℕ
  | [] => 0
  | .teleport o p' presh :: as =>
      (if o = p ∧ p' = q ∧ presh = false then 1 else 0) + countPairFresh p q as
  | _ :: as => countPairFresh p q as

/-- The number of teleportation actions marked as using a preshared pair. -/
def countPresharedSteps : List PartyAction → ℕ
  | [] => 0
  | .teleport _ _ presh :: as =>
      (if presh = true then 1 else 0) + countPresharedSteps as
  | _ :: as => countPresharedSteps as

/-- The number of teleportation actions marked as using a fresh pair. -/
def countFreshSteps : List PartyAction → ℕ
  | [] => 0
  | .teleport _ _ presh :: as =>
      (if presh = false then 1 else 0) + countFreshSteps as
  | _ :: as => countFreshSteps as

/-- The number of measurement actions along a party-plan transcript. -/
def PartyPlan.measureCount {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) : ℕ :=
  countMeasureActions (pl.actions t)

/-- The number of teleportation actions along a party-plan transcript. -/
def PartyPlan.teleportCount {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) : ℕ :=
  countTeleportActions (pl.actions t)

/-- The number of transmission actions along a party-plan transcript. -/
def PartyPlan.transmitCount {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) : ℕ :=
  countTransmitActions (pl.actions t)

/-- The preshared and fresh teleportation counts sum to the total teleportation count of an
action list. -/
private theorem preshared_fresh_split (as : List PartyAction) :
    countPresharedSteps as + countFreshSteps as = countTeleportActions as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases a with
      | measure owner outcome => exact ih
      | transmit sender receiver bits => exact ih
      | teleport o p' presh =>
          cases hp : presh with
          | false =>
              rw [countPresharedSteps, countFreshSteps, countTeleportActions]
              rw [if_neg (by simp), if_pos (by simp)]
              omega
          | true =>
              rw [countPresharedSteps, countFreshSteps, countTeleportActions]
              rw [if_pos (by simp), if_neg (by simp)]
              omega

/-- For an ordered pair of parties, preshared and fresh teleportation counts sum to its total
teleportation count. -/
private theorem pair_split (p q : Party) (as : List PartyAction) :
    countPairPreshared p q as + countPairFresh p q as = countPairTeleport p q as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases a with
      | measure owner outcome => exact ih
      | transmit sender receiver bits => exact ih
      | teleport o p' presh =>
          cases hp : presh with
          | false =>
              rw [countPairPreshared, countPairFresh, countPairTeleport]
              by_cases hq : o = p ∧ p' = q
              · rw [if_neg (by simp [hq]), if_pos (by simp [hq]), if_pos (by simp [hq])]
                omega
              · rw [if_neg (by simp [hq]), if_neg (by simp [hq]), if_neg (by simp [hq])]
                omega
          | true =>
              rw [countPairPreshared, countPairFresh, countPairTeleport]
              by_cases hq : o = p ∧ p' = q
              · rw [if_pos (by simp [hq]), if_neg (by simp [hq]), if_pos (by simp [hq])]
                omega
              · rw [if_neg (by simp [hq]), if_neg (by simp [hq]), if_neg (by simp [hq])]
                omega

/-- A symmetric assignment of available EPR-pair counts to pairs of parties. -/
structure EPRSupply where

  available : ℕ → ℕ → ℕ

  symmetric : ∀ p q, available p q = available q p

/-- The preshared-resource flag of a teleportation action, returning `false` for other actions. -/
def presharedFlag : PartyAction → Bool
  | .teleport _ _ presh => presh
  | _ => false

/-- The Boolean predicate recognizing teleportation actions. -/
def isTeleportAction : PartyAction → Bool
  | .teleport _ _ _ => true
  | _ => false

/-- The Boolean predicate recognizing teleportation actions with owner `p` and partner `q`. -/
def pairTeleport (p q : Party) : PartyAction → Bool
  | .teleport o p' _ => decide (o = p ∧ p' = q)
  | _ => false

/-- The Boolean predicate recognizing preshared teleportation actions with owner `p` and partner
`q`. -/
def pairPreshared (p q : Party) : PartyAction → Bool :=
  fun a => pairTeleport p q a && presharedFlag a

/-- The Boolean predicate recognizing fresh-pair teleportation actions with owner `p` and
partner `q`. -/
def pairFresh (p q : Party) : PartyAction → Bool :=
  fun a => pairTeleport p q a && !presharedFlag a

/-- The Boolean predicate recognizing teleportation actions marked as using preshared pairs. -/
def isPresharedStep : PartyAction → Bool :=
  fun a => isTeleportAction a && presharedFlag a

/-- The Boolean predicate recognizing teleportation actions marked as using fresh pairs. -/
def isFreshStep : PartyAction → Bool :=
  fun a => isTeleportAction a && !presharedFlag a

/-- The number of preshared pairs consumed between owner `p` and partner `q` along a transcript. -/
def PartyPlan.presharedUsed {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (p q : Party) : ℕ :=
  countPairPreshared p q (pl.actions t)

/-- The number of fresh-pair teleportations between owner `p` and partner `q` along a
transcript. -/
def PartyPlan.freshPrepared {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (p q : Party) : ℕ :=
  countPairFresh p q (pl.actions t)

/-- The consecutive slot indices from zero up to the preshared-pair usage for an ordered pair of
parties. -/
def PartyPlan.consumedSlots {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (p q : Party) : List ℕ :=
  List.range (pl.presharedUsed t p q)

/-- The consumed preshared-slot list for an ordered pair of parties has no duplicates. -/
theorem consumedSlots_nodup {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (p q : Party) : (pl.consumedSlots t p q).Nodup :=
  List.nodup_range

/-- The length of the consumed-slot list equals the corresponding preshared-pair usage. -/
theorem consumedSlots_length {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (p q : Party) :
    (pl.consumedSlots t p q).length = pl.presharedUsed t p q :=
  List.length_range

/-- A bound on preshared-pair usage by the available supply also bounds the length of the
consumed-slot list. -/
theorem presharedUsed_le_available {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (sup : EPRSupply) (p q : Party)
    (hfeas : pl.presharedUsed t p q ≤ sup.available p q) :
    (pl.consumedSlots t p q).length ≤ sup.available p q := by
  rw [consumedSlots_length]
  exact hfeas

/-- The nonnegative excess of preshared-pair usage over the available supply for an ordered pair
of parties. -/
def PartyPlan.supplyDeficit {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (sup : EPRSupply) (p q : Party) : ℕ :=
  max 0 (pl.presharedUsed t p q - sup.available p q)

/-- The counts satisfying `q` and respectively `r` or its negation sum to the count satisfying
`q`. -/
private theorem countP_split {α : Type} (l : List α) (q r : α → Bool) :
    (l.countP (fun a => q a && r a)) + (l.countP (fun a => q a && !r a)) = l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.countP_cons]
      cases hq : q a with
      | false =>
          cases hr : r a with
          | false => exact ih
          | true => exact ih
      | true =>
          cases hr : r a with
          | false => simp <;> omega
          | true => simp <;> omega

/-- Counting elements with the constantly true predicate gives the list length. -/
private theorem countP_true {α : Type} (l : List α) : l.countP (fun _ => true) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.countP_cons, ih]

/-- For each ordered pair of parties, preshared usage plus fresh preparation equals the number
of its teleportation actions. -/
theorem preshared_fresh_disjoint {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (p q : Party) :
    pl.presharedUsed t p q + pl.freshPrepared t p q
      = countPairTeleport p q (pl.actions t) := by
  unfold PartyPlan.presharedUsed PartyPlan.freshPrepared
  exact pair_split p q (pl.actions t)

/-- The total number of preshared-pair teleportation steps along a transcript. -/
def PartyPlan.presharedCount {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) : ℕ :=
  countPresharedSteps (pl.actions t)

/-- The total number of fresh-pair teleportation steps along a transcript. -/
def PartyPlan.freshCount {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) : ℕ :=
  countFreshSteps (pl.actions t)

/-- Measurement actions in a party plan and instrument events in its network have equal counts
along each transcript. -/
theorem measureCount_eq_events : ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P)
    (t : P.Transcript),
    countMeasureActions (pl.actions t) = countInstrumentEvents (P.events t) := by
  intro D E P
  induction P with
  | done D =>
      intro pl t
      cases pl
      simp only [PartyPlan.actions, FiniteNetwork.events, countMeasureActions,
          countInstrumentEvents]
  | measure s I next ih =>
      intro pl t
      cases pl with
      | @measure _ _ _ _ _ _ owner rest =>
          simp only [PartyPlan.measureCount, PartyPlan.actions, FiniteNetwork.events,
            countMeasureActions, countInstrumentEvents]
          rw [ih t.1 (rest t.1) t.2]
  | send bits next ih =>
      intro pl t
      cases pl with
      | @send _ _ _ _ sender receiver rest =>
          simp only [PartyPlan.measureCount, PartyPlan.actions, FiniteNetwork.events,
            countMeasureActions, countInstrumentEvents]
          rw [ih rest t]
  | teleport hn width fits next ih =>
      intro pl t
      cases pl with
      | @teleport _ _ _ _ _ _ owner partner preshared rest =>
          simp only [PartyPlan.measureCount, PartyPlan.actions, FiniteNetwork.events,
            countMeasureActions, countInstrumentEvents]
          rw [ih t.1 (rest t.1) t.2]

/-- Teleportation actions in a party plan and teleportation events in its network have equal
counts along each transcript. -/
theorem teleportCount_eq_events : ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P)
    (t : P.Transcript),
    countTeleportActions (pl.actions t) = countTeleportEvents (P.events t) := by
  intro D E P
  induction P with
  | done D =>
      intro pl t
      cases pl
      simp only [PartyPlan.actions, FiniteNetwork.events, countTeleportActions, countTeleportEvents]
  | measure s I next ih =>
      intro pl t
      cases pl with
      | @measure _ _ _ _ _ _ owner rest =>
          simp only [PartyPlan.teleportCount, PartyPlan.actions, FiniteNetwork.events,
            countTeleportActions, countTeleportEvents]
          rw [ih t.1 (rest t.1) t.2]
  | send bits next ih =>
      intro pl t
      cases pl with
      | @send _ _ _ _ sender receiver rest =>
          simp only [PartyPlan.teleportCount, PartyPlan.actions, FiniteNetwork.events,
            countTeleportActions, countTeleportEvents]
          rw [ih rest t]
  | teleport hn width fits next ih =>
      intro pl t
      cases pl with
      | @teleport _ _ _ _ _ _ owner partner preshared rest =>
          simp only [PartyPlan.teleportCount, PartyPlan.actions, FiniteNetwork.events,
            countTeleportActions, countTeleportEvents]
          rw [ih t.1 (rest t.1) t.2]

/-- A party plan's measurement count equals the number of instrument events in the underlying
network transcript. -/
theorem plan_measureCount_eq {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P)
    (t : P.Transcript) :
    pl.measureCount t = countInstrumentEvents (P.events t) := by
  rw [PartyPlan.measureCount]
  exact measureCount_eq_events P pl t

/-- A party plan's teleportation count equals the number of teleportation events in the
underlying network transcript. -/
theorem plan_teleportCount_eq {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P)
    (t : P.Transcript) :
    pl.teleportCount t = countTeleportEvents (P.events t) := by
  rw [PartyPlan.teleportCount]
  exact teleportCount_eq_events P pl t

/-- The abstract-instrument-call resource count equals the number of instrument events. -/
private theorem abstractCalls_eq_events_aux (es : List NetworkEvent) :
    (eventResources es).abstractInstrumentCalls = countInstrumentEvents es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | instrument s o =>
          simp only [eventResources, countInstrumentEvents]
          rw [ih]
          omega
      | transmit bits =>
          simp only [eventResources, countInstrumentEvents]
          rw [ih]
      | teleport n hn o =>
          simp only [eventResources, countInstrumentEvents]
          rw [ih]

/-- The number of entries in the fresh-pair dimension list equals the number of teleportation
events. -/
private theorem freshPairDimensions_eq_teleportEvents_aux (es : List NetworkEvent) :
    (eventResources es).freshPairDimensions.length = countTeleportEvents es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | instrument s o =>
          simp only [eventResources, countTeleportEvents]
          rw [ih]
      | transmit bits =>
          simp only [eventResources, countTeleportEvents]
          rw [ih]
      | teleport n hn o =>
          simp only [eventResources, countTeleportEvents, List.length_cons]
          rw [ih]
          omega

/-- The macro-measurement count of a network transcript equals its number of teleportation
events. -/
theorem macroMeasurements_eq_teleportEvents : ∀ {D E : ℕ} (P : FiniteNetwork D E)
    (t : P.Transcript),
    (P.resources t).macroMeasurements = countTeleportEvents (P.events t) := by
  intro D E P t
  have h := network_resource_invariants P t
  have h2 := freshPairDimensions_eq_teleportEvents_aux (P.events t)
  have h2' : (P.resources t).freshPairDimensions.length
      = countTeleportEvents (P.events t) := by
    simpa only [FiniteNetwork.resources] using h2
  omega

/-- An execution cost record separating abstract instrument calls, macro gates and measurements,
declared native gates, communication bits, and preshared and fresh pairs. -/
structure LoccCost where

  abstractInstrumentCalls : ℕ

  macroGates : ℕ

  macroMeasurements : ℕ

  declaredNativeGates : ℕ

  classicalBits : ℕ

  presharedPairsUsed : ℕ

  freshPairsPrepared : ℕ
  deriving DecidableEq

/-- The execution cost record obtained from network resources, party-plan entanglement counts,
and a supplied native-gate count. -/
noncomputable def PartyPlan.cost {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (declaredNative : ℕ) : LoccCost :=
  { abstractInstrumentCalls := (P.resources t).abstractInstrumentCalls
    macroGates := (P.resources t).matrixGates
    macroMeasurements := (P.resources t).macroMeasurements
    declaredNativeGates := declaredNative
    classicalBits := (P.resources t).classicalBits
    presharedPairsUsed := pl.presharedCount t
    freshPairsPrepared := pl.freshCount t }

/-- The macro-gate count is six times the macro-measurement count. -/
theorem cost_macro_gates {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (d : ℕ) :
    (pl.cost t d).macroGates = 6 * (pl.cost t d).macroMeasurements := by
  have h := network_resource_invariants P t
  simp only [PartyPlan.cost] at h ⊢
  omega

/-- The macro-gate count is six times the macro-measurement count, and abstract instrument calls
equal the party plan's measurement count. -/
theorem cost_abstract_calls_are_free {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (d : ℕ) :
    (pl.cost t d).macroGates = 6 * (pl.cost t d).macroMeasurements ∧
      (pl.cost t d).abstractInstrumentCalls = pl.measureCount t := by
  refine ⟨cost_macro_gates pl t d, ?_⟩
  simp only [PartyPlan.cost]
  have h1 := abstractCalls_eq_events_aux (P.events t)
  have h2 := measureCount_eq_events P pl t
  have h1' : (P.resources t).abstractInstrumentCalls = countInstrumentEvents (P.events t) := by
    simpa only [FiniteNetwork.resources] using h1
  have h2' : countMeasureActions (pl.actions t) = countInstrumentEvents (P.events t) := h2
  simp only [PartyPlan.cost, PartyPlan.measureCount]
  omega

/-- The macro-measurement count equals the party plan's teleportation count. -/
theorem cost_macro_measurements {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (d : ℕ) :
    (pl.cost t d).macroMeasurements = pl.teleportCount t := by
  have h := macroMeasurements_eq_teleportEvents P t
  have h2 := teleportCount_eq_events P pl t
  simp only [PartyPlan.cost, PartyPlan.teleportCount]
  omega

/-- The preshared-pair and fresh-pair counts in the cost record sum to the total teleportation
count. -/
theorem cost_entanglement_split {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (d : ℕ) :
    (pl.cost t d).presharedPairsUsed + (pl.cost t d).freshPairsPrepared
      = pl.teleportCount t := by
  have hsplit : pl.presharedCount t + pl.freshCount t = pl.teleportCount t := by
    unfold PartyPlan.presharedCount PartyPlan.freshCount PartyPlan.teleportCount
    exact preshared_fresh_split (pl.actions t)
  simp only [PartyPlan.cost]
  omega

/-- A resource record of gate, measurement, and input counts for an input-loading procedure. -/
structure InputLoading where

  gates : ℕ

  measurements : ℕ

  inputs : ℕ
  deriving DecidableEq

/-- The input-loading resource record with six gates, one measurement, and one input for a
nonzero qudit dimension. -/
def entangledInputLoading (n : ℕ) [NeZero n] : InputLoading :=
  { gates := 6, measurements := 1, inputs := 1 }

/-- The gate count of entangled input loading equals that of any qudit teleportation program
leaf. -/
theorem entangledInputLoading_gates (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    (entangledInputLoading n).gates = (quditProgramLeaf n o).gates := by
  rw [entangledInputLoading]
  exact (quditProgramLeaf_counts n o).2.2.1.symm

/-- The measurement count of entangled input loading equals that of any qudit teleportation
program leaf. -/
theorem entangledInputLoading_measurements (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    (entangledInputLoading n).measurements = (quditProgramLeaf n o).measurements := by
  rw [entangledInputLoading]
  exact (quditProgramLeaf_counts n o).2.2.2.1.symm

/-- A teleportation node on input conjugated by `U` applies the actual teleportation branch to
that input and then runs the selected continuation. -/
theorem loadedInput_teleport_branch {n E : ℕ} [NeZero n] (U : Operator n)
    (width : ℕ) (fits : n ≤ 2 ^ width) (next : Fin n × Fin n → FiniteNetwork n E)
    (o : Fin n × Fin n) (t : (next o).Transcript) (ρ : Operator n) :
    networkBranch (.teleport (inferInstance : NeZero n) width fits next) ⟨o, t⟩
        (U * ρ * Uᴴ)
      = networkBranch (next o) t (quditActualBranchCore n o (U * ρ * Uᴴ)) :=
  teleport_node_execution width fits next o t _

/-- Entangled input loading matches both the gate and measurement costs of a qudit teleportation
program leaf. -/
theorem loading_cost_is_separate (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    (entangledInputLoading n).gates = (quditProgramLeaf n o).gates ∧
      (entangledInputLoading n).measurements = (quditProgramLeaf n o).measurements :=
  ⟨entangledInputLoading_gates n o, entangledInputLoading_measurements n o⟩

/-- The complete binary message tree whose leaves all have the specified depth. -/
def completeTree : ℕ → BinaryMessageTree
  | 0 => .leaf
  | k + 1 => .fork (completeTree k) (completeTree k)

/-- The complete binary message tree indexed by `k` has depth `k`. -/
theorem completeTree_depth (k : ℕ) : (completeTree k).depth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [completeTree, BinaryMessageTree.depth, ih, max_self]

/-- The complete binary message tree of depth `k` has `2 ^ k` leaf paths. -/
theorem completeTree_card (k : ℕ) : Fintype.card (completeTree k).Path = 2 ^ k := by
  induction k with
  | zero => simp [completeTree, BinaryMessageTree.Path]
  | succ k ih =>
      have hcard : Fintype.card ((completeTree k).Path ⊕ (completeTree k).Path)
          = 2 ^ k + 2 ^ k := by simp only [Fintype.card_sum, ih]
      calc Fintype.card (completeTree (k + 1)).Path
          = Fintype.card ((completeTree k).Path ⊕ (completeTree k).Path) := rfl
        _ = 2 ^ k + 2 ^ k := hcard
        _ = 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- Every path in the complete depth-`k` message tree has an encoding of length `k`. -/
theorem completeTree_encode_length (k : ℕ) (t : (completeTree k).Path) :
    ((completeTree k).encode t).length = k := by
  induction k with
  | zero =>
      cases t
      rfl
  | succ k ih =>
      cases t with
      | inl p => simp [completeTree, BinaryMessageTree.encode, ih]
      | inr p => simp [completeTree, BinaryMessageTree.encode, ih]

/-- If `k ≤ C`, the complete depth-`k` message tree has at most `2 ^ C` paths. -/
theorem completeTree_card_le (k C : ℕ) (hC : k ≤ C) :
    Fintype.card (completeTree k).Path ≤ 2 ^ C := by
  rw [completeTree_card]
  exact Nat.pow_le_pow_right (by decide) hC

/-- The network that measures with `I`, transmits the tree encoding of its outcome, and executes
the fixed continuation. -/
noncomputable def messageNetwork {D E F : ℕ} (T : BinaryMessageTree)
    (I : Instrument (Fin (Fintype.card T.Path)) D E) (next : FiniteNetwork E F) :
    FiniteNetwork D F :=
  .measure (Fintype.card T.Path) I
    (fun o => .send (T.encode ((Fintype.equivFin T.Path).symm o)) next)

/-- A message-network event trace consists of the instrument outcome, its encoded transmission,
and the continuation's events. -/
theorem messageNetwork_transmitted {D E F : ℕ} (T : BinaryMessageTree)
    (I : Instrument (Fin (Fintype.card T.Path)) D E) (next : FiniteNetwork E F)
    (o : Fin (Fintype.card T.Path)) (t' : next.Transcript) :
    (messageNetwork T I next).events ⟨o, t'⟩ =
      .instrument (Fintype.card T.Path) o.val ::
        .transmit (T.encode ((Fintype.equivFin T.Path).symm o)) :: (next.events t') := rfl

/-- A message-network node adds its encoded-word length to the continuation's classical-bit
count. -/
theorem messageNetwork_bits {D E F : ℕ} (T : BinaryMessageTree)
    (I : Instrument (Fin (Fintype.card T.Path)) D E) (next : FiniteNetwork E F)
    (o : Fin (Fintype.card T.Path)) (t' : next.Transcript) :
    ((messageNetwork T I next).resources ⟨o, t'⟩).classicalBits =
      (T.encode ((Fintype.equivFin T.Path).symm o)).length
        + (next.resources t').classicalBits := by
  have h1 := network_resource_invariants (messageNetwork T I next) ⟨o, t'⟩
  have h2 := network_resource_invariants next t'
  have h3 : (messageNetwork T I next).events ⟨o, t'⟩
      = .instrument (Fintype.card T.Path) o.val
        :: .transmit (T.encode ((Fintype.equivFin T.Path).symm o))
        :: (next.events t') := rfl
  rw [h3] at h1
  have h5 := h1.2.2.2
  have h6 : transmittedWords (.instrument (Fintype.card T.Path) o.val
        :: .transmit (T.encode ((Fintype.equivFin T.Path).symm o)) :: (next.events t'))
      = (T.encode ((Fintype.equivFin T.Path).symm o)) :: transmittedWords (next.events t') := rfl
  rw [h6] at h5
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h5
  have h4 : ((transmittedWords (next.events t')).map List.length).sum
      = (next.resources t').classicalBits := h2.2.2.2.symm
  omega

/-- The word transmitted for any outcome has length at most the message-tree depth. -/
theorem messageNetwork_word_le_depth {D E F : ℕ} (T : BinaryMessageTree)
    (_I : Instrument (Fin (Fintype.card T.Path)) D E) (_next : FiniteNetwork E F)
    (o : Fin (Fintype.card T.Path)) :
    (T.encode ((Fintype.equivFin T.Path).symm o)).length ≤ T.depth :=
  messageTree_word_length T ((Fintype.equivFin T.Path).symm o)

/-- The party plan assigning the measurement and transmission to the sender, the transmission
endpoint to the receiver, and the supplied plan to the continuation. -/
noncomputable def messageNetworkPlan {D E F : ℕ} (T : BinaryMessageTree)
    (I : Instrument (Fin (Fintype.card T.Path)) D E) (next : FiniteNetwork E F)
    (nextPlan : PartyPlan next) (sender receiver : Party) :
    PartyPlan (messageNetwork T I next) :=
  .measure sender (fun _ => .send sender receiver nextPlan)

/-- The encoding that replaces every bit of a word by `r` consecutive copies. -/
def redundantEncode (r : ℕ) : List Bool → List Bool
  | [] => []
  | b :: bs => List.replicate r b ++ redundantEncode r bs

/-- Repeating each bit `r` times multiplies the length of a word by `r`. -/
theorem redundantEncode_length (r : ℕ) (w : List Bool) :
    (redundantEncode r w).length = r * w.length := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
      simp only [redundantEncode, List.length_append, List.length_replicate, ih,
        List.length_cons]
      ring

/-- Repeating each bit a positive number of times cannot shorten a word. -/
theorem redundantEncode_length_pos {r : ℕ} (hr : 0 < r) (w : List Bool) :
    w.length ≤ (redundantEncode r w).length := by
  have key : ∀ (n : ℕ), n ≤ r * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.mul_succ]
        have hr1 : 1 ≤ r := hr
        omega
  have h := redundantEncode_length r w
  rw [h]
  exact key w.length

/-- A deterministic guessing scheme with `k` input-dependent message words of fixed per-round
lengths and a guess function on their concatenation. -/
structure MultiRoundGuess (X : Type) [Fintype X] (k : ℕ) where

  alice : X → Fin k → List Bool

  guess : List Bool → X

  roundLength : Fin k → ℕ

  alice_length : ∀ x i, (alice x i).length = roundLength i

/-- The concatenation of Alice's round messages in increasing round order. -/
def MultiRoundGuess.concatenated {X : Type} [Fintype X] {k : ℕ}
    (P : MultiRoundGuess X k) (x : X) : List Bool :=
  (List.finRange k).flatMap fun i => P.alice x i

/-- The sum of the prescribed message lengths over all rounds. -/
def MultiRoundGuess.totalBits {X : Type} [Fintype X] {k : ℕ}
    (P : MultiRoundGuess X k) : ℕ :=
  ∑ i : Fin k, P.roundLength i

/-- Equality of Alice's words in every round implies equality of their concatenations. -/
theorem MultiRoundGuess.concatenated_eq_of_same_words {X : Type} [Fintype X] {k : ℕ}
    (P : MultiRoundGuess X k) (x y : X) (h : ∀ i, P.alice x i = P.alice y i) :
    (List.finRange k).flatMap (P.alice x) = (List.finRange k).flatMap (P.alice y) := by
  have h2 : ∀ (l : List (Fin k)), l.flatMap (P.alice x) = l.flatMap (P.alice y) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp [h i, ih]
  exact h2 (List.finRange k)

/-- Equal concatenated transcripts produce the same value under the protocol's guess function. -/
theorem MultiRoundGuess.concatenated_injective {X : Type} [Fintype X] {k : ℕ}
    (P : MultiRoundGuess X k) (x y : X) (h : P.concatenated x = P.concatenated y) :
    P.guess (P.concatenated x) = P.guess (P.concatenated y) := by
  rw [h]

/-- The instrument obtained by relabelling outcomes along the equivalence `e`. -/
noncomputable def instrumentReindex {O P : Type*} [Fintype O] [Fintype P]
    {D E : ℕ} (I : Instrument O D E) (e : O ≃ P) : Instrument P D E :=
  I.coarsen e

/-- The branch at a relabelled outcome is the original branch at its inverse image under `e`. -/
theorem instrumentReindex_branch {O P : Type*} [Fintype O] [Fintype P]
    {D E : ℕ} (I : Instrument O D E) (e : O ≃ P) (p : P) :
    (instrumentReindex I e).branch p = I.branch (e.symm p) := by
  have hfilter : Finset.univ.filter (fun o : O => e o = p) = {e.symm p} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have h' : e o = e (e.symm p) := h.trans (Equiv.symm_apply_apply e.symm p).symm
      exact e.injective h'
    · intro h
      subst h
      simp
  show (∑ o ∈ Finset.univ.filter (fun o : O => e o = p), I.branch o) = I.branch (e.symm p)
  rw [hfilter, Finset.sum_singleton]

/-- The sum of all reindexed instrument branches preserves trace. -/
theorem instrumentReindex_total {O P : Type*} [Fintype O] [Fintype P]
    {D E : ℕ} (I : Instrument O D E) (e : O ≃ P) (A : Operator D) :
    Matrix.trace (∑ p, (instrumentReindex I e).branch p A) = Matrix.trace A :=
  (instrumentReindex I e).total A

/-- Relabelling instrument outcomes by an equivalence leaves the forgotten channel unchanged. -/
theorem instrumentReindex_forget {O P : Type*} [Fintype O] [Fintype P]
    {D E : ℕ} (I : Instrument O D E) (e : O ≃ P) (ρ : Operator D) :
    (instrumentReindex I e).forget.map ρ = I.forget.map ρ :=
  Instrument.forget_coarsen_apply I e ρ

/-- A one-way guessing protocol with `Fin s` instrument outcomes identified with paths of a
binary message tree. -/
structure FinGuessProtocol (X : Type) [Fintype X] (T : BinaryMessageTree)
    (A E B F : ℕ) (s : ℕ) where

  alice : X → Instrument (Fin s) A E

  bob : Fin s → Instrument X B F

  reindex : Fin s ≃ T.Path

/-- The tree-message guessing protocol obtained by reindexing Alice's outcomes and Bob's
instruments along the specified path equivalence. -/
noncomputable def FinGuessProtocol.toTree {X : Type} [Fintype X]
    {T : BinaryMessageTree} {A E B F : ℕ} {s : ℕ} (P : FinGuessProtocol X T A E B F s) :
    OneWayGuessingProtocol X T A E B F where
  alice x := instrumentReindex (P.alice x) P.reindex
  bob t := P.bob (P.reindex.symm t)

/-- The success of the converted tree protocol equals the prior-weighted sum of correct-guess
probabilities over the original finite outcomes. -/
theorem FinGuessProtocol.success_eq {X : Type} [Fintype X] {T : BinaryMessageTree}
    {A E B F : ℕ} {s : ℕ} (P : FinGuessProtocol X T A E B F s)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (prior : X → ℝ) :
    P.toTree.success σ prior
      = ∑ x, ∑ o, prior x * instrumentProb (P.bob o)
          (partialTraceFirst (tensorLeft ((P.alice x).branch o) σ)) x := by
  classical
  have hinner : ∀ x : X,
      (∑ t : T.Path, prior x * instrumentProb (P.bob (P.reindex.symm t))
        (partialTraceFirst (tensorLeft ((instrumentReindex (P.alice x) P.reindex).branch t) σ)) x)
      = ∑ o : Fin s, prior x * instrumentProb (P.bob o)
        (partialTraceFirst (tensorLeft ((P.alice x).branch o) σ)) x := by
    intro x
    have hsum : (∑ t : T.Path, prior x * instrumentProb (P.bob (P.reindex.symm t))
        (partialTraceFirst (tensorLeft ((instrumentReindex (P.alice x) P.reindex).branch t) σ)) x)
        = ∑ t : T.Path, prior x * instrumentProb (P.bob (P.reindex.symm t))
        (partialTraceFirst (tensorLeft ((P.alice x).branch (P.reindex.symm t)) σ)) x := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [instrumentReindex_branch]
    rw [hsum]
    exact Equiv.sum_comp P.reindex.symm (fun o =>
      prior x * instrumentProb (P.bob o)
        (partialTraceFirst (tensorLeft ((P.alice x).branch o) σ)) x)
  have hgoal : (∑ x, ∑ t, prior x * instrumentProb (P.bob (P.reindex.symm t))
        (partialTraceFirst (tensorLeft ((instrumentReindex (P.alice x) P.reindex).branch t) σ)) x)
      = ∑ x, ∑ o, prior x * instrumentProb (P.bob o)
        (partialTraceFirst (tensorLeft ((P.alice x).branch o) σ)) x := by
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  unfold FinGuessProtocol.toTree OneWayGuessingProtocol.success
    OneWayGuessingProtocol.bobState
  exact hgoal

/-- For a uniform prior on a nonempty finite input type and a shared density operator, a
tree-depth bound `C` gives success at most `2 ^ C / Fintype.card X`. -/
theorem FinGuessProtocol.success_le {X : Type} [Fintype X] [Nonempty X]
    {T : BinaryMessageTree} {A E B F : ℕ} {s : ℕ} (P : FinGuessProtocol X T A E B F s)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C) :
    P.toTree.success σ (fun _ => 1 / (Fintype.card X : ℝ)) ≤ (2 : ℝ) ^ C / Fintype.card X :=
  oneWay_uniform_bits_success_le P.toTree σ hσ htrace C hC

/-- A one-way guessing protocol with a finite message type, input-dependent Alice instruments,
and message-dependent Bob guessing instruments. -/
structure MessageGuessProtocol (X : Type) [Fintype X] (M : Type) [Fintype M]
    (A E B F : ℕ) where

  alice : X → Instrument M A E

  bob : M → Instrument X B F

/-- Bob's unnormalized state conditioned on Alice's input and instrument message, obtained by
tracing out Alice's output. -/
noncomputable def MessageGuessProtocol.bobState {X : Type} [Fintype X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (x : X) (m : M) : Operator B :=
  partialTraceFirst (tensorLeft ((P.alice x).branch m) σ)

/-- The prior-weighted sum of correct-guess probabilities over all inputs and messages. -/
noncomputable def MessageGuessProtocol.success {X : Type} [Fintype X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (prior : X → ℝ) : ℝ :=
  ∑ x, ∑ m, prior x * instrumentProb (P.bob m) (P.bobState σ x m) x

/-- For every input, summing Bob's conditional states over all messages returns his original
marginal. -/
theorem MessageGuessProtocol.no_signalling {X : Type} [Fintype X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (x : X) :
    ∑ m, P.bobState σ x m = partialTraceFirst σ := by
  have he : partialTraceFirst (∑ m, tensorLeft ((P.alice x).branch m) σ)
      = ∑ m, P.bobState σ x m := by
    ext i j
    simp only [MessageGuessProtocol.bobState, partialTraceFirst, Matrix.traceLeft,
      Matrix.of_apply, Matrix.sum_apply]
    exact Finset.sum_comm
  rw [← he]
  exact (P.alice x).referenceMarginal σ

/-- The probability of a fixed instrument outcome is additive over finite sums of input
operators. -/
private theorem instrumentProb_sum_input {O K : Type*} [Fintype O] [Fintype K]
    {B F : ℕ} (J : Instrument O B F) (states : K → Operator B) (o : O) :
    instrumentProb J (∑ k, states k) o = ∑ k, instrumentProb J (states k) o := by
  simp [instrumentProb, map_sum, Matrix.trace_sum, Complex.re_sum]

/-- On positive semidefinite shared input, the success contribution of a single message is
bounded by Bob's corresponding outcome probability on his original marginal. -/
theorem MessageGuessProtocol.branch_le_blind {X : Type} [Fintype X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (x : X) (m : M) :
    instrumentProb (P.bob m) (P.bobState σ x m) x
      ≤ instrumentProb (P.bob m) (partialTraceFirst σ) x := by
  have hpos (m' : M) : (P.bobState σ x m').PosSemidef :=
    (tensorLeft_posSemidef ((P.alice x).cp m') hσ).traceLeft
  calc
    instrumentProb (P.bob m) (P.bobState σ x m) x
        ≤ ∑ m', instrumentProb (P.bob m) (P.bobState σ x m') x :=
      Finset.single_le_sum (fun m' _ => instrumentProb_nonneg (P.bob m) (hpos m') x)
        (Finset.mem_univ m)
    _ = instrumentProb (P.bob m) (partialTraceFirst σ) x := by
      rw [← instrumentProb_sum_input, MessageGuessProtocol.no_signalling]

/-- For a shared density operator and nonnegative prior weights bounded by `p`, guessing success
is at most the message count times `p`. -/
theorem MessageGuessProtocol.success_le {X : Type} [Fintype X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (prior : X → ℝ) (p : ℝ)
    (hprior : ∀ x, 0 ≤ prior x) (hmax : ∀ x, prior x ≤ p) :
    P.success σ prior ≤ (Fintype.card M : ℝ) * p := by
  have hβ : (partialTraceFirst σ).PosSemidef := hσ.traceLeft
  have hmass (m : M) : ∑ x, instrumentProb (P.bob m) (partialTraceFirst σ) x = 1 := by
    rw [sum_instrumentProb, Matrix.traceLeft_trace, htrace]
    rfl
  calc
    P.success σ prior = ∑ m, ∑ x,
        prior x * instrumentProb (P.bob m) (P.bobState σ x m) x :=
      Finset.sum_comm
    _ ≤ ∑ m, ∑ x, p * instrumentProb (P.bob m) (partialTraceFirst σ) x := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro x _
      exact (mul_le_mul_of_nonneg_left
          (MessageGuessProtocol.branch_le_blind P σ hσ x m) (hprior x)).trans
        (mul_le_mul_of_nonneg_right (hmax x) (instrumentProb_nonneg (P.bob m) hβ x))
    _ = (Fintype.card M : ℝ) * p := by
      simp only [← Finset.mul_sum, hmass, mul_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

/-- With a uniform prior on a nonempty finite input type, guessing success is at most the
message count divided by the input count. -/
theorem MessageGuessProtocol.uniform_success_le {X : Type} [Fintype X] [Nonempty X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) :
    P.success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (Fintype.card M : ℝ) * (1 / (Fintype.card X : ℝ)) := by
  have hn : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := MessageGuessProtocol.success_le P σ hσ htrace (fun _ => 1 / (Fintype.card X : ℝ))
    (1 / (Fintype.card X : ℝ)) (fun _ => (one_div_pos.mpr hn).le) (fun _ => le_refl _)
  simpa only [div_eq_mul_inv, one_mul] using h

/-- The protocol obtained by coarsening Alice's messages along `m` and using the supplied
instruments for Bob on the new messages. -/
noncomputable def MessageGuessProtocol.coarsen {X : Type} [Fintype X]
    {M N : Type} [Fintype M] [Fintype N] {A E B F : ℕ}
    (P : MessageGuessProtocol X M A E B F) (m : M → N) (bob : N → Instrument X B F) :
    MessageGuessProtocol X N A E B F where
  alice x := (P.alice x).coarsen m
  bob := bob

/-- After coarsening to message type `N`, uniform guessing success is bounded by the cardinality
of `N` divided by the input cardinality. -/
theorem MessageGuessProtocol.coarsen_uniform_success_le {X : Type} [Fintype X]
    [Nonempty X] {M N : Type} [Fintype M] [Fintype N] {A E B F : ℕ}
    (P : MessageGuessProtocol X M A E B F) (m : M → N) (bob : N → Instrument X B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) :
    (P.coarsen m bob).success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (Fintype.card N : ℝ) * (1 / (Fintype.card X : ℝ)) :=
  MessageGuessProtocol.uniform_success_le (P.coarsen m bob) σ hσ htrace

/-- After coarsening messages to a binary tree of depth at most `C`, uniform guessing success is
at most `2 ^ C / Fintype.card X`. -/
theorem MessageGuessProtocol.coarsen_tree_success_le {X : Type} [Fintype X]
    [Nonempty X] {M : Type} [Fintype M] {T : BinaryMessageTree} {A E B F : ℕ}
    (P : MessageGuessProtocol X M A E B F) (m : M → T.Path)
    (bob : T.Path → Instrument X B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C) :
    (P.coarsen m bob).success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (2 : ℝ) ^ C * (1 / (Fintype.card X : ℝ)) := by
  have h1 := MessageGuessProtocol.coarsen_uniform_success_le P m bob σ hσ htrace
  have hc : Fintype.card T.Path ≤ 2 ^ C :=
    (messageTree_card_le T).trans (Nat.pow_le_pow_right (by decide) hC)
  have hc' : (Fintype.card T.Path : ℝ) ≤ (2 : ℝ) ^ C := by exact_mod_cast hc
  calc
    (P.coarsen m bob).success σ (fun _ => 1 / (Fintype.card X : ℝ))
        ≤ (Fintype.card T.Path : ℝ) * (1 / (Fintype.card X : ℝ)) := h1
    _ ≤ (2 : ℝ) ^ C * (1 / (Fintype.card X : ℝ)) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)

/-- If the sum of a finite family of linear maps preserves trace, its tensor extension preserves
the marginal of any reference system. -/
theorem referenceMarginal_of_total {O : Type*} [Fintype O] {D E : ℕ}
    (B : O → (Operator D →ₗ[ℂ] Operator E))
    (hTP : ∀ A, Matrix.trace (∑ o, B o A) = Matrix.trace A)
    {R : ℕ} (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    partialTraceFirst (∑ o, tensorLeft (B o) ρ) = partialTraceFirst ρ := by
  ext r r'
  have hstep : ∀ o : O, ∑ a : Fin E, tensorLeft (B o) ρ (a, r) (a, r')
      = Matrix.trace (B o (fun i j => ρ (i, r) (j, r'))) := by
    intro o
    simp only [Matrix.trace, Matrix.diag_apply, tensorLeft]
  show (∑ a : Fin E, (∑ o : O, tensorLeft (B o) ρ) (a, r) (a, r'))
      = ∑ a : Fin D, ρ (a, r) (a, r')
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]
  have h2 : (∑ o : O, ∑ a : Fin E, tensorLeft (B o) ρ (a, r) (a, r'))
      = ∑ o : O, Matrix.trace (B o (fun i j => ρ (i, r) (j, r'))) :=
    Finset.sum_congr rfl fun o _ => hstep o
  rw [h2, ← Matrix.trace_sum, hTP]
  rfl

/-- Tensor extension of a finite branch family whose sum preserves trace also preserves total
trace after summing outcomes. -/
theorem tensorLeft_total_of_total {O : Type*} [Fintype O] {D E : ℕ}
    (B : O → (Operator D →ₗ[ℂ] Operator E))
    (hTP : ∀ A, Matrix.trace (∑ o, B o A) = Matrix.trace A)
    {R : ℕ} (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix.trace (∑ o, tensorLeft (B o) ρ) = Matrix.trace ρ := by
  calc Matrix.trace (∑ o, tensorLeft (B o) ρ)
      = Matrix.trace (partialTraceFirst (∑ o, tensorLeft (B o) ρ)) :=
        (Matrix.traceLeft_trace _).symm
    _ = Matrix.trace (partialTraceFirst ρ) :=
          congrArg Matrix.trace (referenceMarginal_of_total B hTP ρ)
    _ = Matrix.trace ρ := Matrix.traceLeft_trace _

/-- For completely positive branches whose sum preserves trace, each tensor-extended branch is
trace nonincreasing on positive semidefinite input. -/
theorem tensorLeft_tni_of_total {O : Type*} [Fintype O] {D E : ℕ}
    (B : O → (Operator D →ₗ[ℂ] Operator E))
    (hCP : ∀ o, CompletelyPositive (B o))
    (hTP : ∀ A, Matrix.trace (∑ o, B o A) = Matrix.trace A)
    {R : ℕ} {ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ} (hρ : ρ.PosSemidef) (o : O) :
    (Matrix.trace (tensorLeft (B o) ρ)).re ≤ (Matrix.trace ρ).re := by
  have hm : ∀ p, 0 ≤ (Matrix.trace (tensorLeft (B p) ρ)).re :=
    fun p => (RCLike.nonneg_iff.mp (tensorLeft_posSemidef (hCP p) hρ).trace_nonneg).1
  calc (Matrix.trace (tensorLeft (B o) ρ)).re
      ≤ ∑ p, (Matrix.trace (tensorLeft (B p) ρ)).re :=
        Finset.single_le_sum (fun p _ => hm p) (Finset.mem_univ o)
    _ = (Matrix.trace ρ).re := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, tensorLeft_total_of_total B hTP ρ]

/-- The instrument obtained by conjugating each branch output by its outcome-selected unitary. -/
noncomputable def conditionalUnitaryInstrument {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) : Instrument O D E where
  branch o := (conjBranch (U o)).comp (I.branch o)
  cp o := (completelyPositive_conjBranch (U o)).comp (I.cp o)
  tni o := by
    intro A hA
    have h := I.tni o hA
    have h' : Matrix.trace ((conjBranch (U o)).comp (I.branch o) A)
        = Matrix.trace (I.branch o A) := trace_conjBranch_unitary (U o) (hU o) (I.branch o A)
    rw [h']
    exact h
  total := by
    intro A
    calc Matrix.trace (∑ o, ((conjBranch (U o)).comp (I.branch o)) A)
        = ∑ o, Matrix.trace (conjBranch (U o) (I.branch o A)) := by
          rw [Matrix.trace_sum]
          rfl
      _ = ∑ o, Matrix.trace (I.branch o A) :=
          Finset.sum_congr rfl fun o _ => trace_conjBranch_unitary (U o) (hU o) (I.branch o A)
      _ = Matrix.trace (∑ o, I.branch o A) := (Matrix.trace_sum _ _).symm
      _ = Matrix.trace A := I.total A

/-- A branch of the conditional-unitary instrument is the corresponding original branch
conjugated by its selected unitary. -/
theorem conditionalUnitaryInstrument_branch {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) (o : O) (ρ : Operator D) :
    (conditionalUnitaryInstrument I U hU).branch o ρ
      = (U o) * (I.branch o ρ) * (U o)ᴴ := rfl

/-- Forgetting the conditional-unitary outcome sums all original branch outputs after their
selected unitary conjugations. -/
theorem conditionalUnitaryInstrument_forget {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) (ρ : Operator D) :
    (conditionalUnitaryInstrument I U hU).forget.map ρ
      = ∑ o, (U o) * (I.branch o ρ) * (U o)ᴴ :=
  (conditionalUnitaryInstrument I U hU).forget_apply ρ

/-- The sum of conditional-unitary branches preserves the marginal of an arbitrary reference
system. -/
theorem conditionalUnitaryInstrument_reference {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) (R : ℕ)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    partialTraceFirst (∑ o, tensorLeft ((conditionalUnitaryInstrument I U hU).branch o) ρ)
      = partialTraceFirst ρ :=
  referenceMarginal_of_total (fun o => (conjBranch (U o)).comp (I.branch o))
    (fun A => (conditionalUnitaryInstrument I U hU).total A) ρ

/-- Every tensor-extended conditional-unitary branch is trace nonincreasing on positive
semidefinite input. -/
theorem conditionalUnitaryInstrument_tni {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) (R : ℕ)
    {ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ} (hρ : ρ.PosSemidef) (o : O) :
    (Matrix.trace (tensorLeft ((conditionalUnitaryInstrument I U hU).branch o) ρ)).re
      ≤ (Matrix.trace ρ).re :=
  tensorLeft_tni_of_total (fun o => (conjBranch (U o)).comp (I.branch o))
    (fun o => (completelyPositive_conjBranch (U o)).comp (I.cp o))
    (fun A => (conditionalUnitaryInstrument I U hU).total A) hρ o

/-- A zero-probability conditional-unitary branch on positive semidefinite input has zero
output. -/
theorem conditionalUnitaryInstrument_zero {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) (ρ : Operator D) (o : O)
    (hρ : ρ.PosSemidef)
    (hz : instrumentProb (conditionalUnitaryInstrument I U hU) ρ o = 0) :
    (conditionalUnitaryInstrument I U hU).branch o ρ = 0 :=
  (instrumentProb_eq_zero_iff (conditionalUnitaryInstrument I U hU) hρ o).mp hz

/-- Each corrected qudit teleportation branch, tensored with an arbitrary reference, multiplies
the input by `1 / n ^ 2`. -/
theorem qudit_correction_reference {n : ℕ} [NeZero n] (R : ℕ)
    (ρ : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ) (o : Fin n × Fin n) :
    tensorLeft ((quditCorrectedInstrument n).branch o) ρ = (1 / (n : ℂ) ^ 2) • ρ :=
  tensorLeft_eq_smul ((1 : ℂ) / (n : ℂ) ^ 2)
    (fun ρ' => quditCorrectedInstrument_branch n ρ' o) ρ

/-- Summing all corrected qudit teleportation branches, with an arbitrary reference system,
returns the input operator. -/
theorem qudit_correction_reference_total {n : ℕ} [NeZero n] (R : ℕ)
    (ρ : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ) :
    (∑ o : Fin n × Fin n, tensorLeft ((quditCorrectedInstrument n).branch o) ρ) = ρ := by
  calc (∑ o : Fin n × Fin n, tensorLeft ((quditCorrectedInstrument n).branch o) ρ)
      = ∑ o : Fin n × Fin n, (1 / (n : ℂ) ^ 2) • ρ := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        exact tensorLeft_eq_smul ((1 : ℂ) / (n : ℂ) ^ 2)
          (fun ρ' => quditCorrectedInstrument_branch n ρ' o) ρ
    _ = ρ := by
      simp only [← Finset.sum_smul, qudit_uniform_scalar_sum, one_smul]

/-- The preshared and fresh teleportation counts of a party-plan transcript sum to its total
teleportation count. -/
theorem preshared_fresh_split_total {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P)
    (t : P.Transcript) :
    pl.presharedCount t + pl.freshCount t = pl.teleportCount t := by
  unfold PartyPlan.presharedCount PartyPlan.freshCount PartyPlan.teleportCount
  exact preshared_fresh_split (pl.actions t)

/-- The fresh-pair dimension list in network resources is obtained by extracting dimensions from
teleportation events. -/
theorem fresh_pair_dimensions_eq {D E : ℕ} (P : FiniteNetwork D E) (t : P.Transcript) :
    (P.resources t).freshPairDimensions
      = (P.events t).filterMap (fun e => match e with
          | .teleport n _ _ => some n
          | _ => none) := by
  induction P with
  | done D =>
      simp [FiniteNetwork.resources, FiniteNetwork.events, eventResources]
  | measure s I next ih =>
      simp only [FiniteNetwork.resources, FiniteNetwork.events, eventResources]
      have h := ih t.1 t.2
      simp only [FiniteNetwork.resources] at h
      rw [h]
      simp
  | send bits next ih =>
      simp only [FiniteNetwork.resources, FiniteNetwork.events, eventResources]
      have h := ih t
      simp only [FiniteNetwork.resources] at h
      rw [h]
      simp
  | teleport hn width fits next ih =>
      simp only [FiniteNetwork.resources, FiniteNetwork.events, eventResources]
      have h := ih t.1 t.2
      simp only [FiniteNetwork.resources] at h
      rw [h]
      simp

/-- A ledger of preshared pairs consumed, fresh pairs created, and total teleportation steps. -/
structure LoccEntanglementLedger where

  sharedEprUsed : ℕ

  eprCreated : ℕ

  teleportSteps : ℕ
  deriving DecidableEq

/-- The entanglement ledger populated from a party plan's preshared, fresh, and total
teleportation counts. -/
noncomputable def PartyPlan.entanglementLedger {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) : LoccEntanglementLedger :=
  { sharedEprUsed := pl.presharedCount t
    eprCreated := pl.freshCount t
    teleportSteps := pl.teleportCount t }

/-- The ledger's consumed preshared pairs and newly created pairs sum to its teleportation-step
count. -/
theorem entanglementLedger_law {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) :
    (pl.entanglementLedger t).sharedEprUsed + (pl.entanglementLedger t).eprCreated
      = (pl.entanglementLedger t).teleportSteps := by
  exact preshared_fresh_split (pl.actions t)

/-- An assumed bound on a party pair's preshared usage by its available supply is retained for
that party-plan transcript. -/
theorem entanglementLedger_supply {D E : ℕ} {P : FiniteNetwork D E} (pl : PartyPlan P)
    (t : P.Transcript) (sup : EPRSupply) (p q : Party)
    (h : pl.presharedUsed t p q ≤ sup.available p q) :
    pl.presharedUsed t p q ≤ sup.available p q := h

/-- The condition that no encoded word is a prefix of the word for a distinct message. -/
def PrefixFree {M : Type} (w : M → List Bool) : Prop :=
  ∀ a b, a ≠ b → ¬ List.IsPrefix (w a) (w b)

/-- The six nonempty Boolean words of lengths one and two, indexed by `Fin 6`. -/
def counterWords : Fin 6 → List Bool
  | 0 => [false]
  | 1 => [true]
  | 2 => [false, false]
  | 3 => [false, true]
  | 4 => [true, false]
  | 5 => [true, true]

/-- Every word in `counterWords` has length at most two. -/
theorem counterWords_length_le (i : Fin 6) : (counterWords i).length ≤ 2 := by
  fin_cases i <;> decide

/-- The six-word encoding `counterWords` is not prefix free. -/
theorem counterWords_not_prefixFree : ¬ PrefixFree counterWords := by
  intro h
  exact (h 0 2 (by decide)) (by simp [counterWords])

/-- The six messages indexing `counterWords` outnumber the `2 ^ 2` binary words of length two. -/
theorem counterWords_card_gt : 2 ^ 2 < Fintype.card (Fin 6) := by decide

/-- For nonnegative prior weights bounded by `p`, the success of a message guessing protocol on
a shared density operator is at most the message count times `p`. -/
theorem MessageGuessProtocol.messageCount_bound {X : Type} [Fintype X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (prior : X → ℝ) (p : ℝ)
    (hprior : ∀ x, 0 ≤ prior x) (hmax : ∀ x, prior x ≤ p) :
    P.success σ prior ≤ (Fintype.card M : ℝ) * p :=
  MessageGuessProtocol.success_le P σ hσ htrace prior p hprior hmax

end MeasurementNetworkLOCCDefs
