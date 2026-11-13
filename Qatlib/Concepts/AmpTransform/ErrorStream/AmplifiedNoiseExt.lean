/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.AmplifiedNoise
import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport

/-!
# Executable recovery with fresh error streams

`runWithFallback` combines continued-fraction candidates with a bounded verified pool, filters
them using fresh protected observations, and records all costs in `RecoveryTrace` and `Bill`.
The module relates these executable traces to finite Bernoulli distributions and to explicit
threshold sampling from fair-bit tapes.

`frontier1` collects the transport, identification, and resource results. Fixed noise can leave
distinct planted periods indistinguishable; under the stated legality and marking assumptions,
protected resampling instead yields the failure bound `B * pmax ^ t` and excludes a wrong
returned period.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `Multi.candidate_survival_probability`: exact survival probability from candidate separation.
* `actualFailureMass_le`: a public failure bound for executable fallback recovery.
* `Effective.roundsRun_fiber`: exact transport from fair tapes to Bernoulli rounds.
* `frontier1`: the combined recovery and resource package.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchArith.TransposeAccess.FinDist
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.FourierRecovery.ModularFourier
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

set_option autoImplicit false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib

/-- Resource counters for oracle queries, continued-fraction stages and work, table tests, and
source gates. -/
structure Bill where
  queries : ℕ
  cfStages : ℕ
  cfWork : ℕ
  tableTests : ℕ
  sourceGates : ℕ
  deriving DecidableEq, Repr

/-- The resource bill with every counter equal to zero. -/
def Bill.zero : Bill := ⟨0,0,0,0,0⟩

/-- Add two resource bills componentwise. -/
def Bill.add (a b : Bill) : Bill :=
  ⟨a.queries+b.queries, a.cfStages+b.cfStages, a.cfWork+b.cfWork,
    a.tableTests+b.tableTests, a.sourceGates+b.sourceGates⟩

/-- Collect the successful period candidates from the supplied labels and accumulate their
query, continued-fraction, and source-gate costs. -/
def collect {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ) :
    List (Fin N) → List ℕ × Bill
  | [] => ([], Bill.zero)
  | y::ys =>
    let a := aqAttempt h s M B y
    let tail := collect h s M B k ys
    (a.1.toList ++ tail.1,
      Bill.add ⟨k+a.2.1, a.2.2.1, a.2.2.2, 0, 3*k+2⟩ tail.2)

/-- The candidate list produced by `collect` equals `aqCandidateRecord`. -/
theorem collect_outputs {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) : (collect h s M B k xs).1 = aqCandidateRecord h s M B xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [collect, aqCandidateRecord, List.filterMap_cons, ih]
    cases ha : (aqAttempt h s M B y).1 <;> rfl

/-- The query counter of `collect` equals `aqCandidateRecordQueries`. -/
theorem collect_queries {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) :
    (collect h s M B k xs).2.queries = aqCandidateRecordQueries h s M B k xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [collect, Bill.add, aqCandidateRecordQueries, List.map_cons, List.sum_cons]
    rw [ih]
    rfl

/-- Candidate collection produces at most one entry per input label. -/
theorem collect_length {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) : (collect h s M B k xs).1.length ≤ xs.length := by
  rw [collect_outputs]
  exact List.length_filterMap_le _ _

/-- Read the supplied oracle locations, returning the set of locations marked true and the
number of queries. -/
def readRegister {N : ℕ} (h : Fin N → Bool) : List (Fin N) → Finset (Fin N) × ℕ
  | [] => (∅,0)
  | x::xs =>
    let tail := readRegister h xs
    (if h x then insert x tail.1 else tail.1, tail.2+1)

/-- Reading a list of locations uses exactly its length in oracle queries. -/
theorem readRegister_queries {N : ℕ} (h : Fin N → Bool) (xs : List (Fin N)) :
    (readRegister h xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [readRegister, List.length_cons] using! congrArg (·+1) ih

/-- A location belongs to the readout precisely when it occurs in the input list and its oracle
value is true. -/
theorem readRegister_mem {N : ℕ} (h : Fin N → Bool) (xs : List (Fin N)) (x : Fin N) :
    x ∈ (readRegister h xs).1 ↔ x ∈ xs ∧ h x = true := by
  induction xs with
  | nil => simp [readRegister]
  | cons y ys ih =>
    cases hy : h y <;> simp [readRegister, hy, ih] <;> aesop

/-- Check that each indexed site `s + r * q` lies in the register and the observed set,
recording one test per index. -/
def checkSites {N : ℕ} (obs : Finset (Fin N)) (s q : ℕ) : List ℕ → Bool × ℕ
  | [] => (true,0)
  | r::rs =>
    let tail := checkSites obs s q rs
    let bit := if h : s+r*q < N then decide ((⟨s+r*q,h⟩ : Fin N) ∈ obs) else false
    (bit && tail.1, tail.2+1)

/-- The site checker performs exactly one test per supplied index. -/
theorem checkSites_tests {N : ℕ} (obs : Finset (Fin N)) (s q : ℕ) (rs : List ℕ) :
    (checkSites obs s q rs).2 = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simpa only [checkSites, List.length_cons] using! congrArg (·+1) ih

/-- Filter period candidates by positivity, register bounds, and observed progression sites,
recording the number of tests. -/
def prune {N : ℕ} (obs : Finset (Fin N)) (s M : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([],0)
  | q::qs =>
    let checked := checkSites obs s q (List.range M)
    let tail := prune obs s M qs
    (if decide (0<q ∧ s+(M-1)*q<N) && checked.1 then q::tail.1 else tail.1,
      tail.2+checked.2+1)

/-- Pruning performs exactly `M + 1` tests per input candidate. -/
theorem prune_tests {N : ℕ} (obs : Finset (Fin N)) (s M : ℕ) (qs : List ℕ) :
    (prune obs s M qs).2 = qs.length*(M+1) := by
  induction qs with
  | nil => simp only [prune, List.length_nil, Nat.zero_mul]
  | cons q qs ih =>
    simp only [prune, checkSites_tests, List.length_range, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Pruning cannot increase the length of the candidate list. -/
theorem prune_length {N : ℕ} (obs : Finset (Fin N)) (s M : ℕ) (qs : List ℕ) :
    (prune obs s M qs).1.length ≤ qs.length := by
  induction qs with
  | nil => exact Nat.le_refl 0
  | cons q qs ih =>
    simp only [prune]
    split <;> simp only [List.length_cons] <;> omega

/-- Read each fresh oracle table and successively prune the candidate list, accumulating queries
and table tests. -/
def freshRounds {N : ℕ} (s M : ℕ) :
    List (Fin N → Bool) → List ℕ → List ℕ × Bill
  | [], qs => (qs,Bill.zero)
  | h::hs, qs =>
    let observed := readRegister h (List.finRange N)
    let filtered := prune observed.1 s M qs
    let tail := freshRounds s M hs filtered.1
    (tail.1, Bill.add ⟨observed.2,0,0,filtered.2,0⟩ tail.2)

/-- Return a value when the list is nonempty and all its entries agree, and return `none`
otherwise. -/
def uniqueOutput : List ℕ → Option ℕ
  | [] => none
  | q::qs => if qs.all (fun r => r == q) then some q else none

/-- Collect period candidates, filter them through fresh observations, and return their common
value with the accumulated resource bill. -/
def run {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) : Option ℕ × Bill :=
  let first := collect h s M B k labels
  let second := freshRounds s M observations first.1
  (uniqueOutput second.1, first.2.add second.2)

/-- Fresh filtering uses exactly `N` queries for each observation table. -/
theorem freshRounds_queries {N : ℕ} (s M : ℕ)
    (observations : List (Fin N → Bool)) (qs : List ℕ) :
    (freshRounds s M observations qs).2.queries = observations.length*N := by
  induction observations generalizing qs with
  | nil => simp only [freshRounds, Bill.zero, List.length_nil, Nat.zero_mul]
  | cons h hs ih =>
    simp only [freshRounds, Bill.add, readRegister_queries, List.length_finRange,
      ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Fresh filtering cannot increase the length of the initial candidate list. -/
theorem freshRounds_length {N : ℕ} (s M : ℕ)
    (observations : List (Fin N → Bool)) (qs : List ℕ) :
    (freshRounds s M observations qs).1.length ≤ qs.length := by
  induction observations generalizing qs with
  | nil => exact Nat.le_refl _
  | cons h hs ih =>
    exact (ih _).trans (prune_length (readRegister h (List.finRange N)).1 s M qs)

/-- The table-test count is at most the number of observations times the initial candidate count
times `M + 1`. -/
theorem freshRounds_tests {N : ℕ} (s M : ℕ)
    (observations : List (Fin N → Bool)) (qs : List ℕ) :
    (freshRounds s M observations qs).2.tableTests ≤
      observations.length*qs.length*(M+1) := by
  induction observations generalizing qs with
  | nil => simp only [freshRounds, Bill.zero, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons h hs ih =>
    let obs := (readRegister h (List.finRange N)).1
    have htail := ih (prune obs s M qs).1
    have hlen := prune_length obs s M qs
    have hmul := Nat.mul_le_mul_right (M+1) (Nat.mul_le_mul_left hs.length hlen)
    have hh := htail.trans hmul
    change (prune obs s M qs).2 +
      (freshRounds s M hs (prune obs s M qs).1).2.tableTests ≤ _
    rw [prune_tests, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_mul]
    omega

/-- The total query count is the candidate-record query count plus `N` queries per fresh
observation. -/
theorem run_queries {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) :
    (run h s M B k labels observations).2.queries =
      aqCandidateRecordQueries h s M B k labels + observations.length*N := by
  exact congrArg₂ (·+·) (collect_queries h s M B k labels)
    (freshRounds_queries s M observations (collect h s M B k labels).1)

/-- The query count is at most `labels.length * (k + 3) + observations.length * N`. -/
theorem run_query_cap {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) :
    (run h s M B k labels observations).2.queries ≤
      labels.length*(k+3)+observations.length*N := by
  rw [run_queries]
  exact Nat.add_le_add_right (aqCandidateRecordQueries_cap h s M B k labels) _

/-- The site checker returns true exactly when every requested progression site is in bounds and
observed. -/
theorem checkSites_true {N : ℕ} (obs : Finset (Fin N)) (s q : ℕ) (rs : List ℕ) :
    (checkSites obs s q rs).1 = true ↔
      ∀ r ∈ rs, ∃ h : s+r*q<N, (⟨s+r*q,h⟩ : Fin N) ∈ obs := by
  induction rs with
  | nil => simp [checkSites]
  | cons r rs ih =>
    by_cases hr : s+r*q<N
    · simp [checkSites, hr, ih]
    · simp [checkSites, hr]

/-- For a nonempty progression within the register, checking its first `M` sites is equivalent
to candidate consistency. -/
theorem checkSites_consistent {N : ℕ} (obs : Finset (Fin N)) (s M q : ℕ)
    (hM : 0 < M) (hb : s+(M-1)*q<N) :
    (checkSites obs s q (List.range M)).1 = true ↔ aqCandidateConsistent N s M q obs := by
  rw [checkSites_true]
  constructor
  · intro hall x hx
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨r,hr,he⟩ := hx
    obtain ⟨hg,hobs⟩ := hall r (List.mem_range.mpr (Finset.mem_range.mp hr))
    have heq : (⟨s+r*q,hg⟩ : Fin N) = x := Fin.ext he.symm
    rw [heq] at hobs
    exact hobs
  · intro hconsistent r hr
    have hg := aqProgression_index_lt N s M q r hM hb (List.mem_range.mp hr)
    refine ⟨hg, hconsistent ?_⟩
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, Finset.mem_range.mpr (List.mem_range.mp hr), rfl⟩

/-- Every collected candidate is positive and its last progression site lies within the
register. -/
theorem collect_legal {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) (q : ℕ) (hq : q ∈ (collect h s M B k xs).1) :
    0<q ∧ s+(M-1)*q<N := by
  rw [collect_outputs] at hq
  have hv := aqCandidateRecord_verified h s M B xs q hq
  unfold aqVerify at hv
  split at hv
  · rename_i hlegal
    exact ⟨hlegal.1, hlegal.2.2.2⟩
  · simp at hv

/-- Candidate collection charges exactly `3 * k + 2` source gates per input label. -/
theorem collect_source_gates {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) :
    (collect h s M B k xs).2.sourceGates = xs.length*(3*k+2) := by
  induction xs with
  | nil => simp only [collect, Bill.zero, List.length_nil, Nat.zero_mul]
  | cons y ys ih =>
    simp only [collect, Bill.add, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- With the amplified round count, the source-gate bill is the number of labels times the gate
count of `aqCircuit`. -/
theorem collect_actual_gates (N : ℕ) (hN : 0<N) (T : ℕ)
    (C : Finset (Fin N)) (h : Fin N → Bool) (s M B : ℕ) (xs : List (Fin N)) :
    (collect h s M B (aqRounds N T) xs).2.sourceGates =
      xs.length*GateCount (aqCircuit N hN T) := by
  rw [collect_source_gates, (aq_error_word_counts N hN T C).2.2.2.1]

/-- A recovery attempt uses at most `cfDepth N + 1` continued-fraction stages and has the stated
triangular work count. -/
theorem attempt_classical {N : ℕ} (h : Fin N → Bool) (s M B : ℕ) (y : Fin N) :
    (aqAttempt h s M B y).2.2.1 ≤ cfDepth N+1 ∧
      (aqAttempt h s M B y).2.2.2 = (cfDepth N+1)*(cfDepth N+2)/2 := by
  have hN : N≠0 := by have hy := y.isLt; omega
  have hd := continued_fraction_bad_output_soundness_and_work B N y.val
  have hg : (cfRationalDecode B N y.val).2.2 = (cfDepth N+1)*(cfDepth N+2)/2 := by
    simp only [cfRationalDecode, if_neg hN, cfGenerationWork_eq]
  unfold aqAttempt
  (try dsimp only)
  split <;> exact ⟨hd.1,hg⟩

/-- Candidate collection has the stated linear stage bound and triangular work count, and
performs no table tests. -/
theorem collect_classical {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ) (xs : List (Fin N)) :
    (collect h s M B k xs).2.cfStages ≤ xs.length*(cfDepth N+1) ∧
      (collect h s M B k xs).2.cfWork = xs.length*((cfDepth N+1)*(cfDepth N+2)/2) ∧
      (collect h s M B k xs).2.tableTests = 0 := by
  induction xs with
  | nil => simp only [collect, Bill.zero, List.length_nil, Nat.zero_mul, Nat.le_refl, and_self]
  | cons y ys ih =>
    obtain ⟨hs,hw⟩ := attempt_classical h s M B y
    obtain ⟨htail,hwork,htests⟩ := ih
    simp only [collect, Bill.add, List.length_cons, Nat.zero_add]
    refine ⟨?_,?_,?_⟩
    · rw [Nat.add_mul ys.length 1 (cfDepth N+1), Nat.one_mul]
      omega
    · rw [hw,hwork]
      rw [Nat.add_mul ys.length 1 ((cfDepth N+1)*(cfDepth N+2)/2), Nat.one_mul]
      omega
    · exact htests

/-- Fresh filtering charges no continued-fraction stages, continued-fraction work, or source
gates. -/
theorem freshRounds_extra {N : ℕ} (s M : ℕ) (observations : List (Fin N → Bool)) (qs : List ℕ) :
    (freshRounds s M observations qs).2.cfStages = 0 ∧
      (freshRounds s M observations qs).2.cfWork = 0 ∧
      (freshRounds s M observations qs).2.sourceGates = 0 := by
  induction observations generalizing qs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons h hs ih =>
    obtain ⟨ht,hw,hg⟩ := ih (prune (readRegister h (List.finRange N)).1 s M qs).1
    simp only [freshRounds, Bill.add, ht,hw,hg, Nat.zero_add, and_self]

/-- Pruning equals list filtering by the legality check and the observed-site checker. -/
theorem prune_filter {N : ℕ} (obs : Finset (Fin N)) (s M : ℕ) (qs : List ℕ) :
    (prune obs s M qs).1 = qs.filter
      (fun q => decide (0<q ∧ s+(M-1)*q<N) && (checkSites obs s q (List.range M)).1) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [prune, List.filter_cons, ih]

/-- A candidate survives pruning exactly when it was present, is legal, and passes the site
checker. -/
theorem prune_mem {N : ℕ} (obs : Finset (Fin N)) (s M q : ℕ) (qs : List ℕ) :
    q ∈ (prune obs s M qs).1 ↔
      q ∈ qs ∧ (0<q ∧ s+(M-1)*q<N) ∧ (checkSites obs s q (List.range M)).1 = true := by
  rw [prune_filter]
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- For legal candidates and positive progression length, pruning retains exactly the candidates
consistent with the observation. -/
theorem prune_consistent {N : ℕ} (obs : Finset (Fin N)) (s M q : ℕ) (qs : List ℕ)
    (hM : 0<M) (hlegal : ∀ r ∈ qs, 0<r ∧ s+(M-1)*r<N) :
    q ∈ (prune obs s M qs).1 ↔ q ∈ qs ∧ aqCandidateConsistent N s M q obs := by
  rw [prune_mem]
  constructor
  · rintro ⟨hq,hleg,hcheck⟩
    exact ⟨hq,(checkSites_consistent obs s M q hM hleg.2).mp hcheck⟩
  · rintro ⟨hq,hcon⟩
    exact ⟨hq,hlegal q hq,(checkSites_consistent obs s M q hM (hlegal q hq).2).mpr hcon⟩

/-- Reading the entire register returns exactly the locations where the oracle is true. -/
theorem readRegister_all {N : ℕ} (h : Fin N → Bool) :
    (readRegister h (List.finRange N)).1 = Finset.univ.filter (fun x => h x = true) := by
  ext x
  simp only [readRegister_mem, List.mem_finRange, true_and, Finset.mem_filter, Finset.mem_univ]

/-- Fresh filtering preserves positivity and register bounds of the initial candidates. -/
theorem freshRounds_legal {N : ℕ} (s M : ℕ) (observations : List (Fin N → Bool))
    (qs : List ℕ) (hlegal : ∀ q ∈ qs, 0<q ∧ s+(M-1)*q<N) :
    ∀ q ∈ (freshRounds s M observations qs).1, 0<q ∧ s+(M-1)*q<N := by
  induction observations generalizing qs with
  | nil => exact hlegal
  | cons h hs ih =>
    exact ih _ (fun q hq => ((prune_mem _ s M q qs).mp hq).2.1)

/-- For legal candidates and positive progression length, survival means initial membership and
consistency with every fresh table. -/
theorem freshRounds_mem {N : ℕ} (s M q : ℕ) (observations : List (Fin N → Bool))
    (qs : List ℕ) (hM : 0<M) (hlegal : ∀ r ∈ qs, 0<r ∧ s+(M-1)*r<N) :
    q ∈ (freshRounds s M observations qs).1 ↔
      q ∈ qs ∧ ∀ h ∈ observations,
        aqCandidateConsistent N s M q (readRegister h (List.finRange N)).1 := by
  induction observations generalizing qs with
  | nil => simp only [freshRounds, List.not_mem_nil, false_implies, forall_const, and_true]
  | cons h hs ih =>
    change q ∈ (freshRounds s M hs (prune (readRegister h (List.finRange N)).1 s M qs).1).1 ↔ _
    rw [ih _ (fun r hr => ((prune_mem _ s M r qs).mp hr).2.1)]
    rw [prune_consistent _ s M q qs hM hlegal]
    simp only [List.forall_mem_cons, and_assoc]

/-- The list selector returns `some q` exactly when `q` occurs and every entry equals `q`. -/
theorem uniqueOutput_spec (qs : List ℕ) (q : ℕ) :
    uniqueOutput qs = some q ↔ q ∈ qs ∧ ∀ r ∈ qs, r=q := by
  cases qs with
  | nil => simp only [uniqueOutput, List.not_mem_nil, false_and, reduceCtorEq]
  | cons a rest =>
    rw [List.forall_mem_cons]
    simp only [uniqueOutput, List.mem_cons]
    by_cases ha : rest.all (fun r => r == a) = true
    · have hall : ∀ r ∈ rest, r=a := by
        simpa only [List.all_eq_true, beq_iff_eq] using! ha
      rw [if_pos ha, Option.some.injEq]
      constructor
      · intro he
        subst q
        exact ⟨Or.inl rfl,rfl,hall⟩
      · rintro ⟨_,he,_⟩
        exact he
    · rw [if_neg ha]
      constructor
      · intro he
        cases he
      · rintro ⟨_,he,hall⟩
        exfalso
        apply ha
        simp only [List.all_eq_true, beq_iff_eq]
        intro r hr
        exact (hall r hr).trans he.symm

/-- The list selector returns `some q` exactly when the set of list entries is the singleton
`{q}`. -/
theorem uniqueOutput_eq_some_iff (qs : List ℕ) (q : ℕ) :
    uniqueOutput qs = some q ↔ qs.toFinset = {q} := by
  rw [uniqueOutput_spec, Finset.eq_singleton_iff_unique_mem]
  simp only [List.mem_toFinset]

namespace Separation

open scoped Classical

/-- A progression of length at least two contains its in-bounds second site `s + P`. -/
theorem second_site_mem (N s M P : ℕ) (hM : 2 ≤ M) (hsp : s + P < N) :
    (⟨s + P, hsp⟩ : Fin N) ∈ aqProgressionSet N s M P := by
  simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨1, Finset.mem_range.mpr (by omega), by simp⟩

/-- If the site `s + P` lies in a progression with the same start and positive `P`, its step `Q`
is at most `P`. -/
theorem period_le_of_second_site (N s M P Q : ℕ) (hP : 0 < P) (hsp : s + P < N)
    (hx : (⟨s + P, hsp⟩ : Fin N) ∈ aqProgressionSet N s M Q) : Q ≤ P := by
  simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨r, _, hr⟩ := hx
  have he : P = r * Q := Nat.add_left_cancel hr
  have hpos : 1 ≤ r := by
    by_contra hn
    have hz : r = 0 := by omega
    rw [hz, zero_mul] at he
    omega
  have hm := Nat.mul_le_mul_right Q hpos
  simpa only [one_mul, ← he] using! hm

/-- Two legal positive-step progressions with the same start and length at least two have equal
steps if their sets coincide. -/
theorem progression_period_injective (N s M P Q : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hQ : 0 < Q)
    (hbP : s + (M - 1) * P < N) (hbQ : s + (M - 1) * Q < N)
    (hsets : aqProgressionSet N s M P = aqProgressionSet N s M Q) : P = Q := by
  have hsp : s + P < N := by
    simpa only [one_mul] using!
      aqProgression_index_lt N s M P 1 (by omega) hbP (by omega)
  have hsq : s + Q < N := by
    simpa only [one_mul] using!
      aqProgression_index_lt N s M Q 1 (by omega) hbQ (by omega)
  have hxP := second_site_mem N s M P hM hsp
  have hxQ := second_site_mem N s M Q hM hsq
  rw [hsets] at hxP
  rw [← hsets] at hxQ
  exact Nat.le_antisymm
    (period_le_of_second_site N s M Q P hQ hsq hxQ)
    (period_le_of_second_site N s M P Q hP hsp hxP)

/-- Distinct legal positive periods have positive candidate separation when the progression
length is at least two. -/
theorem candidate_separation_pos (N s M P Q : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hQ : 0 < Q)
    (hbP : s + (M - 1) * P < N) (hbQ : s + (M - 1) * Q < N)
    (hQP : Q ≠ P) : 0 < aqCandidateSeparation N s M P Q := by
  by_contra hn
  have hz : (aqProgressionSet N s M Q \ aqProgressionSet N s M P).card = 0 := by
    change ¬0 < (aqProgressionSet N s M Q \ aqProgressionSet N s M P).card at hn
    omega
  have hsub : aqProgressionSet N s M Q ⊆ aqProgressionSet N s M P :=
    Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hz)
  have hcP := aqProgression_card N s M P (by omega) hP hbP
  have hcQ := aqProgression_card N s M Q (by omega) hQ hbQ
  have hsets : aqProgressionSet N s M Q = aqProgressionSet N s M P :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hQP (progression_period_injective N s M Q P hM hQ hP hbQ hbP hsets)

/-- A progression of length zero is empty. -/
theorem empty_progression (N s P : ℕ) : aqProgressionSet N s 0 P = ∅ := by
  ext x
  simp [aqProgressionSet]

/-- A progression of length one is independent of its period parameter. -/
theorem singleton_period_irrelevant (N s P Q : ℕ) :
    aqProgressionSet N s 1 P = aqProgressionSet N s 1 Q := by
  ext x
  simp [aqProgressionSet]

/-- Candidate separation vanishes for progressions of length zero. -/
theorem zero_separation_at_zero_length (N s P Q : ℕ) :
    aqCandidateSeparation N s 0 P Q = 0 := by
  simp [aqCandidateSeparation, empty_progression]

/-- Candidate separation vanishes for progressions of length one. -/
theorem zero_separation_at_singleton (N s P Q : ℕ) :
    aqCandidateSeparation N s 1 P Q = 0 := by
  unfold aqCandidateSeparation
  rw [singleton_period_irrelevant N s Q P, Finset.sdiff_self, Finset.card_empty]

end Separation

namespace Multi

noncomputable section
open scoped Classical BigOperators

/-- A family of `t` Boolean noise streams on a register of size `N`. -/
abbrev RawRounds (N t : ℕ) := Fin t → (Fin N → Bool)
/-- A family of `t` observed subsets of a register of size `N`. -/
abbrev Observations (N t : ℕ) := Fin t → Finset (Fin N)

/-- The product distribution of `t` independent Bernoulli noise streams with parameter `p`. -/
def roundsLaw (N t : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FinDist (RawRounds N t) where
  prob σ := (bernoulliStreamLaw N p hp hp1).probOf σ
  nonneg σ := Finset.prod_nonneg fun i _ =>
    (bernoulliStreamLaw N p hp hp1).nonneg (σ i)
  sum_one := (bernoulliStreamLaw N p hp hp1).sum_probOf t

/-- Overlay the planted progression on each raw noise stream to obtain the observed marked sets. -/
def observedRounds (N s M P t : ℕ) (σ : RawRounds N t) : Observations N t :=
  fun i => aqFreshMarked N s M P (σ i)

/-- Successively retain candidates consistent with every observed set in a list. -/
def filterList (N s M : ℕ) : List (Finset (Fin N)) → Finset ℕ → Finset ℕ
  | [], cands => cands
  | obs::rest, cands => filterList N s M rest (aqFreshCompatible N s M cands obs)

/-- The candidate set remaining after filtering against all `t` observations. -/
def survivors (N s M t : ℕ) (cands : Finset ℕ) (obs : Observations N t) : Finset ℕ :=
  filterList N s M (List.ofFn obs) cands

/-- Return the sole element of a singleton candidate set, and return `none` otherwise. -/
def uniqueOutput (cands : Finset ℕ) : Option ℕ :=
  match cands.toList with
  | [Q] => some Q
  | _ => none

/-- Select the unique surviving candidate after all observations have been processed. -/
def output (N s M t : ℕ) (cands : Finset ℕ) (obs : Observations N t) : Option ℕ :=
  uniqueOutput (survivors N s M t cands obs)

/-- The condition that candidate `Q` is consistent with every observation. -/
def allConsistent (N s M t Q : ℕ) (obs : Observations N t) : Prop :=
  ∀ i : Fin t, aqCandidateConsistent N s M Q (obs i)

/-- A candidate survives list filtering exactly when it was initially present and is consistent
with every listed observation. -/
theorem mem_filterList (N s M Q : ℕ) (obs : List (Finset (Fin N))) :
    ∀ cands, Q ∈ filterList N s M obs cands ↔
      Q ∈ cands ∧ ∀ o ∈ obs, aqCandidateConsistent N s M Q o := by
  induction obs with
  | nil => intro cands; simp [filterList]
  | cons o rest ih =>
      intro cands
      simp [filterList, ih, aqFreshCompatible, and_assoc]

/-- A candidate belongs to the survivor set exactly when it was initially present and is
consistent with all rounds. -/
theorem mem_survivors (N s M t Q : ℕ) (cands : Finset ℕ)
    (obs : Observations N t) :
    Q ∈ survivors N s M t cands obs ↔ Q ∈ cands ∧ allConsistent N s M t Q obs := by
  rw [survivors, mem_filterList]
  constructor
  · rintro ⟨hQ,hall⟩
    refine ⟨hQ,?_⟩
    intro i
    exact hall (obs i) ((List.mem_ofFn' obs (obs i)).mpr ⟨i,rfl⟩)
  · rintro ⟨hQ,hall⟩
    refine ⟨hQ,?_⟩
    intro o ho
    obtain ⟨i,he⟩ := (List.mem_ofFn' obs o).mp ho
    rw [← he]
    exact hall i

/-- The set selector returns `some Q` exactly when the candidate set equals `{Q}`. -/
theorem uniqueOutput_eq_some_iff (cands : Finset ℕ) (Q : ℕ) :
    uniqueOutput cands = some Q ↔ cands = {Q} := by
  constructor
  · intro h
    cases hs : cands.toList with
    | nil => simp [uniqueOutput,hs] at h
    | cons a rest =>
        cases rest with
        | nil =>
            have ha : a = Q := Option.some.inj (by simpa only [uniqueOutput,hs] using! h)
            subst a
            exact Finset.toList_eq_singleton_iff.mp hs
        | cons b bs => simp [uniqueOutput,hs] at h
  · intro h
    rw [h]
    simp [uniqueOutput]

/-- The planted period survives all protected observations whenever it belongs to the initial
candidate set. -/
theorem true_survives (N s M P t : ℕ) (cands : Finset ℕ) (hP : P ∈ cands)
    (σ : RawRounds N t) :
    P ∈ survivors N s M t cands (observedRounds N s M P t σ) := by
  apply (mem_survivors N s M t P cands _).mpr
  exact ⟨hP, fun i => aq_true_period_always_consistent N s M P (σ i)⟩

/-- If the planted period survives, the survivor set fails to be its singleton exactly when a
false initial candidate is consistent with every round. -/
theorem survivors_ne_singleton_iff (N s M P t : ℕ) (cands : Finset ℕ)
    (obs : Observations N t) (hP : P ∈ survivors N s M t cands obs) :
    survivors N s M t cands obs ≠ {P} ↔
      ∃ Q ∈ cands \ {P}, allConsistent N s M t Q obs := by
  constructor
  · intro hne
    by_contra hnone
    apply hne
    ext Q
    constructor
    · intro hQ
      obtain ⟨hc,hall⟩ := (mem_survivors N s M t Q cands obs).mp hQ
      by_cases he : Q = P
      · simp only [he,Finset.mem_singleton]
      · exact False.elim (hnone ⟨Q,Finset.mem_sdiff.mpr
          ⟨hc,by simpa only [Finset.mem_singleton] using! he⟩,hall⟩)
    · intro hQ
      have he : Q = P := Finset.mem_singleton.mp hQ
      exact he.symm ▸ hP
  · rintro ⟨Q,hQ,hall⟩ he
    have hsur := (mem_survivors N s M t Q cands obs).mpr
      ⟨(Finset.mem_sdiff.mp hQ).1,hall⟩
    rw [he] at hsur
    exact (Finset.mem_sdiff.mp hQ).2 hsur

/-- When the planted period is initially present, recovery fails exactly when some false
candidate remains consistent with all protected observations. -/
theorem output_failure_iff (N s M P t : ℕ) (cands : Finset ℕ)
    (hP : P ∈ cands) (σ : RawRounds N t) :
    output N s M t cands (observedRounds N s M P t σ) ≠ some P ↔
      ∃ Q ∈ cands \ {P},
        allConsistent N s M t Q (observedRounds N s M P t σ) := by
  rw [output, ne_eq, uniqueOutput_eq_some_iff]
  exact survivors_ne_singleton_iff N s M P t cands _ (true_survives N s M P t cands hP σ)

/-- Recovery returns the planted period if it is initially present and no false candidate is
consistent with every protected observation. -/
theorem output_true_of_no_false (N s M P t : ℕ) (cands : Finset ℕ)
    (hP : P ∈ cands) (σ : RawRounds N t)
    (hfalse : ¬ ∃ Q ∈ cands \ {P},
      allConsistent N s M t Q (observedRounds N s M P t σ)) :
    output N s M t cands (observedRounds N s M P t σ) = some P := by
  by_contra h
  exact hfalse ((output_failure_iff N s M P t cands hP σ).mp h)

/-- The indicator of a finite conjunction equals the product of its individual indicators. -/
private theorem indicator_forall {t : ℕ} (C : Fin t → Prop) [DecidablePred C] :
    (if ∀ i, C i then (1 : ℝ) else 0) = ∏ i : Fin t, (if C i then (1 : ℝ) else 0) := by
  by_cases hall : ∀ i, C i
  · rw [if_pos hall]
    symm
    exact Finset.prod_eq_one fun i _ => if_pos (hall i)
  · rw [if_neg hall]
    obtain ⟨i,hi⟩ := not_forall.mp hall
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Under independent Bernoulli rounds, the survival probability of candidate `Q` is `p` raised
to `t` times its separation from the planted period. -/
theorem candidate_survival_probability (N s M P Q t : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ σ : RawRounds N t, (roundsLaw N t p hp hp1).prob σ *
      (if allConsistent N s M t Q (observedRounds N s M P t σ) then 1 else 0)) =
        p ^ (t * aqCandidateSeparation N s M P Q) := by
  have hi (σ : RawRounds N t) :
      (if allConsistent N s M t Q (observedRounds N s M P t σ) then (1 : ℝ) else 0) =
        ∏ i : Fin t, (if aqCandidateConsistent N s M Q
          (aqFreshMarked N s M P (σ i)) then (1 : ℝ) else 0) := by
    by_cases hall : allConsistent N s M t Q (observedRounds N s M P t σ)
    · rw [if_pos hall]
      symm
      exact Finset.prod_eq_one fun i _ => if_pos (hall i)
    · rw [if_neg hall]
      have hnot : ¬ ∀ i : Fin t,
          aqCandidateConsistent N s M Q (aqFreshMarked N s M P (σ i)) := hall
      obtain ⟨i,hi⟩ := not_forall.mp hnot
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  calc
    (∑ σ : RawRounds N t, (roundsLaw N t p hp hp1).prob σ *
        (if allConsistent N s M t Q (observedRounds N s M P t σ) then 1 else 0)) =
        ∑ σ : RawRounds N t, (bernoulliStreamLaw N p hp hp1).probOf σ *
          ∏ i : Fin t, (if aqCandidateConsistent N s M Q
            (aqFreshMarked N s M P (σ i)) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [hi]
      rfl
    _ = ∏ i : Fin t, ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        (if aqCandidateConsistent N s M Q (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) :=
      FinDist.expect_prod (bernoulliStreamLaw N p hp hp1)
        (fun (_i : Fin t) (σ : Fin N → Bool) =>
          if aqCandidateConsistent N s M Q (aqFreshMarked N s M P σ) then (1 : ℝ) else 0)
    _ = ∏ _i : Fin t, p ^ aqCandidateSeparation N s M P Q := by
      apply Finset.prod_congr rfl
      intro i _
      exact aq_fresh_consistency_probability N s M P Q p hp hp1
    _ = (p ^ aqCandidateSeparation N s M P Q) ^ t := by simp
    _ = p ^ (t * aqCandidateSeparation N s M P Q) := by
      simpa only [Nat.mul_comm] using!
        (pow_mul p (aqCandidateSeparation N s M P Q) t).symm

/-- The indicator of a finite union of events is bounded by the sum of their indicators. -/
private theorem union_indicator_le (D : Finset ℕ) (C : ℕ → Prop) [DecidablePred C] :
    (if ∃ Q ∈ D, C Q then (1 : ℝ) else 0) ≤
      ∑ Q ∈ D, (if C Q then (1 : ℝ) else 0) := by
  by_cases hex : ∃ Q ∈ D, C Q
  · obtain ⟨Q,hQ,hC⟩ := hex
    rw [if_pos ⟨Q,hQ,hC⟩]
    have h := Finset.single_le_sum
      (f := fun R => if C R then (1 : ℝ) else 0)
      (fun R _ => by (try dsimp only); split <;> norm_num) hQ
    simpa only [if_pos hC] using! h
  · rw [if_neg hex]
    exact Finset.sum_nonneg fun Q _ => by split <;> norm_num

/-- The probability that protected fresh-observation filtering fails to return the planted
period. -/
def failureMass (N s M P t : ℕ) (cands : Finset ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  ∑ σ : RawRounds N t, (roundsLaw N t p hp hp1).prob σ *
    (if output N s M t cands (observedRounds N s M P t σ) ≠ some P then 1 else 0)

/-- If the planted period is initially present and `p ≤ pmax < 1`, failure mass is bounded by
the sum of the false-candidate survival bounds. -/
theorem failureMass_le (N s M P t : ℕ) (cands : Finset ℕ) (hP : P ∈ cands)
    (p pmax : ℝ) (hp : 0 ≤ p) (hpp : p ≤ pmax) (hmax : pmax < 1) :
    failureMass N s M P t cands p hp (le_trans hpp hmax.le) ≤
      ∑ Q ∈ cands \ {P}, pmax ^ (t * aqCandidateSeparation N s M P Q) := by
  let law := roundsLaw N t p hp (le_trans hpp hmax.le)
  have hpoint (σ : RawRounds N t) :
      (if output N s M t cands (observedRounds N s M P t σ) ≠ some P then (1 : ℝ) else 0) ≤
        ∑ Q ∈ cands \ {P},
          (if allConsistent N s M t Q (observedRounds N s M P t σ) then (1 : ℝ) else 0) := by
    simpa only [output_failure_iff N s M P t cands hP σ] using!
      (union_indicator_le (cands \ {P})
        (fun Q => allConsistent N s M t Q (observedRounds N s M P t σ)))
  calc
    failureMass N s M P t cands p hp (le_trans hpp hmax.le) =
        ∑ σ : RawRounds N t, law.prob σ *
          (if output N s M t cands (observedRounds N s M P t σ) ≠ some P then 1 else 0) := rfl
    _ ≤ ∑ σ : RawRounds N t, law.prob σ *
        ∑ Q ∈ cands \ {P},
          (if allConsistent N s M t Q (observedRounds N s M P t σ) then (1 : ℝ) else 0) := by
      exact Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hpoint σ) (law.nonneg σ)
    _ = ∑ Q ∈ cands \ {P}, ∑ σ : RawRounds N t, law.prob σ *
        (if allConsistent N s M t Q (observedRounds N s M P t σ) then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ Q ∈ cands \ {P}, p ^ (t * aqCandidateSeparation N s M P Q) := by
      apply Finset.sum_congr rfl
      intro Q _
      exact candidate_survival_probability N s M P Q t p hp (le_trans hpp hmax.le)
    _ ≤ ∑ Q ∈ cands \ {P}, pmax ^ (t * aqCandidateSeparation N s M P Q) := by
      exact Finset.sum_le_sum fun Q _ => pow_le_pow_left₀ hp hpp _

end
end Multi

namespace RawNoise

noncomputable section
open scoped Classical BigOperators

/-- The set of true noise locations outside the protected set `A`. -/
def noiseOutside {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun i => i ∉ A ∧ σ i = true

/-- The condition that a bit agrees with membership in `G` outside `A`, with no restriction on
sites in `A`. -/
def siteOK {N : ℕ} (A G : Finset (Fin N)) (i : Fin N) (b : Bool) : Prop :=
  i ∈ A ∨ (b = true ↔ i ∈ G)

/-- For disjoint `A` and `G`, the outside-noise set equals `G` exactly when every site satisfies
`siteOK`. -/
theorem outside_eq_iff {N : ℕ} (A G : Finset (Fin N)) (σ : Fin N → Bool)
    (hAG : Disjoint A G) :
    noiseOutside A σ = G ↔ ∀ i, siteOK A G i (σ i) := by
  constructor
  · intro he i
    by_cases hi : i ∈ A
    · exact Or.inl hi
    · right
      have hm := Finset.ext_iff.mp he i
      simpa [noiseOutside, hi] using! hm
  · intro hall
    ext i
    by_cases hi : i ∈ A
    · have hg : i ∉ G := fun h => Finset.disjoint_left.mp hAG hi h
      simp [noiseOutside, hi, hg]
    · have hm := (hall i).resolve_left hi
      simpa [noiseOutside, hi] using! hm

/-- A product of finitely many indicators equals the indicator that all their predicates hold. -/
theorem product_indicator {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] :
    (∏ i, if P i then (1 : ℝ) else 0) = if ∀ i, P i then 1 else 0 := by
  by_cases hall : ∀ i, P i
  · rw [if_pos hall]
    apply Finset.prod_eq_one
    intro i _
    exact if_pos (hall i)
  · rw [if_neg hall]
    obtain ⟨i, hi⟩ := not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The Bernoulli expectation of `siteOK` is one on `A`, `p` on `G` outside `A`, and `1 - p`
elsewhere. -/
theorem site_expectation {N : ℕ} (A G : Finset (Fin N)) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin N) :
    (∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b *
      (if siteOK A G i b then 1 else 0)) =
      if i ∈ A then 1 else if i ∈ G then p else 1 - p := by
  by_cases hi : i ∈ A
  · simp [siteOK, bernoulliSiteLaw, hi]
  · by_cases hg : i ∈ G <;>
      simp [siteOK, bernoulliSiteLaw, hi, hg]

/-- For disjoint `A` and `G`, the product of site weights is `p ^ G.card * (1 - p) ^ (N - A.card
- G.card)`. -/
theorem site_weight_product {N : ℕ} (A G : Finset (Fin N)) (p : ℝ)
    (hAG : Disjoint A G) :
    (∏ i : Fin N, if i ∈ A then 1 else if i ∈ G then p else 1 - p) =
      p ^ G.card * (1 - p) ^ (N - A.card - G.card) := by
  let D : Finset (Fin N) := Finset.univ \ (A ∪ G)
  have hfactor (i : Fin N) :
      (if i ∈ A then 1 else if i ∈ G then p else 1 - p) =
        (if i ∈ G then p else 1) * (if i ∈ D then 1 - p else 1) := by
    by_cases hi : i ∈ A
    · have hg : i ∉ G := fun h => Finset.disjoint_left.mp hAG hi h
      simp [hi, hg, D]
    · by_cases hg : i ∈ G <;> simp [hi, hg, D]
  have hc : D.card = N - A.card - G.card := by
    dsimp only [D]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_union_of_disjoint hAG]
    omega
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
  simp only [Finset.prod_const, hc]

/-- For disjoint `A` and `G`, the probability that outside noise equals `G` has the
corresponding Bernoulli subset weight. -/
theorem raw_overlay_fiber_mass (N : ℕ) (A G : Finset (Fin N)) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hAG : Disjoint A G) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if noiseOutside A σ = G then 1 else 0)) =
      p ^ G.card * (1 - p) ^ (N - A.card - G.card) := by
  have hind (σ : Fin N → Bool) :
      (if noiseOutside A σ = G then (1 : ℝ) else 0) =
        ∏ i, if siteOK A G i (σ i) then 1 else 0 := by
    rw [product_indicator]
    by_cases he : noiseOutside A σ = G
    · rw [if_pos he, if_pos ((outside_eq_iff A G σ hAG).mp he)]
    · rw [if_neg he, if_neg (fun hall => he ((outside_eq_iff A G σ hAG).mpr hall))]
  calc
    _ = ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        ∏ i, if siteOK A G i (σ i) then 1 else 0 := by simp_rw [hind]
    _ = ∏ i : Fin N, ∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b *
        (if siteOK A G i b then 1 else 0) :=
      aq_bernoulli_stream_independent N p hp hp1
        (fun (i : Fin N) (b : Bool) => if siteOK A G i b then (1 : ℝ) else 0)
    _ = ∏ i : Fin N, if i ∈ A then 1 else if i ∈ G then p else 1 - p := by
      apply Finset.prod_congr rfl
      intro i _
      exact site_expectation A G p hp hp1 i
    _ = _ := site_weight_product A G p hAG

end
end RawNoise

namespace Pool

open scoped Classical BigOperators

/-- The list of positive integers from one through `B`. -/
def positiveRange (B : ℕ) : List ℕ := (List.range B).map Nat.succ

/-- Membership in `positiveRange B` is equivalent to `0 < q` and `q ≤ B`. -/
theorem positiveRange_mem (B q : ℕ) : q ∈ positiveRange B ↔ 0 < q ∧ q ≤ B := by
  constructor
  · intro hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have hrB := List.mem_range.mp hr
    omega
  · rintro ⟨hq, hqB⟩
    apply List.mem_map.mpr
    refine ⟨q - 1, List.mem_range.mpr (by omega), ?_⟩
    omega

/-- The positive range through `B` has length `B`. -/
theorem positiveRange_length (B : ℕ) : (positiveRange B).length = B := by
  simp [positiveRange]

/-- Retain candidates accepted by `aqVerify` and sum the oracle-query costs of verifying all
entries. -/
def verifyList {N : ℕ} (h : Fin N → Bool) (s M : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | q::qs =>
      let checked := aqVerify h s M q
      let tail := verifyList h s M qs
      (if checked.1 then q::tail.1 else tail.1, checked.2 + tail.2)

/-- A candidate survives list verification exactly when it occurs in the list and `aqVerify`
accepts it. -/
theorem verifyList_mem {N : ℕ} (h : Fin N → Bool) (s M q : ℕ) (qs : List ℕ) :
    q ∈ (verifyList h s M qs).1 ↔ q ∈ qs ∧ (aqVerify h s M q).1 = true := by
  induction qs with
  | nil => simp [verifyList]
  | cons r rs ih =>
    cases hv : (aqVerify h s M r).1 <;> simp [verifyList, hv, ih] <;> aesop

/-- The query count of list verification is the sum of the individual verification query counts. -/
theorem verifyList_queries {N : ℕ} (h : Fin N → Bool) (s M : ℕ) (qs : List ℕ) :
    (verifyList h s M qs).2 = (qs.map fun q => (aqVerify h s M q).2).sum := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [verifyList, List.map_cons, List.sum_cons]
    rw [ih]

/-- List verification uses at most three queries per candidate. -/
theorem verifyList_query_cap {N : ℕ} (h : Fin N → Bool) (s M : ℕ) (qs : List ℕ) :
    (verifyList h s M qs).2 ≤ 3 * qs.length := by
  induction qs with
  | nil => simp [verifyList]
  | cons q qs ih =>
    have hc := aqVerify_cost h s M q
    change (aqVerify h s M q).2 + (verifyList h s M qs).2 ≤ _
    rw [List.length_cons]
    omega

/-- Verification cannot increase the length of a candidate list. -/
theorem verifyList_length {N : ℕ} (h : Fin N → Bool) (s M : ℕ) (qs : List ℕ) :
    (verifyList h s M qs).1.length ≤ qs.length := by
  induction qs with
  | nil => exact Nat.le_refl _
  | cons q qs ih =>
    simp only [verifyList]
    split <;> simp only [List.length_cons] <;> omega

/-- Verify all positive candidate periods up to `B`, returning the accepted list and its query
cost. -/
def boundedPool {N : ℕ} (h : Fin N → Bool) (s M B : ℕ) : List ℕ × ℕ :=
  verifyList h s M (positiveRange B)

/-- The bounded pool contains exactly the positive candidates at most `B` that pass `aqVerify`. -/
theorem boundedPool_mem {N : ℕ} (h : Fin N → Bool) (s M B q : ℕ) :
    q ∈ (boundedPool h s M B).1 ↔
      0 < q ∧ q ≤ B ∧ (aqVerify h s M q).1 = true := by
  simp only [boundedPool, verifyList_mem, positiveRange_mem, and_assoc]

/-- The bounded-pool query count is the sum of verification costs over the positive range
through `B`. -/
theorem boundedPool_queries {N : ℕ} (h : Fin N → Bool) (s M B : ℕ) :
    (boundedPool h s M B).2 =
      ((positiveRange B).map fun q => (aqVerify h s M q).2).sum :=
  verifyList_queries h s M (positiveRange B)

/-- Constructing the bounded pool uses at most `3 * B` oracle queries. -/
theorem boundedPool_query_cap {N : ℕ} (h : Fin N → Bool) (s M B : ℕ) :
    (boundedPool h s M B).2 ≤ 3 * B := by
  simpa only [positiveRange_length] using! verifyList_query_cap h s M (positiveRange B)

/-- The bounded candidate pool has length at most `B`. -/
theorem boundedPool_length {N : ℕ} (h : Fin N → Bool) (s M B : ℕ) :
    (boundedPool h s M B).1.length ≤ B := by
  simpa only [positiveRange_length] using! verifyList_length h s M (positiveRange B)

/-- The set of candidates in the bounded pool has cardinality at most `B`. -/
theorem boundedPool_card {N : ℕ} (h : Fin N → Bool) (s M B : ℕ) :
    (boundedPool h s M B).1.toFinset.card ≤ B :=
  (List.toFinset_card_le _).trans (boundedPool_length h s M B)

/-- Every candidate in the bounded pool passes `aqVerify`. -/
theorem boundedPool_verified {N : ℕ} (h : Fin N → Bool) (s M B q : ℕ)
    (hq : q ∈ (boundedPool h s M B).1) : (aqVerify h s M q).1 = true :=
  ((boundedPool_mem h s M B q).mp hq).2.2

/-- Every bounded-pool candidate is positive, at most `B`, and has its last progression site
within the register. -/
theorem boundedPool_legal {N : ℕ} (h : Fin N → Bool) (s M B q : ℕ)
    (hq : q ∈ (boundedPool h s M B).1) :
    0 < q ∧ q ≤ B ∧ s + (M - 1) * q < N := by
  have hp := (boundedPool_mem h s M B q).mp hq
  have hv := hp.2.2
  unfold aqVerify at hv
  split at hv
  · rename_i hc
    exact ⟨hp.1, hp.2.1, hc.2.2.2⟩
  · simp at hv

/-- A legal planted progression of length at least two passes verification if all its sites are
marked. -/
theorem planted_verified {N : ℕ} (h : Fin N → Bool) (s M P : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hb : s + (M - 1) * P < N)
    (hmark : ∀ x : Fin N, x ∈ aqProgressionSet N s M P → h x = true) :
    (aqVerify h s M P).1 = true := by
  have hs : s < N := by
    simpa only [zero_mul, add_zero] using!
      aqProgression_index_lt N s M P 0 (by omega) hb (by omega)
  have hsp : s + P < N := by
    simpa only [one_mul] using!
      aqProgression_index_lt N s M P 1 (by omega) hb (by omega)
  have guard : 0 < P ∧ s < N ∧ s + P < N ∧ s + (M - 1) * P < N :=
    ⟨hP, hs, hsp, hb⟩
  have h0 : h (⟨s, guard.2.1⟩ : Fin N) = true := by
    apply hmark
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
  have h1 : h (⟨s + P, guard.2.2.1⟩ : Fin N) = true := by
    apply hmark
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, Finset.mem_range.mpr (by omega), by simp⟩
  have hlast : h (⟨s + (M - 1) * P, guard.2.2.2⟩ : Fin N) = true := by
    apply hmark
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨M - 1, Finset.mem_range.mpr (by omega), rfl⟩
  unfold aqVerify
  rw [dif_pos guard]
  simp [h0, h1, hlast]

/-- A legal marked planted period at most `B` belongs to the bounded pool when its progression
has length at least two. -/
theorem planted_mem_pool {N : ℕ} (h : Fin N → Bool) (s M P B : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hPB : P ≤ B)
    (hb : s + (M - 1) * P < N)
    (hmark : ∀ x : Fin N, x ∈ aqProgressionSet N s M P → h x = true) :
    P ∈ (boundedPool h s M B).1 :=
  (boundedPool_mem h s M B P).mpr
    ⟨hP, hPB, planted_verified h s M P hM hP hb hmark⟩

/-- The planted period belongs to the bounded pool when the oracle marks the union of its legal
progression and an arbitrary noise set. -/
theorem planted_mem_pool_union_noise {N : ℕ} (h : Fin N → Bool) (s M P B : ℕ)
    (G : Finset (Fin N)) (hM : 2 ≤ M) (hP : 0 < P) (hPB : P ≤ B)
    (hb : s + (M - 1) * P < N)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    P ∈ (boundedPool h s M B).1 := by
  apply planted_mem_pool h s M P B hM hP hPB hb
  intro x hx
  rw [hmark]
  simp only [decide_eq_true_eq]
  exact Finset.mem_union.mpr (Or.inl hx)

/-- Any period returned by `aqAttempt` is positive, at most `B`, and accepted by `aqVerify`. -/
theorem attempt_return_properties {N : ℕ} (h : Fin N → Bool) (s M B : ℕ)
    (y : Fin N) (q : ℕ) (hq : (aqAttempt h s M B y).1 = some q) :
    0 < q ∧ q ≤ B ∧ (aqVerify h s M q).1 = true := by
  unfold aqAttempt at hq
  (try dsimp only at hq)
  split at hq
  · simp at hq
  · rename_i c hc
    (try dsimp only at hq)
    split at hq
    · rename_i hv
      have he : c.2 = q := Option.some.inj hq
      have hd := (continued_fraction_bad_output_soundness_and_work B N y.val).2.2 c.1 c.2 hc
      exact ⟨by simpa only [he] using! hd.1,
        by simpa only [he] using! hd.2.1, by simpa only [he] using! hv⟩
    · simp at hq

/-- Every continued-fraction candidate record entry belongs to the bounded verified pool. -/
theorem cf_record_subset_pool {N : ℕ} (h : Fin N → Bool) (s M B : ℕ)
    (xs : List (Fin N)) (q : ℕ) (hq : q ∈ aqCandidateRecord h s M B xs) :
    q ∈ (boundedPool h s M B).1 := by
  obtain ⟨y, _, hy⟩ := (aqCandidateRecord_mem h s M B q xs).mp hq
  exact (boundedPool_mem h s M B q).mpr (attempt_return_properties h s M B y q hy)

/-- Collecting continued-fraction candidates and constructing the bounded pool uses at most
`xs.length * (k + 3) + 3 * B` queries. -/
theorem cf_plus_pool_query_cap {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) :
    aqCandidateRecordQueries h s M B k xs + (boundedPool h s M B).2 ≤
      xs.length * (k + 3) + 3 * B :=
  Nat.add_le_add (aqCandidateRecordQueries_cap h s M B k xs)
    (boundedPool_query_cap h s M B)

end Pool

/-- Read each Boolean oracle on the entire register to obtain a list of observed sets. -/
def readTables {N : ℕ} (observations : List (Fin N → Bool)) : List (Finset (Fin N)) :=
  observations.map (fun h => (readRegister h (List.finRange N)).1)

/-- Reading the characteristic oracle of a finite set returns that set. -/
theorem readRegister_set {N : ℕ} (obs : Finset (Fin N)) :
    (readRegister (fun x => decide (x ∈ obs)) (List.finRange N)).1 = obs := by
  rw [readRegister_all]
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- For legal candidates and positive progression length, the set produced by executable fresh
filtering equals abstract compatibility filtering. -/
theorem actual_survivors {N : ℕ} (s M : ℕ) (observations : List (Fin N → Bool))
    (qs : List ℕ) (hM : 0<M) (hlegal : ∀ q ∈ qs, 0<q ∧ s+(M-1)*q<N) :
    (freshRounds s M observations qs).1.toFinset =
      Multi.filterList N s M (readTables observations) qs.toFinset := by
  ext q
  simp only [List.mem_toFinset, freshRounds_mem s M q observations qs hM hlegal,
    Multi.mem_filterList, readTables, List.forall_mem_map]

/-- The Boolean characteristic oracles for the protected marked sets generated by the raw
rounds. -/
noncomputable def oracleRounds (N s M P t : ℕ) (σ : Multi.RawRounds N t) :
    Fin t → (Fin N → Bool) :=
  fun i x => decide (x ∈ aqFreshMarked N s M P (σ i))

/-- Reading the generated oracle rounds yields exactly their abstract observed marked sets. -/
theorem oracleRounds_tables (N s M P t : ℕ) (σ : Multi.RawRounds N t) :
    readTables (List.ofFn (oracleRounds N s M P t σ)) =
      List.ofFn (Multi.observedRounds N s M P t σ) := by
  rw [readTables, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact readRegister_set _

/-- For legal candidates and positive progression length, executable selection after fresh
filtering equals the abstract multi-round output. -/
theorem actual_output_eq (N s M P t : ℕ) (σ : Multi.RawRounds N t) (qs : List ℕ)
    (hM : 0<M) (hlegal : ∀ q ∈ qs, 0<q ∧ s+(M-1)*q<N) :
    uniqueOutput (freshRounds s M (List.ofFn (oracleRounds N s M P t σ)) qs).1 =
      Multi.output N s M t qs.toFinset (Multi.observedRounds N s M P t σ) := by
  apply Option.ext
  intro q
  rw [uniqueOutput_eq_some_iff, Multi.output, Multi.uniqueOutput_eq_some_iff,
    actual_survivors s M _ qs hM hlegal, oracleRounds_tables]
  rfl

/-- Append the bounded verified fallback pool to the candidates collected from the supplied
labels. -/
def initialCandidates {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ) (labels : List (Fin N)) : List ℕ :=
  (collect h s M B k labels).1 ++ (Pool.boundedPool h s M B).1

/-- The set of initial candidates equals the set of bounded-pool candidates. -/
theorem initialCandidates_set {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) :
    (initialCandidates h s M B k labels).toFinset = (Pool.boundedPool h s M B).1.toFinset := by
  rw [initialCandidates, List.toFinset_append]
  apply Finset.union_eq_right.mpr
  intro q hq
  apply List.mem_toFinset.mpr
  apply Pool.cf_record_subset_pool h s M B labels q
  rw [collect_outputs] at hq
  exact List.mem_toFinset.mp hq

/-- Every initial candidate is positive and defines an in-bounds progression. -/
theorem initialCandidates_legal {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) :
    ∀ q ∈ initialCandidates h s M B k labels, 0<q ∧ s+(M-1)*q<N := by
  intro q hq
  rcases List.mem_append.mp hq with hc | hp
  · exact collect_legal h s M B k labels q hc
  · have hleg := Pool.boundedPool_legal h s M B q hp
    exact ⟨hleg.1,hleg.2.2⟩

/-- Compare each list entry with `q`, stopping at the first mismatch and counting comparisons. -/
def compareRest (q : ℕ) : List ℕ → Bool × ℕ
  | [] => (true,0)
  | r::rs => if r=q then
      let tail := compareRest q rs
      (tail.1,tail.2+1)
    else (false,1)

/-- The comparison routine returns true exactly when every entry equals `q`. -/
theorem compareRest_value (q : ℕ) (rs : List ℕ) :
    (compareRest q rs).1 = rs.all (fun r => r == q) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => by_cases he : r=q <;> simp [compareRest, he, ih]

/-- The comparison routine uses at most one test per list entry. -/
theorem compareRest_tests (q : ℕ) (rs : List ℕ) : (compareRest q rs).2 ≤ rs.length := by
  induction rs with
  | nil => exact Nat.le_refl 0
  | cons r rs ih => by_cases he : r=q <;> simp only [compareRest, he, if_true, if_false,
      List.length_cons] <;> omega

/-- Select a common value of a nonempty candidate list and record the comparisons used to check
uniqueness. -/
def uniquePaid : List ℕ → Option ℕ × ℕ
  | [] => (none,0)
  | q::qs => let checked := compareRest q qs
      (if checked.1 then some q else none,checked.2)

/-- The value returned by the costed selector agrees with `uniqueOutput`. -/
theorem uniquePaid_value (qs : List ℕ) : (uniquePaid qs).1 = uniqueOutput qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [uniquePaid, uniqueOutput, compareRest_value]

/-- The costed selector performs at most as many tests as there are list entries. -/
theorem uniquePaid_tests (qs : List ℕ) : (uniquePaid qs).2 ≤ qs.length := by
  cases qs with
  | nil => exact Nat.le_refl 0
  | cons q qs => exact (compareRest_tests q qs).trans (Nat.le_succ _)

/-- The continued-fraction candidates, combined pool, compatible candidates, output, and
resource bill of a fallback recovery run. -/
structure RecoveryTrace where
  cfCandidates : List ℕ
  candidates : List ℕ
  compatible : List ℕ
  result : Option ℕ
  bill : Bill
  deriving Repr

/-- Run candidate collection, bounded-pool fallback, fresh-observation pruning, and costed
uniqueness selection, returning the complete recovery trace. -/
def runWithFallback {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) : RecoveryTrace :=
  let cf := collect h s M B k labels
  let pool := Pool.boundedPool h s M B
  let candidates := cf.1 ++ pool.1
  let fresh := freshRounds s M observations candidates
  let selected := uniquePaid fresh.1
  ⟨cf.1, candidates, fresh.1, selected.1,
    cf.2.add (Bill.add ⟨pool.2,0,0,B,0⟩ (fresh.2.add ⟨0,0,0,selected.2,0⟩))⟩

/-- The fallback run uses at most `labels.length * (k + 3) + 3 * B + observations.length * N`
oracle queries. -/
theorem fallback_query_cap {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) :
    (runWithFallback h s M B k labels observations).bill.queries ≤
      labels.length*(k+3)+3*B+observations.length*N := by
  change (collect h s M B k labels).2.queries +
    ((Pool.boundedPool h s M B).2+
      (freshRounds s M observations (initialCandidates h s M B k labels)).2.queries) ≤ _
  rw [collect_queries, freshRounds_queries]
  have hc := Pool.cf_plus_pool_query_cap h s M B k labels
  omega

/-- For positive progression length, fallback recovery on protected oracle rounds equals
abstract recovery from the bounded candidate pool. -/
theorem fallback_result_eq (N s M P B k t : ℕ) (h : Fin N → Bool)
    (labels : List (Fin N)) (σ : Multi.RawRounds N t) (hM : 0<M) :
    (runWithFallback h s M B k labels (List.ofFn (oracleRounds N s M P t σ))).result =
      Multi.output N s M t (Pool.boundedPool h s M B).1.toFinset
        (Multi.observedRounds N s M P t σ) := by
  change (uniquePaid (freshRounds s M (List.ofFn (oracleRounds N s M P t σ))
    (initialCandidates h s M B k labels)).1).1 = _
  rw [uniquePaid_value,
    actual_output_eq N s M P t σ _ hM (initialCandidates_legal h s M B k labels),
    initialCandidates_set]

noncomputable section
open scoped Classical BigOperators

/-- The Bernoulli probability that the executable fallback run fails to return the planted
period for the fixed source labels. -/
def actualFailureMass (N s M P B k t : ℕ) (h : Fin N → Bool)
    (labels : List (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : ℝ :=
  ∑ σ : Multi.RawRounds N t, (Multi.roundsLaw N t p hp hp1).prob σ *
    (if (runWithFallback h s M B k labels (List.ofFn (oracleRounds N s M P t σ))).result ≠
      some P then 1 else 0)

/-- For positive progression length, executable failure mass equals abstract failure mass for
the bounded candidate pool. -/
theorem actualFailureMass_eq (N s M P B k t : ℕ) (h : Fin N → Bool)
    (labels : List (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (hM : 0<M) :
    actualFailureMass N s M P B k t h labels p hp hp1 =
      Multi.failureMass N s M P t (Pool.boundedPool h s M B).1.toFinset p hp hp1 := by
  unfold actualFailureMass Multi.failureMass
  apply Finset.sum_congr rfl
  intro σ _
  rw [fallback_result_eq N s M P B k t h labels σ hM]

/-- For a legal marked planted period at most `B` and length at least two, executable failure
mass is at most `B * pmax ^ t` when `p ≤ pmax < 1`. -/
theorem actualFailureMass_le (N s M P B k t : ℕ) (h : Fin N → Bool)
    (labels : List (Fin N)) (p pmax : ℝ) (hp : 0≤p) (hpp : p≤pmax) (hmax : pmax<1)
    (hM : 2≤M) (hP : 0<P) (hPB : P≤B) (hb : s+(M-1)*P<N)
    (hmark : ∀ x : Fin N, x ∈ aqProgressionSet N s M P → h x = true) :
    actualFailureMass N s M P B k t h labels p hp (le_trans hpp hmax.le) ≤
      (B : ℝ)*pmax^t := by
  let pool := (Pool.boundedPool h s M B).1.toFinset
  have htrue : P ∈ pool := List.mem_toFinset.mpr
    (Pool.planted_mem_pool h s M P B hM hP hPB hb hmark)
  have hcard : (pool \ {P}).card ≤ B :=
    (Finset.card_le_card Finset.sdiff_subset).trans (Pool.boundedPool_card h s M B)
  have hpmax : 0≤pmax := hp.trans hpp
  rw [actualFailureMass_eq N s M P B k t h labels p hp _ (by omega)]
  calc
    Multi.failureMass N s M P t pool p hp (le_trans hpp hmax.le) ≤
        ∑ Q ∈ pool \ {P}, pmax^(t*aqCandidateSeparation N s M P Q) :=
      Multi.failureMass_le N s M P t pool htrue p pmax hp hpp hmax
    _ ≤ ∑ _Q ∈ pool \ {P}, pmax^t := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hleg := Pool.boundedPool_legal h s M B Q
        (List.mem_toFinset.mp (Finset.mem_sdiff.mp hQ).1)
      have hne : Q ≠ P := by simpa only [Finset.mem_singleton] using! (Finset.mem_sdiff.mp hQ).2
      have hsep := Separation.candidate_separation_pos N s M P Q hM hP hleg.1 hb hleg.2.2 hne
      have he := Nat.mul_le_mul_left t (show 1≤aqCandidateSeparation N s M P Q by omega)
      simp only [Nat.mul_one] at he
      exact pow_le_pow_of_le_one hpmax hmax.le he
    _ = (((pool \ {P}).card : ℕ) : ℝ)*pmax^t := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ)*pmax^t :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hpmax t)

/-- Under the planted-period and legality assumptions, fallback recovery on protected
observations cannot return a different period. -/
theorem fallback_wrong_zero (N s M P B k t : ℕ) (h : Fin N → Bool)
    (labels : List (Fin N)) (σ : Multi.RawRounds N t)
    (hM : 2≤M) (hP : 0<P) (hPB : P≤B) (hb : s+(M-1)*P<N)
    (hmark : ∀ x : Fin N, x ∈ aqProgressionSet N s M P → h x = true)
    (Q : ℕ) (hQP : Q≠P) :
    (runWithFallback h s M B k labels (List.ofFn (oracleRounds N s M P t σ))).result ≠ some Q := by
  rw [fallback_result_eq N s M P B k t h labels σ (by omega)]
  intro hret
  have hp : P ∈ (Pool.boundedPool h s M B).1.toFinset :=
    List.mem_toFinset.mpr (Pool.planted_mem_pool h s M P B hM hP hPB hb hmark)
  have hsur := Multi.true_survives N s M P t _ hp σ
  have hs := (Multi.uniqueOutput_eq_some_iff _ Q).mp hret
  rw [hs] at hsur
  exact hQP (Finset.mem_singleton.mp hsur).symm

/-- The finite label distribution given by Born probabilities of the amplified Fourier state for
the marked set `C`. -/
def sourceLabelLaw (N : ℕ) (hN : 0<N) (C : Finset (Fin N)) : FinDist (Fin N) where
  prob y := BornProb (aqState N hN C.card C) y
  nonneg y := bornProb_nonneg _ y
  sum_one := (aq_error_word_counts N hN C.card C).2.2.2.2

/-- Average the executable fresh-observation failure mass over independent amplified source
labels. -/
def jointFailureMass (N : ℕ) (hN : 0<N) (s M P B R t : ℕ) (C : Finset (Fin N))
    (h : Fin N → Bool) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : ℝ :=
  ∑ labels : Fin R → Fin N, (sourceLabelLaw N hN C).probOf labels *
    actualFailureMass N s M P B (aqRounds N C.card) t h (List.ofFn labels) p hp hp1

/-- When `C` contains the legal planted progression and its characteristic oracle is used, joint
failure mass is at most `B * pmax ^ t` under the stated bounds. -/
theorem jointFailureMass_le (N : ℕ) (hN : 0<N) (s M P B R t : ℕ) (C : Finset (Fin N))
    (h : Fin N → Bool) (p pmax : ℝ) (hp : 0≤p) (hpp : p≤pmax) (hmax : pmax<1)
    (hM : 2≤M) (hP : 0<P) (hPB : P≤B) (hb : s+(M-1)*P<N)
    (hC : aqProgressionSet N s M P ⊆ C) (horacle : ∀ x, h x = decide (x∈C)) :
    jointFailureMass N hN s M P B R t C h p hp (le_trans hpp hmax.le) ≤ (B : ℝ)*pmax^t := by
  have hmark (x : Fin N) (hx : x ∈ aqProgressionSet N s M P) : h x = true := by
    rw [horacle x]
    exact decide_eq_true (hC hx)
  calc
    jointFailureMass N hN s M P B R t C h p hp (le_trans hpp hmax.le) ≤
        ∑ labels : Fin R → Fin N, (sourceLabelLaw N hN C).probOf labels * ((B : ℝ)*pmax^t) := by
      apply Finset.sum_le_sum
      intro labels _
      apply mul_le_mul_of_nonneg_left
      · exact actualFailureMass_le N s M P B _ t h _ p pmax hp hpp hmax hM hP hPB hb hmark
      · exact Finset.prod_nonneg fun r _ => (sourceLabelLaw N hN C).nonneg (labels r)
    _ = (B : ℝ)*pmax^t := by
      rw [← Finset.sum_mul, (sourceLabelLaw N hN C).sum_probOf R, one_mul]

end

namespace Effective

open scoped Classical BigOperators

/-- A family of `k`-bit tapes indexed by `t` rounds and `N` register locations. -/
abbrev RawTapes (N t k : ℕ) := Fin t → (Fin N → Reg k)

/-- Return true when the integer encoded by the `k`-bit tape is less than the threshold `a`. -/
def draw (k a : ℕ) (bits : Reg k) : Bool :=
  decide ((bitVecEquiv k bits).val < a)

/-- Apply the threshold draw independently to each supplied site tape. -/
def drawStream (N k a : ℕ) (tapes : Fin N → Reg k) : Fin N → Bool :=
  fun i => draw k a (tapes i)

/-- Convert the tapes for all rounds and sites into Boolean noise streams. -/
def drawRounds (N t k a : ℕ) (tapes : RawTapes N t k) : Multi.RawRounds N t :=
  fun r => drawStream N k a (tapes r)

/-- For a threshold fitting in `k` bits, the direct threshold draw equals `aqNextBernoulliDraw`. -/
theorem draw_eq_next (k a : ℕ) (ha : a ≤ 2^k) (bits : Reg k) :
    draw k a bits = aqNextBernoulliDraw k a ha bits := by
  have hmem : bits ∈ aqNextBernoulliTapes k a ha ↔ (bitVecEquiv k bits).val < a := by
    constructor
    · intro h
      obtain ⟨i,_hi,he⟩ := Finset.mem_image.mp h
      have hv : (bitVecEquiv k bits).val = i.val := by
        rw [← he, Equiv.apply_symm_apply]
      exact hv.symm ▸ i.isLt
    · intro hi
      apply Finset.mem_image.mpr
      refine ⟨⟨(bitVecEquiv k bits).val,hi⟩,Finset.mem_univ _,?_⟩
      have hv : (⟨(bitVecEquiv k bits).val,
          Nat.lt_of_lt_of_le hi ha⟩ : Fin (2^k)) = bitVecEquiv k bits := Fin.ext rfl
      change (bitVecEquiv k).symm ⟨(bitVecEquiv k bits).val,
        Nat.lt_of_lt_of_le hi ha⟩ = bits
      rw [hv]
      exact Equiv.symm_apply_apply (bitVecEquiv k) bits
  unfold draw aqNextBernoulliDraw
  exact decide_eq_decide.mpr hmem.symm

/-- For a threshold fitting in `k` bits, the direct stream draw equals `aqNextBernoulliStream`. -/
theorem drawStream_eq_next (N k a : ℕ) (ha : a ≤ 2^k) (tapes : Fin N → Reg k) :
    drawStream N k a tapes = aqNextBernoulliStream N k a ha tapes := by
  funext i
  exact draw_eq_next k a ha (tapes i)

/-- The dyadic parameter `a / 2 ^ k` realized by threshold sampling from `k` fair bits. -/
noncomputable def realizedP (k a : ℕ) : ℝ := aqNextEffectiveParameter k a

/-- A threshold at most `2 ^ k` realizes a parameter between zero and one. -/
theorem realizedP_range (k a : ℕ) (ha : a ≤ 2^k) :
    0 ≤ realizedP k a ∧ realizedP k a ≤ 1 :=
  aqNext_effective_parameter_range k a ha

/-- The product law of uniform fair `k`-bit tapes for all rounds and register sites. -/
noncomputable def fairRoundsLaw (N t k : ℕ) : FinDist (RawTapes N t k) where
  prob tapes := (uniformFairTapeProductLaw k N).probOf tapes
  nonneg tapes := Finset.prod_nonneg fun r _ =>
    (uniformFairTapeProductLaw k N).nonneg (tapes r)
  sum_one := (uniformFairTapeProductLaw k N).sum_probOf t

/-- Every tape family has probability `((2 ^ k)⁻¹) ^ (N * t)` under the fair-rounds law. -/
theorem fairRoundsLaw_prob (N t k : ℕ) (tapes : RawTapes N t k) :
    (fairRoundsLaw N t k).prob tapes = (((2 : ℝ)^k)⁻¹)^(N*t) := by
  change (∏ r : Fin t, ∏ i : Fin N, (((2 : ℝ)^k)⁻¹)) = _
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (pow_mul (((2 : ℝ)^k)⁻¹) N t).symm

/-- Threshold sampling pushes the uniform site-tape product law to the Bernoulli stream law with
parameter `realizedP k a`. -/
theorem single_round_fiber (N k a : ℕ) (ha : a ≤ 2^k) (σ : Fin N → Bool) :
    (∑ tapes : Fin N → Reg k, (uniformFairTapeProductLaw k N).prob tapes *
      (if drawStream N k a tapes = σ then 1 else 0)) =
      (bernoulliStreamLaw N (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).prob σ := by
  simp_rw [drawStream_eq_next N k a ha]
  have h := aqNext_effective_stream_eq_bernoulli N k a ha σ
  exact h

/-- Threshold sampling of all fair tapes has exactly the multi-round Bernoulli law with the
realized dyadic parameter. -/
theorem actual_rounds_fiber (N t k a : ℕ) (ha : a ≤ 2^k)
    (σ : Multi.RawRounds N t) :
    (∑ tapes : RawTapes N t k, (fairRoundsLaw N t k).prob tapes *
      (if drawRounds N t k a tapes = σ then 1 else 0)) =
      (Multi.roundsLaw N t (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).prob σ := by
  have hind (tapes : RawTapes N t k) :
      (if drawRounds N t k a tapes = σ then (1 : ℝ) else 0) =
        ∏ r : Fin t, (if drawStream N k a (tapes r) = σ r then (1 : ℝ) else 0) := by
    have he : drawRounds N t k a tapes = σ ↔
        ∀ r, drawStream N k a (tapes r) = σ r :=
      ⟨fun h r => congrFun h r,fun h => funext h⟩
    rw [RawNoise.product_indicator]
    by_cases hf : drawRounds N t k a tapes = σ
    · rw [if_pos hf, if_pos (he.mp hf)]
    · rw [if_neg hf, if_neg (fun hall => hf (he.mpr hall))]
  calc
    (∑ tapes : RawTapes N t k, (fairRoundsLaw N t k).prob tapes *
        (if drawRounds N t k a tapes = σ then 1 else 0)) =
        ∑ tapes : RawTapes N t k, (uniformFairTapeProductLaw k N).probOf tapes *
          ∏ r : Fin t, (if drawStream N k a (tapes r) = σ r then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro tapes _
      rw [hind]
      rfl
    _ = ∏ r : Fin t, ∑ tapes : Fin N → Reg k,
        (uniformFairTapeProductLaw k N).prob tapes *
          (if drawStream N k a tapes = σ r then (1 : ℝ) else 0) :=
      FinDist.expect_prod (uniformFairTapeProductLaw k N)
        (fun (r : Fin t) (tapes : Fin N → Reg k) =>
          if drawStream N k a tapes = σ r then (1 : ℝ) else 0)
    _ = ∏ r : Fin t, (bernoulliStreamLaw N (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).prob (σ r) := by
      apply Finset.prod_congr rfl
      intro r _
      exact single_round_fiber N k a ha (σ r)
    _ = _ := rfl

/-- Any decidable output event has equal probability under fair-tape sampling and the
corresponding realized-parameter Bernoulli rounds. -/
theorem output_event_pushforward (N t k a : ℕ) (ha : a ≤ 2^k)
    {Y : Type*} (f : Multi.RawRounds N t → Y) (E : Y → Prop) [DecidablePred E] :
    (fairRoundsLaw N t k).expect
        (fun tapes => if E (f (drawRounds N t k a tapes)) then 1 else 0) =
      (Multi.roundsLaw N t (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).expect
          (fun σ => if E (f σ) then 1 else 0) := by
  have hq (σ : Multi.RawRounds N t) :
      (Multi.roundsLaw N t (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).prob σ =
      ∑ tapes : RawTapes N t k,
        if drawRounds N t k a tapes = σ then (fairRoundsLaw N t k).prob tapes else 0 := by
    rw [← actual_rounds_fiber N t k a ha σ]
    apply Finset.sum_congr rfl
    intro tapes _
    by_cases he : drawRounds N t k a tapes = σ <;> simp [he]
  exact (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.expect_eq_of_pushforward (fairRoundsLaw N t k)
    (Multi.roundsLaw N t (realizedP k a)
      (realizedP_range k a ha).1 (realizedP_range k a ha).2)
    (drawRounds N t k a) (fun σ => if E (f σ) then 1 else 0) hq).symm

/-- Apply a costed function to a list, collecting outputs in order and summing costs. -/
def traverse {I A : Type*} (f : I → A × ℕ) : List I → List A × ℕ
  | [] => ([],0)
  | i::rest =>
      let head := f i
      let tail := traverse f rest
      (head.1::tail.1,head.2+tail.2)

/-- Traversing a function with constant cost `c` returns the mapped values and total cost
`is.length * c`. -/
theorem traverse_const {I A : Type*} (f : I → A × ℕ) (g : I → A) (c : ℕ)
    (hf : ∀ i, f i = (g i,c)) (is : List I) :
    traverse f is = (is.map g,is.length*c) := by
  induction is with
  | nil => simp [traverse]
  | cons i is ih => simp [traverse,hf,ih,Nat.succ_mul,Nat.add_comm]

/-- Traversing all indices of `Fin n` with constant cost `c` returns `List.ofFn g` and cost `n *
c`. -/
theorem traverse_fin_const {A : Type*} (n : ℕ) (f : Fin n → A × ℕ)
    (g : Fin n → A) (c : ℕ) (hf : ∀ i, f i = (g i,c)) :
    traverse f (List.finRange n) = (List.ofFn g,n*c) := by
  simpa only [List.ofFn_eq_map,List.length_finRange] using!
    traverse_const f g c hf (List.finRange n)

/-- View a list as a function on `Fin n`, using the supplied default for missing entries. -/
def table {A : Type*} (n : ℕ) (xs : List A) (default : A) : Fin n → A :=
  fun i => xs.getD i.val default

/-- Converting `List.ofFn g` to a table recovers `g`. -/
theorem table_ofFn {A : Type*} (n : ℕ) (g : Fin n → A) (default : A) :
    table n (List.ofFn g) default = g := by
  funext i
  change (List.ofFn g)[i.val]?.getD default = g i
  rw [List.getElem?_ofFn,dif_pos i.isLt]
  rfl

/-- Read every bit of a site tape, apply the threshold draw, and record the number of bits read. -/
def siteRun (k a : ℕ) (bits : Reg k) : Bool × ℕ :=
  let read := traverse (fun i : Fin k => (bits i,1)) (List.finRange k)
  (draw k a (table k read.1 false),read.2)

/-- The site sampler returns `draw k a bits` and reads exactly `k` bits. -/
theorem siteRun_eq (k a : ℕ) (bits : Reg k) : siteRun k a bits = (draw k a bits,k) := by
  have hr := traverse_fin_const k (fun i : Fin k => (bits i,1)) bits 1 (fun _ => rfl)
  simp only [siteRun,hr,table_ofFn,Nat.mul_one]

/-- Run the costed site sampler at every register location and return the resulting Boolean
stream and bit cost. -/
def streamRun (N k a : ℕ) (tapes : Fin N → Reg k) : (Fin N → Bool) × ℕ :=
  let read := traverse (fun i : Fin N => siteRun k a (tapes i)) (List.finRange N)
  (table N read.1 false,read.2)

/-- The stream sampler returns `drawStream N k a tapes` and reads exactly `N * k` bits. -/
theorem streamRun_eq (N k a : ℕ) (tapes : Fin N → Reg k) :
    streamRun N k a tapes = (drawStream N k a tapes,N*k) := by
  have hr := traverse_fin_const N (fun i : Fin N => siteRun k a (tapes i))
    (fun i => draw k a (tapes i)) k (fun i => siteRun_eq k a (tapes i))
  unfold streamRun
  rw [hr]
  (try dsimp only)
  rw [table_ofFn]
  rfl

/-- Run the costed stream sampler for all rounds, returning the noise streams and total bit
cost. -/
def roundsRun (N t k a : ℕ) (tapes : RawTapes N t k) : Multi.RawRounds N t × ℕ :=
  let read := traverse (fun r : Fin t => streamRun N k a (tapes r)) (List.finRange t)
  (table t read.1 (fun _ => false),read.2)

/-- The rounds sampler returns `drawRounds N t k a tapes` and reads exactly `N * t * k` bits. -/
theorem roundsRun_eq (N t k a : ℕ) (tapes : RawTapes N t k) :
    roundsRun N t k a tapes = (drawRounds N t k a tapes,N*t*k) := by
  have hr := traverse_fin_const t (fun r : Fin t => streamRun N k a (tapes r))
    (fun r => drawStream N k a (tapes r)) (N*k)
    (fun r => streamRun_eq N k a (tapes r))
  unfold roundsRun
  rw [hr]
  (try dsimp only)
  rw [table_ofFn]
  change (drawRounds N t k a tapes,t*(N*k)) = (drawRounds N t k a tapes,N*t*k)
  congr 1
  ring

/-- For a fitting threshold, the costed sampler has the multi-round Bernoulli law with parameter
`realizedP k a`. -/
theorem roundsRun_fiber (N t k a : ℕ) (ha : a ≤ 2^k)
    (σ : Multi.RawRounds N t) :
    (∑ tapes : RawTapes N t k, (fairRoundsLaw N t k).prob tapes *
      (if (roundsRun N t k a tapes).1 = σ then 1 else 0)) =
      (Multi.roundsLaw N t (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).prob σ := by
  simpa only [roundsRun_eq] using! actual_rounds_fiber N t k a ha σ

/-- The rounds sampler reads exactly `N * t * k` bits. -/
theorem roundsRun_bits (N t k a : ℕ) (tapes : RawTapes N t k) :
    (roundsRun N t k a tapes).2 = N*t*k := by
  rw [roundsRun_eq]

/-- Output events of the costed fair-tape sampler have the same probabilities as under
realized-parameter Bernoulli rounds. -/
theorem roundsRun_event_pushforward (N t k a : ℕ) (ha : a ≤ 2^k)
    {Y : Type*} (f : Multi.RawRounds N t → Y) (E : Y → Prop) [DecidablePred E] :
    (fairRoundsLaw N t k).expect
        (fun tapes => if E (f (roundsRun N t k a tapes).1) then 1 else 0) =
      (Multi.roundsLaw N t (realizedP k a)
        (realizedP_range k a ha).1 (realizedP_range k a ha).2).expect
          (fun σ => if E (f σ) then 1 else 0) := by
  simpa only [roundsRun_eq] using! output_event_pushforward N t k a ha f E

/-- The parameter realized by the floored Bernoulli threshold is at most any public upper bound
`pmax` on `p`. -/
theorem floor_realized_le_public (k : ℕ) (p pmax : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpp : p ≤ pmax) :
    realizedP k (aqNextBernoulliThreshold k p) ≤ pmax :=
  (aqNext_effective_parameter_bounds k p hp hp1).1.trans hpp

/-- Sample costed noise rounds and pass them to an arbitrary consumer, retaining the sampling
bit cost. -/
def runOutput {Y : Type*} (N t kBits a : ℕ) (consume : Multi.RawRounds N t → Y)
    (tapes : RawTapes N t kBits) : Y × ℕ :=
  let sampled := roundsRun N t kBits a tapes
  (consume sampled.1,sampled.2)

/-- The sampled consumer output is `consume (drawRounds ...)` and its recorded sampling cost is
`N * t * kBits`. -/
theorem runOutput_eq {Y : Type*} (N t kBits a : ℕ)
    (consume : Multi.RawRounds N t → Y) (tapes : RawTapes N t kBits) :
    runOutput N t kBits a consume tapes =
      (consume (drawRounds N t kBits a tapes),N*t*kBits) := by
  unfold runOutput
  rw [roundsRun_eq]

/-- The failure probability of fallback recovery when fresh noise is generated from uniform
finite fair-bit tapes. -/
noncomputable def effectiveFailureMass (N s M P B kAA t kBits a : ℕ)
    (h : Fin N → Bool) (labels : List (Fin N)) : ℝ :=
  (fairRoundsLaw N t kBits).expect fun tapes =>
    if (runWithFallback h s M B kAA labels
      (List.ofFn (oracleRounds N s M P t (roundsRun N t kBits a tapes).1))).result ≠ some P
      then 1 else 0

/-- For a fitting threshold, finite-tape failure mass equals executable Bernoulli failure mass
at the realized dyadic parameter. -/
theorem effectiveFailureMass_eq (N s M P B kAA t kBits a : ℕ) (ha : a ≤ 2^kBits)
    (h : Fin N → Bool) (labels : List (Fin N)) :
    effectiveFailureMass N s M P B kAA t kBits a h labels =
      actualFailureMass N s M P B kAA t h labels (realizedP kBits a)
        (realizedP_range kBits a ha).1 (realizedP_range kBits a ha).2 := by
  exact roundsRun_event_pushforward N t kBits a ha
    (fun σ => (runWithFallback h s M B kAA labels
      (List.ofFn (oracleRounds N s M P t σ))).result)
    (fun result => result ≠ some P)

/-- Under the planted-period assumptions and a realized parameter at most `pmax < 1`,
finite-tape failure mass is at most `B * pmax ^ t`. -/
theorem effectiveFailureMass_le (N s M P B kAA t kBits a : ℕ) (ha : a ≤ 2^kBits)
    (h : Fin N → Bool) (labels : List (Fin N)) (pmax : ℝ)
    (hpmax : realizedP kBits a ≤ pmax) (hmax : pmax < 1)
    (hM : 2≤M) (hP : 0<P) (hPB : P≤B) (hb : s+(M-1)*P<N)
    (hmark : ∀ x : Fin N, x ∈ aqProgressionSet N s M P → h x = true) :
    effectiveFailureMass N s M P B kAA t kBits a h labels ≤ (B : ℝ)*pmax^t := by
  rw [effectiveFailureMass_eq N s M P B kAA t kBits a ha h labels]
  exact actualFailureMass_le N s M P B kAA t h labels (realizedP kBits a) pmax
    (realizedP_range kBits a ha).1 hpmax hmax hM hP hPB hb hmark

end Effective

/-- Sample one source noise stream and `t` fresh noise rounds, returning both and their combined
bit cost. -/
def sourceAndFreshNoise (N t k a : ℕ) (source : Fin N → Reg k)
    (fresh : Effective.RawTapes N t k) : ((Fin N → Bool) × Multi.RawRounds N t) × ℕ :=
  let first := Effective.streamRun N k a source
  let rest := Effective.roundsRun N t k a fresh
  ((first.1,rest.1),first.2+rest.2)

/-- Sampling the source and fresh noise reads exactly `N * (t + 1) * k` bits. -/
theorem sourceAndFreshNoise_bits (N t k a : ℕ) (source : Fin N → Reg k)
    (fresh : Effective.RawTapes N t k) : (sourceAndFreshNoise N t k a source fresh).2=N*(t+1)*k := by
  unfold sourceAndFreshNoise
  rw [Effective.streamRun_eq,Effective.roundsRun_eq]
  (try dsimp only)
  ring

/-- The initial candidate list has length at most `labels.length + B`. -/
theorem initialCandidates_length {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) :
    (initialCandidates h s M B k labels).length ≤ labels.length+B := by
  rw [initialCandidates, List.length_append]
  exact Nat.add_le_add (collect_length h s M B k labels) (Pool.boundedPool_length h s M B)

/-- The fallback trace has the stated source-gate count, continued-fraction stage bound and work
count, and table-test bound including pool and uniqueness checks. -/
theorem fallback_counts {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) :
    (runWithFallback h s M B k labels observations).bill.sourceGates = labels.length*(3*k+2) ∧
      (runWithFallback h s M B k labels observations).bill.cfStages ≤ labels.length*(cfDepth N+1) ∧
      (runWithFallback h s M B k labels observations).bill.cfWork =
        labels.length*((cfDepth N+1)*(cfDepth N+2)/2) ∧
      (runWithFallback h s M B k labels observations).bill.tableTests ≤
        B+observations.length*(labels.length+B)*(M+1)+(labels.length+B) := by
  let qs := initialCandidates h s M B k labels
  let fresh := freshRounds s M observations qs
  have hlen := initialCandidates_length h s M B k labels
  have hf := freshRounds_extra s M observations qs
  have hc := collect_classical h s M B k labels
  have ht := freshRounds_tests s M observations qs
  have hmul := Nat.mul_le_mul_right (M+1) (Nat.mul_le_mul_left observations.length hlen)
  have htested := ht.trans hmul
  have hcharged : fresh.2.tableTests ≤ observations.length*(labels.length+B)*(M+1) := htested
  have hselected := (uniquePaid_tests fresh.1).trans
    ((freshRounds_length s M observations qs).trans hlen)
  change (collect h s M B k labels).2.sourceGates+(0+(fresh.2.sourceGates+0)) = _ ∧
    (collect h s M B k labels).2.cfStages+(0+(fresh.2.cfStages+0)) ≤ _ ∧
    (collect h s M B k labels).2.cfWork+(0+(fresh.2.cfWork+0)) = _ ∧
    (collect h s M B k labels).2.tableTests+(B+(fresh.2.tableTests+(uniquePaid fresh.1).2)) ≤ _
  rw [hf.1,hf.2.1,hf.2.2,hc.2.2,collect_source_gates]
  simp only [Nat.zero_add,Nat.add_zero, true_and]
  refine ⟨hc.1,hc.2.1,?_⟩
  omega

/-- The continued-fraction field of the fallback trace equals `aqCandidateRecord` on the source
labels. -/
theorem fallback_cf_record {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) :
    (runWithFallback h s M B k labels observations).cfCandidates = aqCandidateRecord h s M B labels :=
  collect_outputs h s M B k labels

/-- Every continued-fraction candidate retained in the fallback trace passes `aqVerify`. -/
theorem fallback_cf_verified {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) (q : ℕ)
    (hq : q ∈ (runWithFallback h s M B k labels observations).cfCandidates) :
    (aqVerify h s M q).1 = true := by
  rw [fallback_cf_record] at hq
  exact aqCandidateRecord_verified h s M B labels q hq

noncomputable section
open scoped Classical BigOperators

/-- Average finite-tape fallback failure mass over independent amplified source labels. -/
def effectiveJointFailureMass (N : ℕ) (hN : 0<N) (s M P B R t kBits a : ℕ)
    (C : Finset (Fin N)) (h : Fin N → Bool) : ℝ :=
  ∑ labels : Fin R → Fin N, (sourceLabelLaw N hN C).probOf labels *
    Effective.effectiveFailureMass N s M P B (aqRounds N C.card) t kBits a h (List.ofFn labels)

/-- Under the planted-progression and oracle assumptions, joint finite-tape failure mass is at
most `B * pmax ^ t` for a realized parameter at most `pmax < 1`. -/
theorem effectiveJointFailureMass_le (N : ℕ) (hN : 0<N) (s M P B R t kBits a : ℕ)
    (ha : a≤2^kBits) (C : Finset (Fin N)) (h : Fin N → Bool) (pmax : ℝ)
    (hpmax : Effective.realizedP kBits a≤pmax) (hmax : pmax<1)
    (hM : 2≤M) (hP : 0<P) (hPB : P≤B) (hb : s+(M-1)*P<N)
    (hC : aqProgressionSet N s M P⊆C) (horacle : ∀ x, h x=decide (x∈C)) :
    effectiveJointFailureMass N hN s M P B R t kBits a C h ≤ (B : ℝ)*pmax^t := by
  unfold effectiveJointFailureMass
  simp_rw [Effective.effectiveFailureMass_eq N s M P B _ t kBits a ha h]
  exact jointFailureMass_le N hN s M P B R t C h (Effective.realizedP kBits a) pmax
    (Effective.realizedP_range kBits a ha).1 hpmax hmax hM hP hPB hb hC horacle

end

namespace SourceRecord

noncomputable section
open scoped Classical BigOperators

/-- The probability that the optional output `a` equals `some z` under the finite distribution
`p`. -/
def actualHitMass {X Z : Type} [Fintype X] [DecidableEq Z]
    (p : FinDist X) (a : X → Option Z) (z : Z) : ℝ :=
  ∑ x, if a x = some z then p.prob x else 0

/-- The probability of an actual optional-output hit is nonnegative. -/
theorem actualHitMass_nonneg {X Z : Type} [Fintype X] [DecidableEq Z]
    (p : FinDist X) (a : X → Option Z) (z : Z) : 0 ≤ actualHitMass p a z := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact p.nonneg x
  · exact le_rfl

/-- The probability of an actual optional-output hit is at most one. -/
theorem actualHitMass_le_one {X Z : Type} [Fintype X] [DecidableEq Z]
    (p : FinDist X) (a : X → Option Z) (z : Z) : actualHitMass p a z ≤ 1 := by
  calc
    actualHitMass p a z ≤ ∑ x, p.prob x := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs
      · exact le_rfl
      · exact p.nonneg x
    _ = 1 := p.sum_one

/-- In `R` independent trials, the probability of at least one actual hit is at least `1 - (1 -
actualHitMass p a z) ^ R`. -/
theorem actual_retained_hit_lower {X Z : Type} [Fintype X] [DecidableEq X] [DecidableEq Z]
    (p : FinDist X) (a : X → Option Z) (z : Z) (R : ℕ) :
    1 - (1 - actualHitMass p a z) ^ R ≤
      ∑ ω : Fin R → X, if (∃ r, a (ω r) = some z) then p.probOf ω else 0 := by
  by_cases hpos : 0 < actualHitMass p a z
  · have hh := fresh_candidate_hit_lower p.prob a z (actualHitMass p a z)
      p.nonneg p.sum_one hpos (le_refl _) R
    simpa only [aqProductMass, FinDist.probOf] using! hh
  · have hz : actualHitMass p a z = 0 :=
      le_antisymm (le_of_not_gt hpos) (actualHitMass_nonneg p a z)
    rw [hz, sub_zero, one_pow, sub_self]
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · change 0 ≤ ∏ r, p.prob (ω r)
      exact Finset.prod_nonneg fun r _ => p.nonneg (ω r)
    · exact le_rfl

/-- The one-label probability that `aqAttempt` returns the target period under the amplified
source-label distribution. -/
def cfActualHitMass (N : ℕ) (hN : 0 < N) (C : Finset (Fin N))
    (h : Fin N → Bool) (s M B P : ℕ) : ℝ :=
  ∑ y : Fin N, if (aqAttempt h s M B y).1 = some P
    then (sourceLabelLaw N hN C).prob y else 0

/-- The target period occurs in a candidate record exactly when some sampled label produces it
in `aqAttempt`. -/
theorem cf_record_mem_iff {N R : ℕ} (h : Fin N → Bool) (s M B P : ℕ)
    (ω : Fin R → Fin N) :
    P ∈ aqCandidateRecord h s M B (List.ofFn ω) ↔
      ∃ r, (aqAttempt h s M B (ω r)).1 = some P := by
  rw [aqCandidateRecord_mem]
  constructor
  · rintro ⟨y, hy, hret⟩
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    exact ⟨r, hret⟩
  · rintro ⟨r, hret⟩
    exact ⟨ω r, List.mem_ofFn.mpr ⟨r, rfl⟩, hret⟩

/-- The probability that `R` source labels retain the target in the candidate record is at least
the repeated actual-hit bound. -/
theorem actual_cf_record_hit (N : ℕ) (hN : 0 < N) (C : Finset (Fin N))
    (h : Fin N → Bool) (s M B P R : ℕ) :
    1 - (1 - cfActualHitMass N hN C h s M B P) ^ R ≤
      ∑ ω : Fin R → Fin N,
        if P ∈ aqCandidateRecord h s M B (List.ofFn ω)
          then (sourceLabelLaw N hN C).probOf ω else 0 := by
  have hh := actual_retained_hit_lower (sourceLabelLaw N hN C)
    (fun y => (aqAttempt h s M B y).1) P R
  simpa only [cfActualHitMass, actualHitMass, cf_record_mem_iff] using! hh

/-- The continued-fraction field of the fallback trace retains the target with at least the
repeated actual-hit probability, even when later observations depend on the labels. -/
theorem fallback_actual_cf_hit (N : ℕ) (hN : 0 < N) (C : Finset (Fin N))
    (h : Fin N → Bool) (s M B P R : ℕ)
    (observations : (Fin R → Fin N) → List (Fin N → Bool)) :
    1 - (1 - cfActualHitMass N hN C h s M B P) ^ R ≤
      ∑ ω : Fin R → Fin N,
        if P ∈ (runWithFallback h s M B (aqRounds N C.card)
            (List.ofFn ω) (observations ω)).cfCandidates
          then (sourceLabelLaw N hN C).probOf ω else 0 := by
  simp_rw [fallback_cf_record]
  exact actual_cf_record_hit N hN C h s M B P R

end
end SourceRecord

namespace SourceNoise

noncomputable section
open scoped Classical BigOperators

/-- The set of register locations whose raw Boolean noise bit is true. -/
def rawSet {N : ℕ} (σ : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun i => σ i = true

/-- The source oracle obtained by exclusive-or of the planted-set indicator and the raw noise
stream. -/
def sourceXor {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool) : Fin N → Bool :=
  fun i => decide (i ∈ A) ^^ σ i

/-- The source oracle obtained by Boolean union of the planted-set indicator and the raw noise
stream. -/
def protectedUnion {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool) : Fin N → Bool :=
  fun i => decide (i ∈ A) || σ i

/-- The Boolean characteristic oracle of a finite marked set. -/
def setObserver {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun i => decide (i ∈ S)

/-- The raw noise set is disjoint from `A` exactly when every raw bit on `A` is false. -/
theorem disjoint_iff_all_false {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool) :
    Disjoint A (rawSet σ) ↔ ∀ i ∈ A, σ i = false := by
  constructor
  · intro h i hi
    cases hb : σ i with
    | false => rfl
    | true =>
        have hm : i ∈ rawSet σ := by simp [rawSet,hb]
        exact False.elim (Finset.disjoint_left.mp h hi hm)
  · intro hall
    apply Finset.disjoint_left.mpr
    intro i hi hm
    have hb : σ i = true := by
      simpa only [rawSet,Finset.mem_filter,Finset.mem_univ,true_and] using! hm
    rw [hall i hi] at hb
    cases hb

/-- The protected union oracle is the characteristic oracle of `A ∪ rawSet σ`. -/
theorem protectedUnion_eq_setObserver {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool) :
    protectedUnion A σ = setObserver (A ∪ rawSet σ) := by
  funext i
  by_cases hi : i ∈ A <;> cases hb : σ i <;>
    simp [protectedUnion,setObserver,rawSet,hi,hb]

/-- Exclusive-or noise and protected union give the same oracle when the raw noise set is
disjoint from the planted set. -/
theorem sourceXor_eq_protectedUnion {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool)
    (h : Disjoint A (rawSet σ)) : sourceXor A σ = protectedUnion A σ := by
  funext i
  by_cases hi : i ∈ A
  · have hb := (disjoint_iff_all_false A σ).mp h i hi
    simp [sourceXor,protectedUnion,hi,hb]
  · simp [sourceXor,protectedUnion,hi]

/-- For noise disjoint from the planted progression, the exclusive-or source equals the
characteristic oracle of the protected fresh marked set. -/
theorem sourceXor_eq_aqFreshMarked (N s M P : ℕ) (σ : Fin N → Bool)
    (h : Disjoint (aqProgressionSet N s M P) (rawSet σ)) :
    sourceXor (aqProgressionSet N s M P) σ =
      setObserver (aqFreshMarked N s M P σ) := by
  exact (sourceXor_eq_protectedUnion _ _ h).trans (protectedUnion_eq_setObserver _ _)

/-- The Bernoulli probability that the raw noise set equals `G`. -/
def rawFiberMass (N : ℕ) (G : Finset (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : ℝ :=
  ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
    (if rawSet σ = G then 1 else 0)

/-- The probability of the raw noise set `G` is `p ^ G.card * (1 - p) ^ (N - G.card)`. -/
theorem raw_fiber_mass (N : ℕ) (G : Finset (Fin N)) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) :
    rawFiberMass N G p hp hp1 = p^G.card*(1-p)^(N-G.card) := by
  have h := RawNoise.raw_overlay_fiber_mass N (∅ : Finset (Fin N)) G p hp hp1
    (Finset.disjoint_empty_left G)
  simpa only [rawFiberMass,RawNoise.noiseOutside,rawSet,Finset.notMem_empty,
    not_false_eq_true,true_and,Finset.card_empty,Nat.sub_zero] using! h

/-- The Bernoulli probability that the raw noise set is disjoint from the planted set `A`. -/
def disjointMass (N : ℕ) (A : Finset (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : ℝ :=
  ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
    (if Disjoint A (rawSet σ) then 1 else 0)

/-- Raw Bernoulli noise avoids every site in `A` with probability `(1 - p) ^ A.card`. -/
theorem disjoint_mass (N : ℕ) (A : Finset (Fin N)) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) : disjointMass N A p hp hp1 = (1-p)^A.card := by
  have hind (σ : Fin N → Bool) :
      (if Disjoint A (rawSet σ) then (1 : ℝ) else 0) =
        ∏ i : Fin N, (if i ∈ A → σ i = false then (1 : ℝ) else 0) := by
    rw [RawNoise.product_indicator]
    by_cases hd : Disjoint A (rawSet σ)
    · rw [if_pos hd, if_pos ((disjoint_iff_all_false A σ).mp hd)]
    · rw [if_neg hd, if_neg (fun hall => hd ((disjoint_iff_all_false A σ).mpr hall))]
  have hsite (i : Fin N) :
      (∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b *
        (if i ∈ A → b = false then (1 : ℝ) else 0)) =
        if i ∈ A then 1-p else 1 := by
    by_cases hi : i ∈ A <;> simp [bernoulliSiteLaw,hi]
  calc
    disjointMass N A p hp hp1 = ∑ σ : Fin N → Bool,
        (bernoulliStreamLaw N p hp hp1).prob σ *
          ∏ i : Fin N, (if i ∈ A → σ i = false then (1 : ℝ) else 0) := by
      unfold disjointMass
      simp_rw [hind]
    _ = ∏ i : Fin N, ∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b *
        (if i ∈ A → b = false then (1 : ℝ) else 0) :=
      aq_bernoulli_stream_independent N p hp hp1
        (fun (i : Fin N) (b : Bool) => if i ∈ A → b = false then (1 : ℝ) else 0)
    _ = ∏ i : Fin N, if i ∈ A then 1-p else 1 := by simp_rw [hsite]
    _ = (1-p)^A.card := by
      rw [Finset.prod_ite_mem_eq]
      simp only [Finset.prod_const]

/-- Noise restricted to the complement of `A` is disjoint from `A`. -/
theorem outside_disjoint {N : ℕ} (A : Finset (Fin N)) (σ : Fin N → Bool) :
    Disjoint A (RawNoise.noiseOutside A σ) := by
  apply Finset.disjoint_left.mpr
  intro i hi ho
  exact (Finset.mem_filter.mp ho).2.1 hi

/-- The normalized mass of the event `rawSet σ = G` conditioned on raw noise being disjoint from
`A`. -/
def conditionalSourceMass (N : ℕ) (A G : Finset (Fin N))
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : ℝ :=
  (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
    (if Disjoint A (rawSet σ) ∧ rawSet σ = G then 1 else 0)) /
      disjointMass N A p hp hp1

/-- The Bernoulli probability that the noise outside `A` equals `G`. -/
def outsideMass (N : ℕ) (A G : Finset (Fin N))
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : ℝ :=
  ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
    (if RawNoise.noiseOutside A σ = G then 1 else 0)

/-- For disjoint `A` and `G` and `p < 1`, the conditioned raw-source mass equals the
outside-noise mass. -/
theorem conditional_source_eq_outside_good (N : ℕ) (A G : Finset (Fin N))
    (p : ℝ) (hp : 0≤p) (hp1 : p<1) (hAG : Disjoint A G) :
    conditionalSourceMass N A G p hp hp1.le = outsideMass N A G p hp hp1.le := by
  have hind (σ : Fin N → Bool) :
      (Disjoint A (rawSet σ) ∧ rawSet σ = G) ↔ rawSet σ = G := by
    constructor
    · exact And.right
    · intro he
      exact ⟨by rw [he]; exact hAG,he⟩
  have hjoint : (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1.le).prob σ *
      (if Disjoint A (rawSet σ) ∧ rawSet σ = G then (1 : ℝ) else 0)) =
        rawFiberMass N G p hp hp1.le := by
    unfold rawFiberMass
    simp_rw [hind]
  have hcard : A.card+G.card ≤ N := by
    have h := Finset.card_le_card (Finset.subset_univ (A ∪ G))
    rw [Finset.card_union_of_disjoint hAG,Finset.card_univ,Fintype.card_fin] at h
    exact h
  have hexp : N-G.card = A.card+(N-A.card-G.card) := by omega
  have hq : (1-p)^A.card ≠ 0 := pow_ne_zero _ (ne_of_gt (sub_pos.mpr hp1))
  unfold conditionalSourceMass outsideMass
  rw [hjoint,raw_fiber_mass,disjoint_mass,
    RawNoise.raw_overlay_fiber_mass N A G p hp hp1.le hAG,hexp,pow_add]
  field_simp [hq]

/-- For `p < 1`, conditioning raw noise to avoid `A` gives the same subset masses as restricting
noise to the complement of `A`. -/
theorem conditional_source_eq_outside (N : ℕ) (A G : Finset (Fin N))
    (p : ℝ) (hp : 0≤p) (hp1 : p<1) :
    conditionalSourceMass N A G p hp hp1.le = outsideMass N A G p hp hp1.le := by
  by_cases hAG : Disjoint A G
  · exact conditional_source_eq_outside_good N A G p hp hp1 hAG
  · have hcond (σ : Fin N → Bool) : ¬(Disjoint A (rawSet σ) ∧ rawSet σ = G) := by
      rintro ⟨hdis,he⟩
      apply hAG
      rw [← he]
      exact hdis
    have hout (σ : Fin N → Bool) : RawNoise.noiseOutside A σ ≠ G := by
      intro he
      apply hAG
      rw [← he]
      exact outside_disjoint A σ
    unfold conditionalSourceMass outsideMass
    simp only [if_neg (hcond _),if_neg (hout _),mul_zero,Finset.sum_const_zero,zero_div]

/-- The probability that raw noise avoids `A` is positive when `p < 1`. -/
theorem disjoint_mass_pos (N : ℕ) (A : Finset (Fin N)) (p : ℝ)
    (hp : 0≤p) (hp1 : p<1) : 0 < disjointMass N A p hp hp1.le := by
  rw [disjoint_mass]
  exact pow_pos (sub_pos.mpr hp1) _

end
end SourceNoise

noncomputable section
open scoped Classical BigOperators

/-- The conjunction of raw subset weights, the disjoint exclusive-or identity, the avoidance
probability, and transport from conditioning to outside noise. -/
def RawBernoulliTransport : Prop :=
  (∀ (N : ℕ) (G : Finset (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1),
    SourceNoise.rawFiberMass N G p hp hp1 = p^G.card*(1-p)^(N-G.card)) ∧
  (∀ (N : ℕ) (A : Finset (Fin N)) (σ : Fin N → Bool),
    Disjoint A (SourceNoise.rawSet σ) →
      SourceNoise.sourceXor A σ = SourceNoise.protectedUnion A σ) ∧
  (∀ (N : ℕ) (A : Finset (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1),
    SourceNoise.disjointMass N A p hp hp1 = (1-p)^A.card) ∧
  (∀ (N : ℕ) (A G : Finset (Fin N)) (p : ℝ) (hp : 0≤p) (hp1 : p<1),
    SourceNoise.conditionalSourceMass N A G p hp hp1.le = SourceNoise.outsideMass N A G p hp hp1.le)

/-- Establish the raw Bernoulli transport identities for the error-stream model of
[Cornwell2014]. -/
theorem rawBernoulliTransport : RawBernoulliTransport :=
  ⟨SourceNoise.raw_fiber_mass, fun _ => SourceNoise.sourceXor_eq_protectedUnion,
    SourceNoise.disjoint_mass, SourceNoise.conditional_source_eq_outside⟩

/-- The conjunction of exact finite-tape Bernoulli transport, its bit cost, and convergence of
dyadic parameters to the requested parameter. -/
def EffectiveBernoulliTransport : Prop :=
  (∀ (N t k a : ℕ) (ha : a≤2^k) (σ : Multi.RawRounds N t),
    (∑ tapes : Effective.RawTapes N t k, (Effective.fairRoundsLaw N t k).prob tapes *
      (if (Effective.roundsRun N t k a tapes).1 = σ then 1 else 0)) =
      (Multi.roundsLaw N t (Effective.realizedP k a)
        (Effective.realizedP_range k a ha).1 (Effective.realizedP_range k a ha).2).prob σ) ∧
  (∀ (N t k a : ℕ) (tapes : Effective.RawTapes N t k),
    (Effective.roundsRun N t k a tapes).2 = N*t*k) ∧
  (∀ (p : ℝ) (_hp : 0≤p) (_hp1 : p≤1),
    Filter.Tendsto (fun k =>
      (Qatlib.Concepts.AmpTransform.ErrorStream.aqNextBernoulliThreshold k p : ℝ) /
        (2 : ℝ)^k) Filter.atTop (nhds p))

/-- Establish exact Bernoulli transport from finite fair tapes, the bit ledger, and convergence
of the effective parameters. -/
theorem effectiveBernoulliTransport : EffectiveBernoulliTransport :=
  ⟨Effective.roundsRun_fiber, Effective.roundsRun_bits,
    Qatlib.Concepts.FourierRecovery.ModularFourier.aqNext_effective_parameter_tendsto⟩

/-- The explicit size-128 example in which periods two and four with two disjoint noise sites
each yield the same marked oracle and both pass verification. -/
def FixedNoiseAmbiguity : Prop :=
  let G2 : Finset (Fin 128) := {8,12}
  let G4 : Finset (Fin 128) := {2,6}
  let C2 := aqProgressionSet 128 0 4 2 ∪ G2
  let C4 := aqProgressionSet 128 0 4 4 ∪ G4
  let h : Fin 128 → Bool := fun x => decide (x ∈ C2)
  G2.card=2 ∧ G4.card=2 ∧ Disjoint G2 (aqProgressionSet 128 0 4 2) ∧
    Disjoint G4 (aqProgressionSet 128 0 4 4) ∧ C2=C4 ∧ (2 : ℝ)<2*(4 : ℝ)/Real.pi ∧
    (aqVerify h 0 4 2).1=true ∧ (aqVerify h 0 4 4).1=true

/-- Establish the explicit fixed-noise ambiguity example with two different verified planted
periods. -/
theorem fixedNoiseAmbiguity : FixedNoiseAmbiguity := same_oracle_two_planted_periods

/-- Every candidate surviving fresh filtering already occurs in the initial list. -/
theorem freshRounds_subset {N : ℕ} (s M : ℕ) (observations : List (Fin N → Bool))
    (qs : List ℕ) : ∀ q ∈ (freshRounds s M observations qs).1, q∈qs := by
  induction observations generalizing qs with
  | nil => exact fun _ hq => hq
  | cons h hs ih =>
    intro q hq
    have hp := ih _ q hq
    exact ((prune_mem _ s M q qs).mp hp).1

/-- Every initial candidate passes `aqVerify` on the source oracle. -/
theorem initialCandidates_verified {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (q : ℕ) (hq : q∈initialCandidates h s M B k labels) :
    (aqVerify h s M q).1=true := by
  rcases List.mem_append.mp hq with hc | hp
  · rw [collect_outputs] at hc
    exact aqCandidateRecord_verified h s M B labels q hc
  · exact Pool.boundedPool_verified h s M B q hp

/-- Every candidate stored or returned at any stage of the fallback trace passes source-oracle
verification. -/
theorem fallback_all_verified {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (labels : List (Fin N)) (observations : List (Fin N → Bool)) (q : ℕ)
    (hq : q∈(runWithFallback h s M B k labels observations).cfCandidates ∨
      q∈(runWithFallback h s M B k labels observations).candidates ∨
      q∈(runWithFallback h s M B k labels observations).compatible ∨
      (runWithFallback h s M B k labels observations).result=some q) :
    (aqVerify h s M q).1=true := by
  rcases hq with hc | hi | hf | hout
  · exact fallback_cf_verified h s M B k labels observations q hc
  · exact initialCandidates_verified h s M B k labels q hi
  · exact initialCandidates_verified h s M B k labels q (freshRounds_subset s M observations _ q hf)
  · have he : uniqueOutput (freshRounds s M observations (initialCandidates h s M B k labels)).1 =
        some q := by simpa only [runWithFallback,uniquePaid_value] using! hout
    have hf := ((uniqueOutput_spec _ q).mp he).1
    exact initialCandidates_verified h s M B k labels q (freshRounds_subset s M observations _ q hf)

/-- The conjunction of fixed-noise denoising and ambiguity results, actual continued-fraction
hit retention, and verification of every candidate in a fallback trace. -/
def FixedCandidateTransport : Prop :=
  FullLayerCFDenoiseUniqueP ∧ FixedNoiseAmbiguity ∧
  (∀ (N : ℕ) (hN : 0<N) (C : Finset (Fin N)) (h : Fin N → Bool) (s M B P R : ℕ)
    (observations : (Fin R → Fin N) → List (Fin N → Bool)),
    1-(1-SourceRecord.cfActualHitMass N hN C h s M B P)^R ≤
      ∑ ω : Fin R → Fin N, if P ∈
        (runWithFallback h s M B (aqRounds N C.card) (List.ofFn ω) (observations ω)).cfCandidates
        then (sourceLabelLaw N hN C).probOf ω else 0) ∧
  (∀ (N : ℕ) (h : Fin N → Bool) (s M B k : ℕ) (labels : List (Fin N))
    (observations : List (Fin N → Bool)) (q : ℕ),
    (q∈(runWithFallback h s M B k labels observations).cfCandidates ∨
      q∈(runWithFallback h s M B k labels observations).candidates ∨
      q∈(runWithFallback h s M B k labels observations).compatible ∨
      (runWithFallback h s M B k labels observations).result=some q) → (aqVerify h s M q).1=true)

/-- Establish the fixed-candidate transport package, including hit retention and verification
throughout the fallback trace. -/
theorem fixedCandidateTransport : FixedCandidateTransport :=
  ⟨fullLayerCFDenoiseUniqueP_answer, fixedNoiseAmbiguity,
    SourceRecord.fallback_actual_cf_hit, fun _ => fallback_all_verified⟩

/-- The joint failure bounds for Bernoulli and finite-tape protected resampling, together with
exclusion of wrong returned periods under the planted-progression assumptions. -/
def ProtectedResamplingIdentification : Prop :=
  ∀ (N : ℕ) (hN : 0<N) (s M P B R t : ℕ) (C : Finset (Fin N)) (h : Fin N → Bool),
    2≤M → 0<P → P≤B → s+(M-1)*P<N →
    aqProgressionSet N s M P⊆C → (∀ x, h x=decide (x∈C)) →
    (∀ (p pmax : ℝ) (hp : 0≤p) (hpp : p≤pmax) (hmax : pmax<1),
      jointFailureMass N hN s M P B R t C h p hp (le_trans hpp hmax.le) ≤ (B : ℝ)*pmax^t) ∧
    (∀ (kBits a : ℕ) (_ha : a≤2^kBits) (pmax : ℝ),
      Effective.realizedP kBits a≤pmax → pmax<1 →
      effectiveJointFailureMass N hN s M P B R t kBits a C h ≤ (B : ℝ)*pmax^t) ∧
    (∀ (labels : List (Fin N)) (σ : Multi.RawRounds N t) (Q : ℕ), Q≠P →
      (runWithFallback h s M B (aqRounds N C.card) labels
        (List.ofFn (oracleRounds N s M P t σ))).result ≠ some Q)

/-- Establish the protected-resampling failure bounds and prove that every returned period
equals the planted period under the stated assumptions. -/
theorem protectedResamplingIdentification : ProtectedResamplingIdentification := by
  intro N hN s M P B R t C h hM hP hPB hb hC horacle
  have hmark (x : Fin N) (hx : x∈aqProgressionSet N s M P) : h x=true := by
    rw [horacle x]
    exact decide_eq_true (hC hx)
  exact ⟨fun p pmax hp hpp hmax =>
    jointFailureMass_le N hN s M P B R t C h p pmax hp hpp hmax hM hP hPB hb hC horacle,
    fun kBits a ha pmax hpmax hmax =>
      effectiveJointFailureMass_le N hN s M P B R t kBits a ha C h pmax hpmax hmax
        hM hP hPB hb hC horacle,
    fun labels σ Q hQP => fallback_wrong_zero N s M P B _ t h labels σ hM hP hPB hb hmark Q hQP⟩

/-- The query, source-gate, continued-fraction, and table-test bounds recorded by a single
fallback recovery trace. -/
def SameRunResources : Prop :=
  ∀ (N : ℕ) (h : Fin N → Bool) (s M B k : ℕ) (labels : List (Fin N))
    (observations : List (Fin N → Bool)),
    (runWithFallback h s M B k labels observations).bill.queries ≤
      labels.length*(k+3)+3*B+observations.length*N ∧
    (runWithFallback h s M B k labels observations).bill.sourceGates = labels.length*(3*k+2) ∧
    (runWithFallback h s M B k labels observations).bill.cfStages ≤ labels.length*(cfDepth N+1) ∧
    (runWithFallback h s M B k labels observations).bill.cfWork =
      labels.length*((cfDepth N+1)*(cfDepth N+2)/2) ∧
    (runWithFallback h s M B k labels observations).bill.tableTests ≤
      B+observations.length*(labels.length+B)*(M+1)+(labels.length+B)

/-- Establish all resource bounds for the same executable fallback recovery run. -/
theorem sameRunResources : SameRunResources := by
  intro N h s M B k labels observations
  exact ⟨fallback_query_cap h s M B k labels observations,
    fallback_counts h s M B k labels observations⟩

/-- For `0 ≤ pmax < 1`, the public failure bound `B * pmax ^ t` tends to zero as the number of
rounds tends to infinity. -/
theorem public_tail_tendsto (B : ℕ) (pmax : ℝ) (h0 : 0≤pmax) (h1 : pmax<1) :
    Filter.Tendsto (fun t : ℕ => (B : ℝ)*pmax^t) Filter.atTop (nhds 0) := by
  simpa only [mul_zero] using! (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul (B : ℝ)

/-- Combine raw Bernoulli transport, effective sampling, fixed-candidate transport, protected
identification, and resource accounting into one result. -/
theorem frontier1 :
    RawBernoulliTransport ∧ EffectiveBernoulliTransport ∧ FixedCandidateTransport ∧
      ProtectedResamplingIdentification ∧ SameRunResources :=
  ⟨rawBernoulliTransport,effectiveBernoulliTransport,fixedCandidateTransport,
    protectedResamplingIdentification,sameRunResources⟩

end

end Qatlib.Concepts.AmpTransform.ErrorStream
