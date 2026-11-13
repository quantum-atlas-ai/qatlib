/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch

/-!
# Certified Fidelity Search and Rounding

This module constructs rational water-level searches for a target fidelity.
`certifiedFidelityRun` checks the target range, finds a margin witness, and chooses a refinement
depth with a certified fidelity error and an explicit operation ledger. These constructions
support the water-filling approach to quantum rejection sampling described in
[OzolsRoettelerRoland2013]. Normalization and rational amplitude bounds connect the selected
level to exact resampling schedules and amplitude amplification [BrassardEtAl2002].

Dyadic rounding supplies mass and dot-product enclosures for `intervalDecision`.
`intervalFidelitySearch` uses exact comparisons on ambiguous steps and recovers the exact search
bracket. The remaining results bound rounding error, ambiguity counts, and plateau resolution,
and construct gap-separation rates from individual saturation pieces or finite segment chains.

## Main statements

* `certifiedFidelityRun_exists_iff_in_range`: characterizes successful runs by the target range
  check and positive tolerance.
* `frontier2`: gives bracket, fidelity-error, witness, and operation-count guarantees for a
  successful run.
* `certifiedSchedule_windows`: gives schedule bounds after source normalization.
* `intervalFidelitySearch_eq`: identifies interval search brackets with exact search brackets.
* `ambiguityCount_le`: bounds ambiguity counts using a positive gap-separation rate.
* `jointTermination_certifies`: combines precision bounds with at most one ambiguous plateau
  level.
* `fidelityGap_rate_across_segment_chain_abs`: propagates a common rate through a finite chain
  of matching pieces.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
open Qatlib.Concepts.Waterfill.LevelSearch
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver

open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch
open scoped BigOperators

/-- The lower fidelity endpoint, given by the squared source-target dot product divided by the
source squared norm, with value zero when that norm vanishes. -/
def computedPmin {m : ℕ} (π σ : Fin m → ℚ) : ℚ :=
  if (∑ j, (π j) ^ 2) = 0 then 0 else (∑ j, π j * σ j) ^ 2 / (∑ j, (π j) ^ 2)

/-- The computed lower fidelity endpoint is nonnegative. -/
theorem computedPmin_nonneg {m : ℕ} (π σ : Fin m → ℚ) : 0 ≤ computedPmin π σ := by
  unfold computedPmin
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- For nonnegative source entries and positive target entries, the fidelity at
`computedWaterHigh` equals `computedPmin`. -/
theorem computedFidelity_at_high {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    computedFidelity π σ (computedWaterHigh π σ) = computedPmin π σ := by
  have hs := computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)
  have hmassH : computedMass π σ (computedWaterHigh π σ) = ∑ j, (π j) ^ 2 := by
    simpa [computedMass] using! hs.2
  have hdotH : computedDot π σ (computedWaterHigh π σ) = ∑ j, π j * σ j := by
    unfold computedDot
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [waterFill_at_high π σ (fun i => ⟨hπ i, hσ i⟩) j]
    ring
  by_cases hz : (∑ j, (π j) ^ 2) = 0
  · simp [computedFidelity, hmassH, computedPmin, hz]
  · simp [computedFidelity, hmassH, hdotH, computedPmin, hz]

/-- Checks whether the target fidelity lies strictly above `computedPmin` and at most
`computedPmax`. -/
def targetRangeCheck {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) : Bool :=
  decide (computedPmin π σ < p ∧ p ≤ computedPmax π σ)

/-- A successful target range check places the target in `(computedPmin π σ, computedPmax π σ]`. -/
theorem targetRangeCheck_spec {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (h : targetRangeCheck π σ p = true) :
    computedPmin π σ < p ∧ p ≤ computedPmax π σ :=
  of_decide_eq_true h

/-- For positive source mass, a target above `computedPmin` gives the strict squared-dot-product
inequality needed for a fidelity bracket. -/
theorem pmin_lt_bracket {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hmass : 0 < ∑ j, (π j) ^ 2) (hmin : computedPmin π σ < p) :
    (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2) := by
  have hne : (∑ j, (π j) ^ 2) ≠ 0 := ne_of_gt hmass
  rw [computedPmin, if_neg hne] at hmin
  exact (div_lt_iff₀ hmass).mp hmin

/-- A margin candidate is an index with positive source entry whose source-target ratio
satisfies `fidelityReaches`. -/
def marginCandidate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i : Fin m) : Prop :=
  0 < π i ∧ fidelityReaches π σ p (π i / σ i)

/-- Tests positivity of a source entry and the squared-dot-product inequality at its
source-target ratio. -/
def marginCandidateTest {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i : Fin m) : Bool :=
  decide (0 < π i ∧
    computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))

/-- Every index passing `marginCandidateTest` is a margin candidate. -/
theorem marginCandidateTest_spec {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i : Fin m)
    (h : marginCandidateTest π σ p i = true) :
    marginCandidate π σ p i := by
  have h' := of_decide_eq_true h
  exact ⟨h'.1, h'.2⟩

/-- Every margin candidate passes `marginCandidateTest`. -/
theorem marginCandidateTest_of {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i : Fin m)
    (h : marginCandidate π σ p i) : marginCandidateTest π σ p i = true := by
  have h' : 0 < π i ∧
      computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i) :=
    ⟨h.1, h.2⟩
  exact decide_eq_true h'

/-- The operation ledger for one margin candidate test on a table with `m` entries. -/
def candidateTestLedger (m : ℕ) : CertifiedSearchLedger := ⟨1, m, m, 2⟩

/-- A margin scan result containing an optional witness, the number of tests, and an operation
ledger. -/
structure MarginScanResult (m : ℕ) where

  witness : Option (Fin m)

  tests : ℕ

  ledger : CertifiedSearchLedger
  deriving DecidableEq, Repr

/-- Scans every index in a list for margin candidates, returning the first successful index
together with total test and operation counts. -/
def marginScan {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) : List (Fin m) → MarginScanResult m
  | [] => ⟨none, 0, ⟨0, 0, 0, 0⟩⟩
  | i :: rest =>
      let r := marginScan π σ p rest
      let led := ledgerAdd r.ledger (candidateTestLedger m)
      if marginCandidateTest π σ p i then ⟨some i, r.tests + 1, led⟩
      else ⟨r.witness, r.tests + 1, led⟩

/-- A margin scan performs one test for each list entry. -/
theorem marginScan_tests {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (l : List (Fin m)) :
    (marginScan π σ p l).tests = l.length := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      simp only [marginScan]
      split <;> simp_all

/-- The margin scan ledger records one division, `m` mass reads, `m` dot reads, and two
comparisons per list entry. -/
theorem marginScan_ledger {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (l : List (Fin m)) :
    (marginScan π σ p l).ledger =
      ⟨l.length, m * l.length, m * l.length, 2 * l.length⟩ := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      simp only [marginScan]
      split <;> simp [ih, ledgerAdd, candidateTestLedger, Nat.mul_succ]

/-- A witness returned by a margin scan belongs to the scanned list and satisfies
`marginCandidate`. -/
theorem marginScan_sound {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (l : List (Fin m))
    {i : Fin m} (h : (marginScan π σ p l).witness = some i) :
    i ∈ l ∧ marginCandidate π σ p i := by
  induction l with
  | nil => simp [marginScan] at h
  | cons j rest ih =>
      by_cases htest : marginCandidateTest π σ p j = true
      · have h' : (some j) = some i := by simpa [marginScan, htest] using! h
        have hij : j = i := Option.some.inj h'
        subst hij
        exact ⟨by simp, marginCandidateTest_spec π σ p j htest⟩
      · have h' : (marginScan π σ p rest).witness = some i := by
          simpa [marginScan, htest] using! h
        obtain ⟨hin, hc⟩ := ih h'
        exact ⟨by simp [hin], hc⟩

/-- If a margin scan returns no witness, no index in its list is a margin candidate. -/
theorem marginScan_none {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (l : List (Fin m))
    (h : (marginScan π σ p l).witness = none) :
    ∀ i ∈ l, ¬ marginCandidate π σ p i := by
  induction l with
  | nil => simp
  | cons j rest ih =>
      by_cases htest : marginCandidateTest π σ p j = true
      · simp [marginScan, htest] at h
      · have h' : (marginScan π σ p rest).witness = none := by
          simpa [marginScan, htest] using! h
        intro i hin
        rcases List.mem_cons.mp hin with hEq | hin'
        · intro hc
          rw [hEq] at hc
          exact htest (marginCandidateTest_of π σ p j hc)
        · exact ih h' i hin'

/-- Searches all indices for a margin witness and records the scan costs. -/
def marginWitnessSearch {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) : MarginScanResult m :=
  marginScan π σ p (List.finRange m)

/-- The full margin witness search performs exactly `m` tests. -/
theorem marginWitnessSearch_count {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) :
    (marginWitnessSearch π σ p).tests = m := by
  show (marginScan π σ p (List.finRange m)).tests = m
  rw [marginScan_tests, List.length_finRange]

/-- A witness returned by the full search is a margin candidate. -/
theorem marginWitnessSearch_sound {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {i : Fin m}
    (h : (marginWitnessSearch π σ p).witness = some i) :
    marginCandidate π σ p i := by
  obtain ⟨hin, hc⟩ := marginScan_sound π σ p (List.finRange m) h
  exact hc

/-- If the full search returns no witness, no index is a margin candidate. -/
theorem marginWitnessSearch_none {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (h : (marginWitnessSearch π σ p).witness = none) :
    ∀ i : Fin m, ¬ marginCandidate π σ p i := by
  intro i
  exact marginScan_none π σ p (List.finRange m) h i (List.mem_finRange i)

/-- The optional margin witness obtained by scanning all indices. -/
def marginWitness {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) : Option (Fin m) :=
  (marginWitnessSearch π σ p).witness

/-- The rational power `2 ^ n` is at least `n + 1`. -/
theorem two_pow_ge_succ (n : ℕ) : (2 : ℚ) ^ n ≥ (n : ℚ) + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h2 : (2 : ℚ) ^ n * 2 ≥ ((n : ℚ) + 1) * 2 :=
        mul_le_mul_of_nonneg_right ih (by norm_num : (0 : ℚ) ≤ 2)
      rw [pow_succ]
      push_cast
      nlinarith

/-- Every rational number is bounded above by a natural power of two. -/
theorem exists_two_pow_ge {X : ℚ} : ∃ k : ℕ, (2 : ℚ) ^ k ≥ X := by
  obtain ⟨n, hn⟩ := exists_nat_gt X
  refine ⟨n, ?_⟩
  have h := two_pow_ge_succ n
  linarith

/-- The power-of-two threshold used to choose a fidelity search depth from the target,
tolerance, and witness index. -/
def requiredBound {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) : ℚ :=
  2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ / (ε * (π i) ^ 2)

/-- The least natural exponent whose power of two reaches a positive rational threshold, with
value zero for nonpositive thresholds. -/
def stepCount (X : ℚ) : ℕ :=
  if 0 < X then Nat.find (p := fun k => (2 : ℚ) ^ k ≥ X) exists_two_pow_ge else 0

/-- For a positive threshold, `stepCount` chooses an exponent whose power of two reaches that
threshold. -/
theorem stepCount_spec {X : ℚ} (hX : 0 < X) : (2 : ℚ) ^ stepCount X ≥ X := by
  rw [stepCount, if_pos hX]
  exact Nat.find_spec exists_two_pow_ge

/-- For a positive threshold, `stepCount` is no larger than any exponent whose power of two
reaches it. -/
theorem stepCount_min {X : ℚ} (hX : 0 < X) {k : ℕ} (hk : (2 : ℚ) ^ k ≥ X) :
    stepCount X ≤ k := by
  rw [stepCount, if_pos hX]
  by_contra hcon
  exact (Nat.find_min exists_two_pow_ge (by omega)) hk

/-- The step count is zero for a nonpositive threshold. -/
theorem stepCount_of_nonpos {X : ℚ} (hX : X ≤ 0) : stepCount X = 0 := by
  rw [stepCount, if_neg (not_lt.mpr hX)]

/-- An exponent is the step count if its power of two reaches the positive threshold and every
smaller exponent falls short. -/
theorem stepCount_eq_of {X : ℚ} (hX : 0 < X) {k : ℕ}
    (hk : (2 : ℚ) ^ k ≥ X) (hkmin : ∀ j : ℕ, j < k → (2 : ℚ) ^ j < X) :
    stepCount X = k := by
  rw [stepCount, if_pos hX]
  refine Nat.le_antisymm ?_ ?_
  · by_contra hcon
    have hlt : k < Nat.find (p := fun j => (2 : ℚ) ^ j ≥ X)
        (exists_two_pow_ge (X := X)) := by omega
    exact (Nat.find_min (exists_two_pow_ge (X := X)) hlt) hk
  · by_contra hcon
    have hlt : Nat.find (p := fun j => (2 : ℚ) ^ j ≥ X)
        (exists_two_pow_ge (X := X)) < k := by omega
    exact lt_irrefl _
      (lt_of_le_of_lt (Nat.find_spec (exists_two_pow_ge (X := X))) (hkmin _ hlt))

/-- The operation ledger for a fidelity search on `m` entries with `k` refinement steps. -/
def searchLedger (m k : ℕ) : CertifiedSearchLedger := ⟨m + k, m * k, m * k, k⟩

/-- The operation ledger for scanning all `m` margin candidates. -/
def scanLedger (m : ℕ) : CertifiedSearchLedger := ⟨m, m * m, m * m, 2 * m⟩

/-- The operation ledger for the final certificate computation on `m` entries. -/
def certificateLedger (m : ℕ) : CertifiedSearchLedger := ⟨0, 2 * m, 2 * m, 2⟩

/-- The total ledger obtained by adding search, margin scan, and certificate costs. -/
def runLedger (m k : ℕ) : CertifiedSearchLedger :=
  ledgerAdd (ledgerAdd (searchLedger m k) (scanLedger m)) (certificateLedger m)

/-- Expands the total run ledger into explicit division, mass-read, dot-read, and comparison
counts. -/
theorem runLedger_counts (m k : ℕ) :
    runLedger m k =
      ⟨2 * m + k, m * k + m * m + 2 * m, m * k + m * m + 2 * m, k + 2 * m + 2⟩ := by
  have hd : (runLedger m k).divisions = 2 * m + k := by
    simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]; omega
  have hm : (runLedger m k).massReads = m * k + m * m + 2 * m := by
    simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]
  have hdot : (runLedger m k).dotReads = m * k + m * m + 2 * m := by
    simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]
  have hc : (runLedger m k).comparisons = k + 2 * m + 2 := by
    simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]
  have h1 : runLedger m k = ⟨(runLedger m k).divisions, (runLedger m k).massReads,
      (runLedger m k).dotReads, (runLedger m k).comparisons⟩ := rfl
  rw [h1, hd, hm, hdot, hc]

/-- The total mass-read count is the sum of the search, scan, and certificate mass-read counts. -/
theorem runLedger_massReads (m k : ℕ) :
    (runLedger m k).massReads
      = (searchLedger m k).massReads + (scanLedger m).massReads
        + (certificateLedger m).massReads := by
  simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]

/-- The total dot-read count is the sum of the search, scan, and certificate dot-read counts. -/
theorem runLedger_dotReads (m k : ℕ) :
    (runLedger m k).dotReads
      = (searchLedger m k).dotReads + (scanLedger m).dotReads
        + (certificateLedger m).dotReads := by
  simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]

/-- The total comparison count is the sum of the search, scan, and certificate comparison
counts. -/
theorem runLedger_comparisons (m k : ℕ) :
    (runLedger m k).comparisons
      = (searchLedger m k).comparisons + (scanLedger m).comparisons
        + (certificateLedger m).comparisons := by
  simp only [runLedger, ledgerAdd, searchLedger, scanLedger, certificateLedger]

/-- The full margin witness search has ledger `scanLedger m`. -/
theorem marginWitnessSearch_ledger {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) :
    (marginWitnessSearch π σ p).ledger = scanLedger m := by
  show (marginScan π σ p (List.finRange m)).ledger = scanLedger m
  rw [marginScan_ledger]
  simp [scanLedger]

/-- A fidelity search result storing a selected level, bracket, witness index, refinement depth,
and operation ledger. -/
structure CertifiedFidelityRun (m : ℕ) where

  level : ℚ

  bracket : ℚ × ℚ

  witness : Fin m

  steps : ℕ

  ledger : CertifiedSearchLedger

/-- Runs the fidelity search when the range check passes, a margin witness exists, and its
required bound is positive. -/
def certifiedFidelityRun {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) :
    Option (CertifiedFidelityRun m) :=
  if targetRangeCheck π σ p = true then
    (marginWitness π σ p).bind fun i =>
      if 0 < requiredBound π σ p ε i then
        let k : ℕ := stepCount (requiredBound π σ p ε i)
        let b : ℚ × ℚ := fidelityBracket π σ p k
        some ⟨b.2, b, i, k,
          ledgerAdd (ledgerAdd (searchLedger m k) (marginWitnessSearch π σ p).ledger)
            (certificateLedger m)⟩
      else none
  else none

/-- A successful run satisfies the range and margin checks, its depth reaches the required
bound, and its level, bracket, and ledger have the prescribed values. -/
theorem certifiedFidelityRun_spec {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (h : certifiedFidelityRun π σ p ε = some r) :
    targetRangeCheck π σ p = true ∧
      marginCandidate π σ p r.witness ∧
      0 < requiredBound π σ p ε r.witness ∧
      (2 : ℚ) ^ r.steps ≥ requiredBound π σ p ε r.witness ∧
      r.bracket = fidelityBracket π σ p r.steps ∧
      r.level = (fidelityBracket π σ p r.steps).2 ∧
      r.ledger = runLedger m r.steps := by
  unfold certifiedFidelityRun at h
  split at h
  · next hR =>
    cases hWi : marginWitness π σ p with
    | none => simp [hWi] at h
    | some i =>
        rw [hWi] at h
        simp only [Option.bind] at h
        by_cases hX : 0 < requiredBound π σ p ε i
        · rw [if_pos hX] at h
          cases h
          refine ⟨hR, ?_, hX, ?_, rfl, rfl, ?_⟩
          · have hsearch : (marginWitnessSearch π σ p).witness = some i := by
              show marginWitness π σ p = some i
              exact hWi
            exact marginWitnessSearch_sound π σ p hsearch
          · exact stepCount_spec hX
          · rw [marginWitnessSearch_ledger]
            rfl
        · simp [hX] at h
  · simp at h

/-- A failed target range check makes `certifiedFidelityRun` return `none`. -/
theorem certifiedFidelityRun_none_of_range {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (h : targetRangeCheck π σ p = false) : certifiedFidelityRun π σ p ε = none := by
  rw [certifiedFidelityRun, h]
  rfl

/-- A nonpositive required bound for the selected witness makes `certifiedFidelityRun` return
`none`. -/
theorem certifiedFidelityRun_none_of_bound {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) {i : Fin m}
    (hw : marginWitness π σ p = some i) (hb : requiredBound π σ p ε i ≤ 0) :
    certifiedFidelityRun π σ p ε = none := by
  rw [certifiedFidelityRun]
  split
  · next hR =>
      rw [hw]
      simp only [Option.bind]
      split
      · next hc => exact (not_lt_of_ge hb hc).elim
      · rfl
  · rfl

/-- Absence of a margin witness makes `certifiedFidelityRun` return `none`. -/
theorem certifiedFidelityRun_none_of_no_witness {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (h : marginWitness π σ p = none) : certifiedFidelityRun π σ p ε = none := by
  rw [certifiedFidelityRun]
  split
  · next hR =>
      rw [h]
      rfl
  · rfl

/-- With nonnegative source entries, positive target entries, positive target fidelity, and a
positive witness entry, the required bound is positive exactly when the tolerance is
positive. -/
theorem requiredBound_sign {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hpi : 0 < π i) :
    (0 < requiredBound π σ p ε i) ↔ (0 < ε) := by
  have hsum : 0 < (∑ j, π j * σ j) := by
    have h1 : π i * σ i ≤ ∑ j, π j * σ j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hπ j) (hσ j).le) (Finset.mem_univ i)
    exact lt_of_lt_of_le (mul_pos hpi (hσ i)) h1
  have hhigh : 0 < computedWaterHigh π σ :=
    (computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)).1
  have hnum : 0 < 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ := by
    have h2 : 0 < 2 * (∑ j, π j * σ j) := by positivity
    exact mul_pos (mul_pos h2 hp) hhigh
  have hpi2 : 0 < (π i) ^ 2 := sq_pos_of_pos hpi
  constructor
  · intro hpos
    have hDne : ε * (π i) ^ 2 ≠ 0 := by
      intro hz
      have hz' : requiredBound π σ p ε i = 0 := by rw [requiredBound, hz, div_zero]
      linarith [hz', hpos]
    have hDpos : 0 < ε * (π i) ^ 2 := by
      by_contra hcon
      have hDle : ε * (π i) ^ 2 ≤ 0 := le_of_not_gt hcon
      by_cases hDz : ε * (π i) ^ 2 = 0
      · have hz' : requiredBound π σ p ε i = 0 := by rw [requiredBound, hDz, div_zero]
        linarith [hz', hpos]
      · have hDneg : ε * (π i) ^ 2 < 0 := lt_of_le_of_ne hDle hDz
        have hneg : requiredBound π σ p ε i < 0 := by
          rw [requiredBound]
          exact div_neg_of_pos_of_neg hnum hDneg
        linarith [hneg, hpos]
    have hε : 0 < ε := by
      rcases mul_pos_iff.mp hDpos with h | h
      · exact h.1
      · exact ((not_lt_of_ge hpi2.le) h.2).elim
    exact hε
  · intro hε
    have hDpos : 0 < ε * (π i) ^ 2 := mul_pos hε hpi2
    rw [requiredBound]
    exact div_pos hnum hDpos

/-- For nonnegative source entries and positive target entries, a successful run exists exactly
when the range check passes, a margin candidate exists, and the tolerance is positive. -/
theorem certifiedFidelityRun_exists_iff {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    (∃ r : CertifiedFidelityRun m, certifiedFidelityRun π σ p ε = some r) ↔
      targetRangeCheck π σ p = true ∧ (∃ i : Fin m, marginCandidate π σ p i) ∧ 0 < ε := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε hr
    have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
    have hp : 0 < p := lt_of_le_of_lt (computedPmin_nonneg π σ) hmin
    have hε : 0 < ε :=
      (requiredBound_sign π σ p ε r.witness hπ hσ hp hmargin.1).mp hX
    exact ⟨hR, ⟨r.witness, hmargin⟩, hε⟩
  · rintro ⟨hR, ⟨i, hmargin⟩, hε⟩
    have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
    have hp : 0 < p := lt_of_le_of_lt (computedPmin_nonneg π σ) hmin
    cases hm : marginWitness π σ p with
    | none =>
        exact False.elim ((marginWitnessSearch_none π σ p
          (by simpa [marginWitness] using! hm) i) hmargin)
    | some i' =>
        have hmargin' : marginCandidate π σ p i' := by
          apply marginWitnessSearch_sound π σ p
          show (marginWitnessSearch π σ p).witness = some i'
          simpa [marginWitness] using! hm
        have hX : 0 < requiredBound π σ p ε i' :=
          (requiredBound_sign π σ p ε i' hπ hσ hp hmargin'.1).mpr hε
        refine ⟨⟨(fidelityBracket π σ p (stepCount (requiredBound π σ p ε i'))).2,
            fidelityBracket π σ p (stepCount (requiredBound π σ p ε i')), i',
            stepCount (requiredBound π σ p ε i'),
            ledgerAdd (ledgerAdd
              (searchLedger m (stepCount (requiredBound π σ p ε i')))
              (marginWitnessSearch π σ p).ledger) (certificateLedger m)⟩, ?_⟩
        rw [certifiedFidelityRun, if_pos hR, hm]
        simp only [Option.bind]
        rw [if_pos hX]

/-- The level returned by a successful run equals `selectedLevel` at the run's refinement depth. -/
theorem certifiedFidelityRun_level_is_selectedLevel {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (h : certifiedFidelityRun π σ p ε = some r) :
    r.level = selectedLevel π σ p r.steps := by
  have hlev := certifiedFidelityRun_spec π σ p ε h
  obtain ⟨-, -, -, -, -, hlevel, -⟩ := hlev
  rw [hlevel]
  rfl

/-- The finite set of indices with strictly positive source entries. -/
def sourceSupport {m : ℕ} (π : Fin m → ℚ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => 0 < π j)

/-- The minimum source-target ratio over the nonempty positive source support. -/
def minSourceRatio {m : ℕ} (π σ : Fin m → ℚ) (hS : (sourceSupport π).Nonempty) : ℚ :=
  Finset.min' ((sourceSupport π).image (fun j => π j / σ j)) (hS.image (fun j => π j / σ j))

/-- The minimum source ratio is at most the ratio at every index in the positive source support. -/
theorem minSourceRatio_le {m : ℕ} (π σ : Fin m → ℚ) {hS : (sourceSupport π).Nonempty}
    {j : Fin m} (hj : j ∈ sourceSupport π) :
    minSourceRatio π σ hS ≤ π j / σ j := by
  have him : π j / σ j ∈ (sourceSupport π).image (fun j => π j / σ j) :=
    Finset.mem_image.mpr ⟨j, hj, rfl⟩
  exact Finset.min'_le ((sourceSupport π).image (fun j => π j / σ j)) _ him

/-- Some index in the positive source support attains `minSourceRatio`. -/
theorem minSourceRatio_mem {m : ℕ} (π σ : Fin m → ℚ) {hS : (sourceSupport π).Nonempty} :
    ∃ j ∈ sourceSupport π, π j / σ j = minSourceRatio π σ hS := by
  have him : minSourceRatio π σ hS ∈ (sourceSupport π).image (fun j => π j / σ j) :=
    Finset.min'_mem ((sourceSupport π).image (fun j => π j / σ j))
      (hS.image (fun j => π j / σ j))
  obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp him
  exact ⟨j, hj, hval⟩

/-- The minimum source ratio is positive when all target entries are positive. -/
theorem minSourceRatio_pos {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ j, 0 < σ j)
    {hS : (sourceSupport π).Nonempty} :
    0 < minSourceRatio π σ hS := by
  obtain ⟨j, hj, hval⟩ := minSourceRatio_mem π σ
  have hpi : 0 < π j := (Finset.mem_filter.mp hj).2
  rw [← hval]
  exact div_pos hpi (hσ j)

/-- Nonempty positive source support and positive target entries imply `computedPmax` is
positive. -/
theorem computedPmax_pos_of_support {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ j, 0 < σ j)
    (hS : (sourceSupport π).Nonempty) : 0 < computedPmax π σ := by
  obtain ⟨j, hj⟩ := hS
  have hpi : 0 < π j := (Finset.mem_filter.mp hj).2
  have hsum : 0 < ∑ i, (if 0 < π i then σ i ^ 2 else 0) := by
    apply (Finset.sum_pos_iff_of_nonneg (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => if 0 < π i then σ i ^ 2 else 0)
      (fun i _ => by
        by_cases hi : 0 < π i
        · simp only [if_pos hi]
          positivity
        · simp only [if_neg hi]
          norm_num)).2
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simp only [if_pos hpi]
    exact sq_pos_of_pos (hσ j)
  simpa [computedPmax] using! hsum

/-- A positive upper fidelity endpoint implies nonempty positive source support. -/
theorem sourceSupport_nonempty {m : ℕ} (π σ : Fin m → ℚ)
    (hmax : 0 < computedPmax π σ) : (sourceSupport π).Nonempty := by
  have hsum : 0 < ∑ i, (if 0 < π i then σ i ^ 2 else 0) := by
    simpa [computedPmax] using! hmax
  have hex : ∃ i : Fin m, 0 < (if 0 < π i then σ i ^ 2 else 0) := by
    have h := (Finset.sum_pos_iff_of_nonneg (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => if 0 < π i then σ i ^ 2 else 0)
      (fun i _ => by
        by_cases hi : 0 < π i
        · simp only [if_pos hi]
          positivity
        · simp only [if_neg hi]
          norm_num)).mp hsum
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, hi⟩
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩⟩
  by_cases h : 0 < π j
  · exact h
  · rw [if_neg h] at hj
    exact absurd hj (lt_irrefl 0)

/-- At the minimum source ratio, water filling equals that ratio times the target on positive
source entries and vanishes elsewhere. -/
theorem waterFill_at_minSourceRatio {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {hS : (sourceSupport π).Nonempty} (j : Fin m) :
    waterFill π σ (minSourceRatio π σ hS) j =
      if 0 < π j then (minSourceRatio π σ hS) * σ j else 0 := by
  by_cases hj : 0 < π j
  · have hmem : j ∈ sourceSupport π :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hle : minSourceRatio π σ hS ≤ π j / σ j := minSourceRatio_le π σ hmem
    have hmul : (minSourceRatio π σ hS) * σ j ≤ π j :=
      (le_div_iff₀ (hσ j)).mp hle
    rw [waterFill, min_eq_right hmul, if_pos hj]
  · have hzero : π j = 0 := by
      by_contra hcon
      exact hj (lt_of_le_of_ne (hπ j) (Ne.symm hcon))
    have hnonneg : 0 ≤ (minSourceRatio π σ hS) * σ j :=
      mul_nonneg (minSourceRatio_pos π σ hσ (hS := hS)).le (hσ j).le
    rw [waterFill, if_neg hj, hzero, min_eq_left hnonneg]

/-- At the minimum source ratio, the filled mass equals its square times `computedPmax`. -/
theorem computedMass_at_minSourceRatio {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {hS : (sourceSupport π).Nonempty} :
    computedMass π σ (minSourceRatio π σ hS) =
      (minSourceRatio π σ hS) ^ 2 * computedPmax π σ := by
  unfold computedMass computedWaterEnergy computedPmax
  have hpoint : ∀ j : Fin m,
      (waterFill π σ (minSourceRatio π σ hS) j) ^ 2 =
        (minSourceRatio π σ hS) ^ 2 * (if 0 < π j then σ j ^ 2 else 0) := by
    intro j
    rw [waterFill_at_minSourceRatio π σ hπ hσ j]
    split <;> ring
  calc
    (∑ i, (waterFill π σ (minSourceRatio π σ hS) i) ^ 2)
        = ∑ i, (minSourceRatio π σ hS) ^ 2 * (if 0 < π i then σ i ^ 2 else 0) :=
          Finset.sum_congr rfl fun i _ => hpoint i
    _ = (minSourceRatio π σ hS) ^ 2 * ∑ i, (if 0 < π i then σ i ^ 2 else 0) := by
          rw [Finset.mul_sum]
    _ = (minSourceRatio π σ hS) ^ 2 * computedPmax π σ := rfl

/-- At the minimum source ratio, the filled dot product equals that ratio times `computedPmax`. -/
theorem computedDot_at_minSourceRatio {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {hS : (sourceSupport π).Nonempty} :
    computedDot π σ (minSourceRatio π σ hS) =
      (minSourceRatio π σ hS) * computedPmax π σ := by
  unfold computedDot computedPmax
  have hpoint : ∀ j : Fin m,
      σ j * waterFill π σ (minSourceRatio π σ hS) j =
        (minSourceRatio π σ hS) * (if 0 < π j then σ j ^ 2 else 0) := by
    intro j
    rw [waterFill_at_minSourceRatio π σ hπ hσ j]
    split <;> ring
  calc
    (∑ i, σ i * waterFill π σ (minSourceRatio π σ hS) i)
        = ∑ i, (minSourceRatio π σ hS) * (if 0 < π i then σ i ^ 2 else 0) :=
          Finset.sum_congr rfl fun i _ => hpoint i
    _ = (minSourceRatio π σ hS) * ∑ i, (if 0 < π i then σ i ^ 2 else 0) := by
          rw [Finset.mul_sum]
    _ = (minSourceRatio π σ hS) * computedPmax π σ := rfl

/-- At the minimum source ratio, the computed fidelity equals `computedPmax`. -/
theorem computedFidelity_at_minSourceRatio {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {hS : (sourceSupport π).Nonempty} :
    computedFidelity π σ (minSourceRatio π σ hS) = computedPmax π σ := by
  have hmax : 0 < computedPmax π σ := computedPmax_pos_of_support π σ hσ hS
  have hmass : computedMass π σ (minSourceRatio π σ hS) > 0 := by
    rw [computedMass_at_minSourceRatio π σ hπ hσ]
    have hpos := minSourceRatio_pos π σ hσ (hS := hS)
    positivity
  unfold computedFidelity
  rw [if_neg (ne_of_gt hmass)]
  rw [computedDot_at_minSourceRatio π σ hπ hσ,
    computedMass_at_minSourceRatio π σ hπ hσ]
  have hne2 : (minSourceRatio π σ hS) ^ 2 * computedPmax π σ ≠ 0 := by
    have hpos := minSourceRatio_pos π σ hσ (hS := hS)
    positivity
  rw [div_eq_iff hne2]
  ring

/-- The minimum source ratio satisfies `fidelityReaches` for every positive target at most
`computedPmax`, under the stated positivity assumptions. -/
theorem fidelityReaches_at_minSourceRatio {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hpq : p ≤ computedPmax π σ)
    {hS : (sourceSupport π).Nonempty} :
    fidelityReaches π σ p (minSourceRatio π σ hS) := by
  have hmax : 0 < computedPmax π σ := lt_of_lt_of_le hp hpq
  unfold fidelityReaches
  rw [computedDot_at_minSourceRatio π σ hπ hσ,
    computedMass_at_minSourceRatio π σ hπ hσ]
  have hsq : (minSourceRatio π σ hS * computedPmax π σ) ^ 2
      = (minSourceRatio π σ hS) ^ 2 * computedPmax π σ ^ 2 := by ring
  rw [hsq]
  have hkey : (minSourceRatio π σ hS) ^ 2 * computedPmax π σ * computedPmax π σ
      ≥ (minSourceRatio π σ hS) ^ 2 * computedPmax π σ * p := by
    have hnonneg : 0 ≤ (minSourceRatio π σ hS) ^ 2 * computedPmax π σ :=
      mul_nonneg (sq_nonneg _) hmax.le
    exact mul_le_mul_of_nonneg_left hpq hnonneg
  calc
    (minSourceRatio π σ hS) ^ 2 * computedPmax π σ ^ 2
        = (minSourceRatio π σ hS) ^ 2 * computedPmax π σ * computedPmax π σ := by ring
    _ ≥ (minSourceRatio π σ hS) ^ 2 * computedPmax π σ * p := hkey
    _ = p * ((minSourceRatio π σ hS) ^ 2 * computedPmax π σ) := by ring

/-- For nonnegative source entries and positive target entries, every positive target at most
`computedPmax` has a margin candidate. -/
theorem marginCandidate_exists {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hpq : p ≤ computedPmax π σ) :
    ∃ i : Fin m, marginCandidate π σ p i := by
  have hmax : 0 < computedPmax π σ := lt_of_lt_of_le hp hpq
  have hS : (sourceSupport π).Nonempty := sourceSupport_nonempty π σ hmax
  obtain ⟨j, hj, hval⟩ := minSourceRatio_mem π σ (hS := hS)
  have hpi : 0 < π j := (Finset.mem_filter.mp hj).2
  refine ⟨j, hpi, ?_⟩
  have hreach := fidelityReaches_at_minSourceRatio π σ p hπ hσ hp hpq (hS := hS)
  rw [← hval] at hreach
  exact hreach

/-- If a margin candidate exists, the full witness search does not return `none`. -/
theorem marginWitnessSearch_some {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (h : ∃ i : Fin m, marginCandidate π σ p i) :
    (marginWitnessSearch π σ p).witness ≠ none := by
  intro hnone
  obtain ⟨i, hc⟩ := h
  exact (marginWitnessSearch_none π σ p hnone i) hc

/-- For nonnegative source entries and positive target entries, a successful run exists exactly
when the target range check passes and the tolerance is positive. -/
theorem certifiedFidelityRun_exists_iff_in_range {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    (∃ r : CertifiedFidelityRun m, certifiedFidelityRun π σ p ε = some r) ↔
      targetRangeCheck π σ p = true ∧ 0 < ε := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε hr
    have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
    have hp : 0 < p := lt_of_le_of_lt (computedPmin_nonneg π σ) hmin
    have hε : 0 < ε :=
      (requiredBound_sign π σ p ε r.witness hπ hσ hp hmargin.1).mp hX
    exact ⟨hR, hε⟩
  · rintro ⟨hR, hε⟩
    have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
    have hp : 0 < p := lt_of_le_of_lt (computedPmin_nonneg π σ) hmin
    have hpq : p ≤ computedPmax π σ := (targetRangeCheck_spec π σ p hR).2
    have hne : (marginWitnessSearch π σ p).witness ≠ none :=
      marginWitnessSearch_some π σ p (marginCandidate_exists π σ p hπ hσ hp hpq)
    cases hm : marginWitness π σ p with
    | none => exact False.elim (hne (by simpa [marginWitness] using! hm))
    | some i' =>
        have hmargin' : marginCandidate π σ p i' := by
          apply marginWitnessSearch_sound π σ p
          show (marginWitnessSearch π σ p).witness = some i'
          simpa [marginWitness] using! hm
        have hX : 0 < requiredBound π σ p ε i' :=
          (requiredBound_sign π σ p ε i' hπ hσ hp hmargin'.1).mpr hε
        refine ⟨⟨(fidelityBracket π σ p (stepCount (requiredBound π σ p ε i'))).2,
            fidelityBracket π σ p (stepCount (requiredBound π σ p ε i')), i',
            stepCount (requiredBound π σ p ε i'),
            ledgerAdd (ledgerAdd
              (searchLedger m (stepCount (requiredBound π σ p ε i')))
              (marginWitnessSearch π σ p).ledger) (certificateLedger m)⟩, ?_⟩
        rw [certifiedFidelityRun, if_pos hR, hm]
        simp only [Option.bind]
        rw [if_pos hX]

/-- A successful run has an ordered bracket of the prescribed dyadic width, opposite endpoint
tests, bounded mass variation, fidelity error at most `ε`, a valid witness, and explicit
operation counts. -/
theorem frontier2 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {r : CertifiedFidelityRun m} (h : certifiedFidelityRun π σ p ε = some r) :

    0 ≤ r.bracket.1 ∧ r.bracket.1 ≤ r.bracket.2 ∧ r.bracket.2 ≤ computedWaterHigh π σ ∧
      r.bracket.2 - r.bracket.1 = computedWaterHigh π σ / (2 : ℚ) ^ r.steps ∧
      fidelityReaches π σ p r.bracket.1 ∧ ¬ fidelityReaches π σ p r.bracket.2 ∧

    0 ≤ computedMass π σ r.bracket.1 ∧
      computedMass π σ r.bracket.1 ≤ computedMass π σ r.bracket.2 ∧
      computedMass π σ r.bracket.2 ≤ (∑ j, (π j) ^ 2) ∧
      computedMass π σ r.bracket.2 - computedMass π σ r.bracket.1 ≤
        2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ r.steps) ∧

    |computedFidelity π σ r.level - p| ≤ ε ∧

    0 < π r.witness ∧ fidelityReaches π σ p (π r.witness / σ r.witness) ∧

    r.ledger = ⟨2 * m + r.steps, m * r.steps + m * m + 2 * m,
      m * r.steps + m * m + 2 * m, r.steps + 2 * m + 2⟩ := by
  obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε h
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le

  have hmass_pos : 0 < (∑ j, (π j) ^ 2) := by
    have h1 : (π r.witness) ^ 2 ≤ ∑ j, (π j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ r.witness)
    exact lt_of_lt_of_le (sq_pos_of_pos hmargin.1) h1

  have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
  have hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2) :=
    pmin_lt_bracket π σ p hmass_pos hmin
  have hp : 0 < p := lt_of_le_of_lt (computedPmin_nonneg π σ) hmin

  have hsum_pos : 0 < (∑ j, π j * σ j) := by
    have h1 : π r.witness * σ r.witness ≤ ∑ j, π j * σ j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hπ j) (hσ' j)) (Finset.mem_univ r.witness)
    exact lt_of_lt_of_le (mul_pos hmargin.1 (hσ r.witness)) h1
  have hhigh_pos : 0 < computedWaterHigh π σ :=
    (computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)).1
  have hnum_pos : 0 < 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ := by positivity

  have hden_ne : ε * (π r.witness) ^ 2 ≠ 0 := by
    intro hz
    have : requiredBound π σ p ε r.witness = 0 := by
      rw [requiredBound, hz, div_zero]
    linarith
  have hmul : requiredBound π σ p ε r.witness * (ε * (π r.witness) ^ 2)
      = 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ := by
    rw [requiredBound]
    exact div_mul_cancel₀ _ hden_ne
  have hXD : 0 < requiredBound π σ p ε r.witness * (ε * (π r.witness) ^ 2) := by
    rw [hmul]
    exact hnum_pos
  have hden_pos : 0 < ε * (π r.witness) ^ 2 := by
    rcases mul_pos_iff.mp hXD with hpos | hneg
    · exact hpos.2
    · exact ((not_lt_of_ge hX.le) hneg.1).elim
  have hε : 0 < ε := by
    have hpi2 : 0 < (π r.witness) ^ 2 := sq_pos_of_pos hmargin.1
    rcases mul_pos_iff.mp hden_pos with hpos | hneg
    · exact hpos.1
    · exact ((not_lt_of_ge hpi2.le) hneg.2).elim

  have hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
      ≤ ε * (π r.witness) ^ 2 * (2 : ℚ) ^ r.steps := by
    calc
      2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
          = requiredBound π σ p ε r.witness * (ε * (π r.witness) ^ 2) := hmul.symm
      _ ≤ (2 : ℚ) ^ r.steps * (ε * (π r.witness) ^ 2) :=
          mul_le_mul_of_nonneg_right hpow hden_pos.le
      _ = ε * (π r.witness) ^ 2 * (2 : ℚ) ^ r.steps := by ring

  have hprops := certifiedFidelityBracket_props π σ p hπ hσ hrange r.steps
  have henergy := certifiedFidelity_energy π σ p r.steps hπ hσ hrange
  have herr := certifiedFidelity_error π σ p ε r.witness r.steps hπ hσ hp hε hmargin.1 hrange
    hmargin.2 hsteps
  rw [hbr, hlev] at *
  refine ⟨hprops.1, hprops.2.1, hprops.2.2.1, hprops.2.2.2.1, hprops.2.2.2.2.1,
    hprops.2.2.2.2.2, henergy.1, henergy.2.1, henergy.2.2.1, henergy.2.2.2, herr,
    hmargin.1, hmargin.2, ?_⟩
  rw [hled, runLedger_counts]

/-- Collects the minimum source ratio formulas, existence of a margin witness, and existence
criterion for a successful run with an in-range target and positive tolerance. -/
theorem frontier3 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hS : (sourceSupport π).Nonempty)
    (hR : targetRangeCheck π σ p = true) (hε : 0 < ε) :

    0 < minSourceRatio π σ hS ∧
      (∃ i : Fin m, 0 < π i ∧ π i / σ i = minSourceRatio π σ hS) ∧
      (∀ j : Fin m, 0 < π j → minSourceRatio π σ hS ≤ π j / σ j) ∧

      (∀ j : Fin m, waterFill π σ (minSourceRatio π σ hS) j =
        if 0 < π j then (minSourceRatio π σ hS) * σ j else 0) ∧

      computedMass π σ (minSourceRatio π σ hS) =
        (minSourceRatio π σ hS) ^ 2 * computedPmax π σ ∧
      computedDot π σ (minSourceRatio π σ hS) =
        (minSourceRatio π σ hS) * computedPmax π σ ∧

      computedFidelity π σ (minSourceRatio π σ hS) = computedPmax π σ ∧

    (∃ i : Fin m, marginCandidate π σ p i) ∧

    (∃ r : CertifiedFidelityRun m, certifiedFidelityRun π σ p ε = some r) ∧

    ((∃ r : CertifiedFidelityRun m, certifiedFidelityRun π σ p ε = some r) ↔
      targetRangeCheck π σ p = true ∧ 0 < ε) := by
  have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
  have hp : 0 < p := lt_of_le_of_lt (computedPmin_nonneg π σ) hmin
  have hpq : p ≤ computedPmax π σ := (targetRangeCheck_spec π σ p hR).2
  have hpos := minSourceRatio_pos π σ hσ (hS := hS)
  obtain ⟨j, hj, hval⟩ := minSourceRatio_mem π σ (hS := hS)
  have hpi : 0 < π j := (Finset.mem_filter.mp hj).2
  have hmass := computedMass_at_minSourceRatio π σ hπ hσ (hS := hS)
  have hdot := computedDot_at_minSourceRatio π σ hπ hσ (hS := hS)
  have hfid := computedFidelity_at_minSourceRatio π σ hπ hσ (hS := hS)
  have hclip := waterFill_at_minSourceRatio π σ hπ hσ (hS := hS)
  have hle : ∀ j : Fin m, 0 < π j → minSourceRatio π σ hS ≤ π j / σ j := by
    intro j hj
    exact minSourceRatio_le π σ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  have hmargin : ∃ i : Fin m, marginCandidate π σ p i :=
    marginCandidate_exists π σ p hπ hσ hp hpq
  have hrun : ∃ r : CertifiedFidelityRun m, certifiedFidelityRun π σ p ε = some r :=
    (certifiedFidelityRun_exists_iff_in_range π σ p ε hπ hσ).mpr ⟨hR, hε⟩
  have hiff := certifiedFidelityRun_exists_iff_in_range π σ p ε hπ hσ
  refine ⟨hpos, ⟨j, hpi, hval⟩, hle, hclip, hmass, hdot, hfid, hmargin, hrun, hiff⟩

/-- The rational dyadic grid point `H * j / 2 ^ k`. -/
def gridPoint (H : ℚ) (k j : ℕ) : ℚ :=
  H * (j : ℚ) / (2 : ℚ) ^ k

/-- The zeroth dyadic grid point is zero. -/
theorem gridPoint_zero (H : ℚ) (k : ℕ) : gridPoint H k 0 = 0 := by
  simp [gridPoint]

/-- The grid point of index one at depth zero is `H`. -/
theorem gridPoint_one (H : ℚ) : gridPoint H 0 1 = H := by
  simp [gridPoint]

/-- Dyadic grid points are nonnegative when the grid height is nonnegative. -/
theorem gridPoint_nonneg {H : ℚ} (hH : 0 ≤ H) {k j : ℕ} : 0 ≤ gridPoint H k j := by
  unfold gridPoint
  positivity

/-- At fixed depth, grid points are monotone in their index when the grid height is nonnegative. -/
theorem gridPoint_mono {H : ℚ} (hH : 0 ≤ H) {k : ℕ} {j j' : ℕ} (h : j ≤ j') :
    gridPoint H k j ≤ gridPoint H k j' := by
  have hj : (j : ℚ) ≤ (j' : ℚ) := by exact_mod_cast h
  have hpow : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  have hdiv : (j : ℚ) / (2 : ℚ) ^ k ≤ (j' : ℚ) / (2 : ℚ) ^ k :=
    div_le_div_of_nonneg_right hj hpow.le
  calc gridPoint H k j = H * ((j : ℚ) / (2 : ℚ) ^ k) := by
        simp only [gridPoint]
        field_simp
    _ ≤ H * ((j' : ℚ) / (2 : ℚ) ^ k) := mul_le_mul_of_nonneg_left hdiv hH
    _ = gridPoint H k j' := by
        simp only [gridPoint]
        field_simp

/-- The midpoint of consecutive depth-`k` grid points is the intervening odd-indexed point at
depth `k + 1`. -/
theorem gridPoint_mid {H : ℚ} (k a : ℕ) :
    (gridPoint H k a + gridPoint H k (a + 1)) / 2 = gridPoint H (k + 1) (2 * a + 1) := by
  have h1 : ((a + 1 : ℕ) : ℚ) = (a : ℚ) + 1 := by push_cast; ring
  have h2 : ((2 * a + 1 : ℕ) : ℚ) = 2 * (a : ℚ) + 1 := by push_cast; ring
  simp only [gridPoint, pow_succ, h1, h2]
  field_simp
  ring

/-- A grid point is unchanged by doubling its index and increasing the depth by one. -/
theorem gridPoint_even {H : ℚ} (k a : ℕ) :
    gridPoint H k a = gridPoint H (k + 1) (2 * a) := by
  have h1 : ((2 * a : ℕ) : ℚ) = 2 * (a : ℚ) := by push_cast; ring
  simp only [gridPoint, pow_succ, h1]
  all_goals ring

/-- The successor grid point is unchanged by replacing its index with `2 * a + 2` at the next
depth. -/
theorem gridPoint_even_succ {H : ℚ} (k a : ℕ) :
    gridPoint H k (a + 1) = gridPoint H (k + 1) (2 * a + 2) := by
  have h1 : ((a + 1 : ℕ) : ℚ) = (a : ℚ) + 1 := by push_cast; ring
  have h2 : ((2 * a + 2 : ℕ) : ℚ) = 2 * (a : ℚ) + 2 := by push_cast; ring
  simp only [gridPoint, pow_succ, h1, h2]
  all_goals ring

/-- Expresses a fidelity bracket as consecutive dyadic grid points whose lower index is maximal
among successful grid tests. -/
def GridBracket {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k a : ℕ) : Prop :=
  a < 2 ^ k ∧
    (fidelityBracket π σ p k).1 = gridPoint (computedWaterHigh π σ) k a ∧
    (fidelityBracket π σ p k).2 = gridPoint (computedWaterHigh π σ) k (a + 1) ∧
    fidelityReaches π σ p (gridPoint (computedWaterHigh π σ) k a) ∧
    ¬ fidelityReaches π σ p (gridPoint (computedWaterHigh π σ) k (a + 1)) ∧
    (∀ j : ℕ, j < 2 ^ k →
      fidelityReaches π σ p (gridPoint (computedWaterHigh π σ) k j) → j ≤ a)

/-- If the high endpoint fails the fidelity test, every refinement depth has a dyadic grid
bracket under the stated positivity assumptions. -/
theorem gridBracket_exists {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ)) :
    ∀ k : ℕ, ∃ a : ℕ, GridBracket π σ p k a := by
  intro k
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
      · rw [gridPoint_zero]
        rfl
      · rw [gridPoint_one]
        rfl
      · rw [gridPoint_zero]
        have hz := computedMass_dot_zero π σ hπ
        unfold fidelityReaches
        rw [hz.2, hz.1, mul_zero]
        exact sq_nonneg _
      · rw [gridPoint_one]
        exact hnot
      · intro j hj hQ
        omega
  | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      have hHpos : 0 ≤ computedWaterHigh π σ := by
        exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
          (computedWaterHigh_pos π σ hπ (fun j => (hσ j).le))
      have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le

      have haidx : a < 2 ^ k := ha.1
      have ha1 : a ≤ 2 ^ k - 1 := by omega
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring

      have hmid : ((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2
          = gridPoint (computedWaterHigh π σ) (k + 1) (2 * a + 1) := by
        rw [ha.2.1, ha.2.2.1, gridPoint_mid]

      have hsplit : fidelityBracket π σ p (k + 1) =
          (if computedDot π σ (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2) ^ 2
              ≥ p * computedMass π σ (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2)
          then (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2,
              (fidelityBracket π σ p k).2)
          else ((fidelityBracket π σ p k).1,
              ((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2)) := by
        rfl

      have hexcl : ∀ j : ℕ, 2 * a + 2 ≤ j →
          fidelityReaches π σ p (gridPoint (computedWaterHigh π σ) (k + 1) j) →
          fidelityReaches π σ p (gridPoint (computedWaterHigh π σ) k (a + 1)) := by
        intro j hj hQ
        have hlo : 0 ≤ (fidelityBracket π σ p k).2 := by
          rw [ha.2.2.1]
          exact gridPoint_nonneg hHpos
        have hle : (fidelityBracket π σ p k).2
            ≤ gridPoint (computedWaterHigh π σ) (k + 1) j := by
          rw [ha.2.2.1]
          have hmono : gridPoint (computedWaterHigh π σ) (k + 1) (2 * a + 2)
              ≤ gridPoint (computedWaterHigh π σ) (k + 1) j :=
            gridPoint_mono hHpos hj
          rw [← gridPoint_even_succ k a] at hmono
          exact hmono
        have hreach : fidelityReaches π σ p (fidelityBracket π σ p k).2 :=
          fidelityReaches_mono π σ p hπ hσ' hlo hle hQ
        rw [ha.2.2.1] at hreach
        exact hreach
      by_cases hmid_reaches :
          computedDot π σ (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2) ^ 2
            ≥ p * computedMass π σ (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2)
      · refine ⟨2 * a + 1, ?_⟩
        unfold GridBracket
        rw [hsplit, if_pos hmid_reaches]
        have hsucc : (2 * a + 1) + 1 = 2 * a + 2 := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpow]
          omega
        · exact hmid
        · exact ha.2.2.1.trans (gridPoint_even_succ k a)
        · rw [← hmid]
          exact hmid_reaches
        · rw [hsucc, ← gridPoint_even_succ k a]
          exact ha.2.2.2.2.1
        · intro j hj hQ
          by_cases hjle : j ≤ 2 * a + 1
          · omega
          · have hj2 : 2 * a + 2 ≤ j := by omega
            exact absurd (hexcl j hj2 hQ) ha.2.2.2.2.1
      · refine ⟨2 * a, ?_⟩
        unfold GridBracket
        rw [hsplit, if_neg hmid_reaches]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpow]
          omega
        · exact ha.2.1.trans (gridPoint_even k a)
        · exact hmid
        · rw [← gridPoint_even k a]
          exact ha.2.2.2.1
        · rw [← hmid]
          exact hmid_reaches
        · intro j hj hQ
          by_cases hjle : j ≤ 2 * a
          · omega
          · by_cases hjeq : j = 2 * a + 1
            · rw [hjeq, ← hmid] at hQ
              exact absurd hQ hmid_reaches
            · have hj2 : 2 * a + 2 ≤ j := by omega
              exact absurd (hexcl j hj2 hQ) ha.2.2.2.2.1

/-- At a fixed depth, increasing the target fidelity cannot increase the grid bracket index. -/
theorem gridBracket_index_anti {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hpp' : p ≤ p')
    {a a' : ℕ} (ha : GridBracket π σ p k a) (ha' : GridBracket π σ p' k a') :
    a' ≤ a := by
  have hQ' : fidelityReaches π σ p' (gridPoint (computedWaterHigh π σ) k a') :=
    ha'.2.2.2.1
  have hQ : fidelityReaches π σ p (gridPoint (computedWaterHigh π σ) k a') := by
    have hmass := computedMass_nonneg π σ (gridPoint (computedWaterHigh π σ) k a')
    have hmul : p * computedMass π σ (gridPoint (computedWaterHigh π σ) k a')
        ≤ p' * computedMass π σ (gridPoint (computedWaterHigh π σ) k a') :=
      mul_le_mul_of_nonneg_right hpp' hmass
    unfold fidelityReaches at hQ' ⊢
    linarith
  exact ha.2.2.2.2.2 a' ha'.1 hQ

/-- Failure of the fidelity test at the high endpoint persists when the target fidelity
increases. -/
theorem fidelityReaches_not_at_high_of_le {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ)
    (hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ)) (hpp' : p ≤ p') :
    ¬ fidelityReaches π σ p' (computedWaterHigh π σ) := by
  have hmass := computedMass_nonneg π σ (computedWaterHigh π σ)
  have hmul : p * computedMass π σ (computedWaterHigh π σ)
      ≤ p' * computedMass π σ (computedWaterHigh π σ) :=
    mul_le_mul_of_nonneg_right hpp' hmass
  intro hc
  unfold fidelityReaches at hc hnot
  linarith

/-- At a fixed refinement depth, `selectedLevel` is antitone in target fidelity when the smaller
target fails at the high endpoint. -/
theorem selectedLevel_anti {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ))
    (hpp' : p ≤ p') :
    selectedLevel π σ p' k ≤ selectedLevel π σ p k := by
  have hnot' := fidelityReaches_not_at_high_of_le π σ p p' hnot hpp'
  obtain ⟨a, ha⟩ := gridBracket_exists π σ p hπ hσ hnot k
  obtain ⟨a', ha'⟩ := gridBracket_exists π σ p' hπ hσ hnot' k
  have ha'le : a' ≤ a := gridBracket_index_anti π σ p p' k hpp' ha ha'
  have hHpos : 0 ≤ computedWaterHigh π σ := by
    exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (computedWaterHigh_pos π σ hπ (fun j => (hσ j).le))
  have hlevels : gridPoint (computedWaterHigh π σ) k (a' + 1)
      ≤ gridPoint (computedWaterHigh π σ) k (a + 1) :=
    gridPoint_mono hHpos (by omega)
  calc selectedLevel π σ p' k = (fidelityBracket π σ p' k).2 := rfl
    _ = gridPoint (computedWaterHigh π σ) k (a' + 1) := ha'.2.2.1
    _ ≤ gridPoint (computedWaterHigh π σ) k (a + 1) := hlevels
    _ = (fidelityBracket π σ p k).2 := ha.2.2.1.symm
    _ = selectedLevel π σ p k := rfl

/-- At a fixed refinement depth, the lower bracket endpoint is antitone in target fidelity under
the stated high-endpoint failure assumption. -/
theorem bracket_anti {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ))
    (hpp' : p ≤ p') :
    (fidelityBracket π σ p' k).1 ≤ (fidelityBracket π σ p k).1 := by
  have hnot' := fidelityReaches_not_at_high_of_le π σ p p' hnot hpp'
  obtain ⟨a, ha⟩ := gridBracket_exists π σ p hπ hσ hnot k
  obtain ⟨a', ha'⟩ := gridBracket_exists π σ p' hπ hσ hnot' k
  have ha'le : a' ≤ a := gridBracket_index_anti π σ p p' k hpp' ha ha'
  have hHpos : 0 ≤ computedWaterHigh π σ := by
    exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (computedWaterHigh_pos π σ hπ (fun j => (hσ j).le))
  have hlevels : gridPoint (computedWaterHigh π σ) k a'
      ≤ gridPoint (computedWaterHigh π σ) k a :=
    gridPoint_mono hHpos ha'le
  calc (fidelityBracket π σ p' k).1 = gridPoint (computedWaterHigh π σ) k a' := ha'.2.1
    _ ≤ gridPoint (computedWaterHigh π σ) k a := hlevels
    _ = (fidelityBracket π σ p k).1 := ha.2.1.symm

/-- For ordered target fidelities, the selected level for the larger target is at most the
earlier level plus one grid spacing. -/
theorem selectedLevel_stable {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ))
    (hpp' : p ≤ p') :
    selectedLevel π σ p' k ≤ selectedLevel π σ p k + computedWaterHigh π σ / 2 ^ k := by
  have hanti := selectedLevel_anti π σ p p' k hπ hσ hnot hpp'
  have hHpos : 0 ≤ computedWaterHigh π σ := by
    exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (computedWaterHigh_pos π σ hπ (fun j => (hσ j).le))
  have hpow : 0 ≤ (2 : ℚ) ^ k := by positivity
  have hwidth : 0 ≤ computedWaterHigh π σ / 2 ^ k := div_nonneg hHpos hpow
  linarith

/-- For positive source mass and a target above `computedPmin`, the selected level is antitone
as the target increases. -/
theorem selectedLevel_anti_in_range {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hmass : 0 < ∑ j, (π j) ^ 2)
    (hpmin : computedPmin π σ < p) (hpp' : p ≤ p') :
    selectedLevel π σ p' k ≤ selectedLevel π σ p k := by
  have hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ) := by
    have hmassH : computedMass π σ (computedWaterHigh π σ) = ∑ j, (π j) ^ 2 := by
      have hs := computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)
      simpa [computedMass] using! hs.2
    have hpos : 0 < computedMass π σ (computedWaterHigh π σ) := by
      rw [hmassH]
      exact hmass
    have hfidH : computedFidelity π σ (computedWaterHigh π σ) = computedPmin π σ :=
      computedFidelity_at_high π σ hπ hσ
    intro hc
    have hmul : p * computedMass π σ (computedWaterHigh π σ)
        ≤ computedDot π σ (computedWaterHigh π σ) ^ 2 := by
      unfold fidelityReaches at hc
      exact hc
    have hdiv : p ≤ computedDot π σ (computedWaterHigh π σ) ^ 2
        / computedMass π σ (computedWaterHigh π σ) :=
      (le_div_iff₀ hpos).2 hmul
    have hfid : computedFidelity π σ (computedWaterHigh π σ) ≥ p := by
      unfold computedFidelity
      rw [if_neg (ne_of_gt hpos)]
      exact hdiv
    have hmin : computedPmin π σ ≥ p := by rw [← hfidH]; exact hfid
    linarith
  exact selectedLevel_anti π σ p p' k hπ hσ hnot hpp'

/-- For a target above `computedPmin`, increasing the target bounds the new selected level by
the earlier level plus one grid spacing. -/
theorem selectedLevel_stable_in_range {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hmass : 0 < ∑ j, (π j) ^ 2)
    (hpmin : computedPmin π σ < p) (hpp' : p ≤ p') :
    selectedLevel π σ p' k ≤ selectedLevel π σ p k + computedWaterHigh π σ / 2 ^ k := by
  have hanti := selectedLevel_anti_in_range π σ p p' k hπ hσ hmass hpmin hpp'
  have hHpos : 0 ≤ computedWaterHigh π σ := by
    exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (computedWaterHigh_pos π σ hπ (fun j => (hσ j).le))
  have hpow : 0 ≤ (2 : ℚ) ^ k := by positivity
  have hwidth : 0 ≤ computedWaterHigh π σ / 2 ^ k := div_nonneg hHpos hpow
  linarith

/-- Successful runs with the same refinement depth have antitone selected levels as their target
fidelities increase. -/
theorem certifiedFidelityRun_level_stable {m : ℕ} (π σ : Fin m → ℚ) (p p' ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {r r' : CertifiedFidelityRun m}
    (hr : certifiedFidelityRun π σ p ε = some r)
    (hr' : certifiedFidelityRun π σ p' ε = some r')
    (hpp' : p ≤ p') (hk : r'.steps = r.steps) :
    r'.level ≤ r.level := by
  obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε hr
  have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
  have hmass : 0 < ∑ j, (π j) ^ 2 := by
    have h1 : (π r.witness) ^ 2 ≤ ∑ j, (π j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ r.witness)
    exact lt_of_lt_of_le (sq_pos_of_pos hmargin.1) h1
  have hanti := selectedLevel_anti_in_range π σ p p' r.steps hπ hσ hmass hmin hpp'
  have hsel : r.level = selectedLevel π σ p r.steps :=
    certifiedFidelityRun_level_is_selectedLevel π σ p ε hr
  have hsel' : r'.level = selectedLevel π σ p' r'.steps :=
    certifiedFidelityRun_level_is_selectedLevel π σ p' ε hr'
  rw [hsel, hsel', hk]
  exact hanti

/-- Collects target monotonicity, the grid-spacing bound, and bracket endpoint tests for targets
above `computedPmin`. -/
theorem frontier4 {m : ℕ} (π σ : Fin m → ℚ) (p p' : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hmass : 0 < ∑ j, (π j) ^ 2)
    (hpmin : computedPmin π σ < p) (hpp' : p ≤ p') :

    selectedLevel π σ p' k ≤ selectedLevel π σ p k ∧

    (fidelityBracket π σ p' k).1 ≤ (fidelityBracket π σ p k).1 ∧

    selectedLevel π σ p' k ≤ selectedLevel π σ p k + computedWaterHigh π σ / 2 ^ k ∧

    (fidelityBracket π σ p' k).2 ≤ computedWaterHigh π σ ∧
      fidelityReaches π σ p' (fidelityBracket π σ p' k).1 ∧
      ¬ fidelityReaches π σ p' (fidelityBracket π σ p' k).2 := by
  have hanti := selectedLevel_anti_in_range π σ p p' k hπ hσ hmass hpmin hpp'
  have hnot : ¬ fidelityReaches π σ p (computedWaterHigh π σ) := by
    have hmassH : computedMass π σ (computedWaterHigh π σ) = ∑ j, (π j) ^ 2 := by
      have hs := computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)
      simpa [computedMass] using! hs.2
    have hpos : 0 < computedMass π σ (computedWaterHigh π σ) := by
      rw [hmassH]
      exact hmass
    have hfidH : computedFidelity π σ (computedWaterHigh π σ) = computedPmin π σ :=
      computedFidelity_at_high π σ hπ hσ
    intro hc
    have hmul : p * computedMass π σ (computedWaterHigh π σ)
        ≤ computedDot π σ (computedWaterHigh π σ) ^ 2 := by
      unfold fidelityReaches at hc
      exact hc
    have hdiv : p ≤ computedDot π σ (computedWaterHigh π σ) ^ 2
        / computedMass π σ (computedWaterHigh π σ) :=
      (le_div_iff₀ hpos).2 hmul
    have hfid : computedFidelity π σ (computedWaterHigh π σ) ≥ p := by
      unfold computedFidelity
      rw [if_neg (ne_of_gt hpos)]
      exact hdiv
    have hmin : computedPmin π σ ≥ p := by rw [← hfidH]; exact hfid
    linarith
  have hbrace := bracket_anti π σ p p' k hπ hσ hnot hpp'
  have hstable := selectedLevel_stable_in_range π σ p p' k hπ hσ hmass hpmin hpp'

  have hpmin' : computedPmin π σ < p' := lt_of_lt_of_le hpmin hpp'
  have hrange : (∑ j, π j * σ j) ^ 2 < p' * (∑ j, (π j) ^ 2) :=
    pmin_lt_bracket π σ p' hmass hpmin'
  have hprops := certifiedFidelityBracket_props π σ p' hπ hσ hrange k
  (try dsimp only at hprops)
  refine ⟨hanti, hbrace, hstable, hprops.2.2.1, hprops.2.2.2.2.1, hprops.2.2.2.2.2⟩

/-- The sum of the squares of the rational source entries. -/
def sourceNormSq {m : ℕ} (π : Fin m → ℚ) : ℚ :=
  ∑ j, (π j) ^ 2

/-- The source squared norm is nonnegative. -/
theorem sourceNormSq_nonneg {m : ℕ} (π : Fin m → ℚ) : 0 ≤ sourceNormSq π := by
  unfold sourceNormSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A positive source entry implies a positive source squared norm. -/
theorem sourceNormSq_pos {m : ℕ} (π : Fin m → ℚ) (i : Fin m) (hpi : 0 < π i) :
    0 < sourceNormSq π := by
  unfold sourceNormSq
  have h1 : (π i) ^ 2 ≤ ∑ j, (π j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact lt_of_lt_of_le (sq_pos_of_pos hpi) h1

/-- A successful run yields positive source mass, an in-range target, the strict initial bracket
inequality, and selection of the upper bracket endpoint. -/
theorem certifiedFidelityRun_facts {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r) :
    0 < ∑ j, (π j) ^ 2 ∧
      computedPmin π σ < p ∧ p ≤ computedPmax π σ ∧
      (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2) ∧
      r.level = (fidelityBracket π σ p r.steps).2 := by
  obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε hr
  have hmass_pos : 0 < ∑ j, (π j) ^ 2 := by
    have h1 : (π r.witness) ^ 2 ≤ ∑ j, (π j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ r.witness)
    exact lt_of_lt_of_le (sq_pos_of_pos hmargin.1) h1
  have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
  have hpq : p ≤ computedPmax π σ := (targetRangeCheck_spec π σ p hR).2
  have hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2) :=
    pmin_lt_bracket π σ p hmass_pos hmin
  exact ⟨hmass_pos, hmin, hpq, hrange, hlev⟩

/-- The selected amplitude `selectedBeta` of a successful run is positive under the stated
source and target positivity assumptions. -/
theorem certifiedBeta_pos {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    0 < selectedBeta π σ r.level := by
  obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε hr
  have hmass : 0 < computedMass π σ r.level := by
    rw [hlev]
    exact certifiedFidelity_mass_pos π σ p r.steps r.witness hπ hσ hmargin.1
  unfold selectedBeta
  exact Real.sqrt_pos_of_pos (by exact_mod_cast hmass)

/-- The square of `selectedBeta` equals the computed filled mass. -/
theorem certifiedBeta_sq {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    (selectedBeta π σ γ) ^ 2 = computedMass π σ γ := by
  unfold selectedBeta
  exact Real.sq_sqrt (by exact_mod_cast computedMass_nonneg π σ γ)

/-- The selected amplitude of a successful run is at most the square root of the source squared
norm. -/
theorem certifiedBeta_le_norm {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    selectedBeta π σ r.level ≤ Real.sqrt (sourceNormSq π) := by
  obtain ⟨hmass_pos, hmin, hpq, hrange, hlev⟩ :=
    certifiedFidelityRun_facts π σ p ε hr
  have henergy := certifiedFidelity_energy π σ p r.steps hπ hσ hrange
  have hmass_le : computedMass π σ r.level ≤ sourceNormSq π := by
    rw [hlev]
    simpa [sourceNormSq] using! henergy.2.2.1
  have hmass_leR : ((computedMass π σ r.level : ℚ) : ℝ) ≤ ((sourceNormSq π : ℚ) : ℝ) := by
    exact_mod_cast hmass_le
  unfold selectedBeta
  exact Real.sqrt_le_sqrt hmass_leR

/-- Every rational number is bounded above by the square of a natural number. -/
theorem exists_nat_sq_ge {X : ℚ} : ∃ N : ℕ, (N : ℚ) ^ 2 ≥ X := by
  obtain ⟨N, hN⟩ := exists_nat_gt X
  refine ⟨N + 1, ?_⟩
  have h2 : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; ring
  have h1 : (1 : ℚ) ≤ ((N + 1 : ℕ) : ℚ) := by
    have h3 : (1 : ℕ) ≤ N + 1 := by omega
    exact_mod_cast h3
  calc
    ((N + 1 : ℕ) : ℚ) ^ 2 ≥ ((N + 1 : ℕ) : ℚ) := by rw [h2]; nlinarith
    _ ≥ X := by rw [h2]; linarith [hN]

/-- Every rational number is bounded above by the square of a natural number at least one. -/
theorem exists_nat_sq_ge_unit {X : ℚ} : ∃ N : ℕ, (N : ℚ) ^ 2 ≥ X ∧ 1 ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_sq_ge (X := X)
  refine ⟨N + 1, ?_, by omega⟩
  have h2 : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; ring
  have hsq : (N : ℚ) ^ 2 ≤ ((N + 1 : ℕ) : ℚ) ^ 2 := by
    rw [h2]
    have h0 : (0 : ℚ) ≤ (N : ℚ) := by positivity
    nlinarith
  linarith

/-- The least positive natural denominator whose square bounds the source squared norm. -/
def normalizationDenominator {m : ℕ} (π : Fin m → ℚ) : ℕ :=
  Nat.find (exists_nat_sq_ge_unit (X := sourceNormSq π))

/-- The normalization denominator is at least one and its square bounds the source squared norm. -/
theorem normalizationDenominator_spec {m : ℕ} (π : Fin m → ℚ) :
    (normalizationDenominator π : ℚ) ^ 2 ≥ sourceNormSq π ∧
      1 ≤ normalizationDenominator π := by
  have h := Nat.find_spec (exists_nat_sq_ge_unit (X := sourceNormSq π))
  simpa only [normalizationDenominator] using! h

/-- No natural number below the normalization denominator is both positive and large enough in
square to bound the source squared norm. -/
theorem normalizationDenominator_min {m : ℕ} (π : Fin m → ℚ) {N : ℕ}
    (hN : N < normalizationDenominator π) :
    ¬ ((N : ℚ) ^ 2 ≥ sourceNormSq π ∧ 1 ≤ N) := by
  have h := Nat.find_min (exists_nat_sq_ge_unit (X := sourceNormSq π)) hN
  simpa only [normalizationDenominator] using! h

/-- The reciprocal of the normalization denominator. -/
def normalizationFactor {m : ℕ} (π : Fin m → ℚ) : ℚ :=
  1 / (normalizationDenominator π : ℚ)

/-- The normalization factor is positive. -/
theorem normalizationFactor_pos {m : ℕ} (π : Fin m → ℚ) : 0 < normalizationFactor π := by
  unfold normalizationFactor
  have hN : (1 : ℚ) ≤ (normalizationDenominator π : ℚ) := by
    exact_mod_cast (normalizationDenominator_spec π).2
  exact div_pos (by norm_num) (by linarith)

/-- The normalization factor is at most one. -/
theorem normalizationFactor_le_one {m : ℕ} (π : Fin m → ℚ) :
    normalizationFactor π ≤ 1 := by
  unfold normalizationFactor
  have hN : (1 : ℚ) ≤ (normalizationDenominator π : ℚ) := by
    exact_mod_cast (normalizationDenominator_spec π).2
  exact (div_le_iff₀ (by linarith)).2 (by linarith [hN])

/-- Scaling the source squared norm by the square of the normalization factor gives a value at
most one. -/
theorem normalizationFactor_spec {m : ℕ} (π : Fin m → ℚ) :
    normalizationFactor π ^ 2 * sourceNormSq π ≤ 1 := by
  have hN2 : (normalizationDenominator π : ℚ) ^ 2 ≥ sourceNormSq π :=
    (normalizationDenominator_spec π).1
  have hN0 : (0 : ℚ) < (normalizationDenominator π : ℚ) := by
    have := (normalizationDenominator_spec π).2
    exact_mod_cast this
  have hdiv : sourceNormSq π / (normalizationDenominator π : ℚ) ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos hN0)]
    linarith [hN2]
  have heq : normalizationFactor π ^ 2 * sourceNormSq π
      = sourceNormSq π / (normalizationDenominator π : ℚ) ^ 2 := by
    unfold normalizationFactor
    rw [div_pow, one_pow]
    field_simp [ne_of_gt hN0]
  rw [heq]
  exact hdiv

/-- Normalizing the source and level scales the selected amplitude into `(0, 1]` and preserves
the fidelity of a successful run. -/
theorem certifiedBeta_normalized {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    selectedBeta (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) =
      normalizationFactor π * selectedBeta π σ r.level ∧
    0 < selectedBeta (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) ∧
    selectedBeta (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) ≤ 1 ∧
    computedFidelity (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) = computedFidelity π σ r.level := by
  have hβ := certifiedBeta_pos π σ p ε hr hπ hσ
  have hident : selectedBeta (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level)
      = normalizationFactor π * selectedBeta π σ r.level := by
    rw [selectedBeta_scaled π σ (normalizationFactor_pos π).le]
  have hfid : computedFidelity (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) = computedFidelity π σ r.level := by
    rw [computedFidelity_scaled π σ (normalizationFactor_pos π)]
  refine ⟨hident, ?_, ?_, hfid⟩
  · rw [hident]
    exact mul_pos (by exact_mod_cast (normalizationFactor_pos π)) hβ
  · rw [hident]
    have hβsqR : (selectedBeta π σ r.level) ^ 2 = ((computedMass π σ r.level : ℚ) : ℝ) := by
      exact certifiedBeta_sq π σ r.level
    have hmass_leR : ((computedMass π σ r.level : ℚ) : ℝ) ≤ ((sourceNormSq π : ℚ) : ℝ) := by
      obtain ⟨hmass_pos, hmin, hpq, hrange, hlev⟩ :=
        certifiedFidelityRun_facts π σ p ε hr
      have henergy := certifiedFidelity_energy π σ p r.steps hπ hσ hrange
      have hmass_le : computedMass π σ r.level ≤ sourceNormSq π := by
        rw [hlev]
        simpa [sourceNormSq] using! henergy.2.2.1
      exact_mod_cast hmass_le
    have hnormR : ((normalizationFactor π : ℚ) : ℝ) ^ 2 * ((sourceNormSq π : ℚ) : ℝ) ≤ 1 := by
      have := normalizationFactor_spec π
      exact_mod_cast this
    have hsq : ((normalizationFactor π * selectedBeta π σ r.level : ℝ)) ^ 2 ≤ 1 := by
      calc
        ((normalizationFactor π * selectedBeta π σ r.level : ℝ)) ^ 2
            = ((normalizationFactor π : ℚ) : ℝ) ^ 2 * (selectedBeta π σ r.level) ^ 2 := by ring
        _ ≤ ((normalizationFactor π : ℚ) : ℝ) ^ 2 * ((sourceNormSq π : ℚ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by linarith [hβsqR, hmass_leR]) (sq_nonneg _)
        _ ≤ 1 := hnormR
    have hnonneg : (0 : ℝ) ≤ (normalizationFactor π * selectedBeta π σ r.level : ℝ) := by
      have h1 : (0 : ℝ) ≤ (normalizationFactor π : ℚ) := by
        exact_mod_cast (normalizationFactor_pos π).le
      have h2 : (0 : ℝ) ≤ selectedBeta π σ r.level := by exact_mod_cast hβ.le
      exact mul_nonneg h1 h2
    have hsqrt : Real.sqrt ((normalizationFactor π * selectedBeta π σ r.level : ℝ) ^ 2)
        ≤ Real.sqrt 1 := by
      exact Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] at hsqrt
    have hone : Real.sqrt 1 = 1 := Real.sqrt_one
    rw [hone] at hsqrt
    linarith

/-- The exact resampling schedule as a triple of round count, angle, and scale. -/
noncomputable def scheduleTriple (β : ℝ) : ℕ × ℝ × ℝ :=
  (resamplingExactRounds β, resamplingExactAngle β, resamplingExactScale β)

/-- The scale, angle, exact rotation, round-count, and perturbation bounds required of a
resampling schedule triple. -/
def ScheduleClause (β : ℝ) (sch : ℕ × ℝ × ℝ) : Prop :=
  1 / 2 ≤ sch.2.2 ∧ sch.2.2 ≤ 1 ∧
    0 < sch.2.1 ∧ sch.2.1 ≤ Real.pi / 2 ∧
    Real.sin sch.2.1 = sch.2.2 * β ∧
    (2 * (sch.1 : ℝ) + 1) * sch.2.1 = Real.pi / 2 ∧
    ((2 * sch.1 + 1 : ℕ) : ℝ) ≤ Real.pi / (2 * β) + 2 ∧
    (β = 1 → sch.1 = 0 ∧ sch.2.2 = 1) ∧
    β / 2 ≤ Real.sin sch.2.1 ∧ Real.sin sch.2.1 ≤ β ∧
    (∀ β' δ : ℝ, 0 ≤ δ → |β - β'| ≤ δ →
      (β' - δ) / 2 ≤ Real.sin sch.2.1 ∧ Real.sin sch.2.1 ≤ β' + δ)

/-- The schedule bounds `ScheduleClause` specialized to `scheduleTriple β`. -/
def ScheduleWindows (β : ℝ) : Prop :=
  ScheduleClause β (scheduleTriple β)

/-- For `0 < β ≤ 1`, the exact resampling schedule satisfies `ScheduleWindows`. -/
theorem scheduleWindows (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) : ScheduleWindows β := by
  obtain ⟨hscaleLo, hscaleHi, hangPos, hangHi, hsin, htotal, hqueries, hend⟩ :=
    resamplingExactSchedule β hβ hβ1
  unfold ScheduleWindows ScheduleClause scheduleTriple
  refine ⟨hscaleLo, hscaleHi, hangPos, hangHi, hsin, htotal, hqueries, hend, ?_, ?_, ?_⟩
  · rw [hsin]
    nlinarith [hscaleLo]
  · rw [hsin]
    nlinarith [hscaleHi]
  · intro β' δ hδ happrox
    have habs := abs_le.mp happrox
    constructor
    · rw [hsin]
      nlinarith [hscaleLo]
    · rw [hsin]
      nlinarith [hscaleHi]

/-- For a selected amplitude in `(0, 1]`, the selected schedule equals `scheduleTriple` and
satisfies its schedule bounds. -/
theorem selectedSchedule_windows {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ)
    (hβ : 0 < selectedBeta π σ γ) (hβ1 : selectedBeta π σ γ ≤ 1) :
    ScheduleWindows (selectedBeta π σ γ) ∧
      selectedSchedule π σ γ = scheduleTriple (selectedBeta π σ γ) := by
  refine ⟨scheduleWindows _ hβ hβ1, ?_⟩
  rfl

/-- The normalized amplitude of a successful run satisfies `ScheduleWindows`, and its selected
schedule equals the corresponding `scheduleTriple`. -/
theorem certifiedSchedule_windows {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) :
    let β' := selectedBeta (scaledSource π (normalizationFactor π)) σ
      ((normalizationFactor π) * r.level)
    let sch := selectedSchedule (scaledSource π (normalizationFactor π)) σ
      ((normalizationFactor π) * r.level)
    0 < β' ∧ β' ≤ 1 ∧
      ScheduleWindows β' ∧
      sch = scheduleTriple β' ∧
      computedFidelity (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) = computedFidelity π σ r.level := by
  (try dsimp only)
  obtain ⟨hident, hpos, hle, hfid⟩ := certifiedBeta_normalized π σ p ε hr hπ hσ
  obtain ⟨hw, hsch⟩ := selectedSchedule_windows (scaledSource π (normalizationFactor π)) σ
    ((normalizationFactor π) * r.level) hpos hle
  exact ⟨hpos, hle, hw, hsch, hfid⟩

/-- Under the stated normalization and bracket hypotheses, the selected level inherits the exact
schedule bounds when its amplitude lies in `(0, 1]`. -/
theorem selectedLevel_inherits_frozen_schedule {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hπn : (∑ j, (π j : ℝ) ^ 2) = 1) (hσn : (∑ j, (σ j : ℝ) ^ 2) = 1)
    (hhigh : computedFidelity π σ (computedWaterHigh π σ) < p)
    (hmax : p ≤ computedPmax π σ)
    (hβ : 0 < selectedBeta π σ (selectedLevel π σ p k))
    (hβ1 : selectedBeta π σ (selectedLevel π σ p k) ≤ 1) :
    ScheduleWindows (selectedBeta π σ (selectedLevel π σ p k)) ∧
      selectedSchedule π σ (selectedLevel π σ p k) =
        scheduleTriple (selectedBeta π σ (selectedLevel π σ p k)) := by
  have hg := gext2 m π σ p hπ hσ hπn hσn hhigh hmax
  have hclause := hg.2.2.2 k
  (try dsimp only at hclause)
  have hsch : selectedSchedule π σ (selectedLevel π σ p k)
      = scheduleTriple (selectedBeta π σ (selectedLevel π σ p k)) := rfl
  rw [hsch] at hclause
  have hw := hclause hβ hβ1
  refine ⟨?_, ?_⟩
  · simpa only [ScheduleWindows, ScheduleClause, scheduleTriple, Prod.fst, Prod.snd] using! hw
  · exact hsch

/-- Under the stated normalization hypotheses, a successful run inherits the exact schedule
bounds at its refinement depth when the selected amplitude lies in `(0, 1]`. -/
theorem certifiedRun_inherits_frozen_schedule {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hπn : (∑ j, (π j : ℝ) ^ 2) = 1) (hσn : (∑ j, (σ j : ℝ) ^ 2) = 1)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hβ : 0 < selectedBeta π σ (selectedLevel π σ p r.steps))
    (hβ1 : selectedBeta π σ (selectedLevel π σ p r.steps) ≤ 1) :
    ScheduleWindows (selectedBeta π σ (selectedLevel π σ p r.steps)) ∧
      selectedSchedule π σ (selectedLevel π σ p r.steps) =
        scheduleTriple (selectedBeta π σ (selectedLevel π σ p r.steps)) := by
  obtain ⟨hR, hmargin, hX, hpow, hbr, hlev, hled⟩ := certifiedFidelityRun_spec π σ p ε hr
  have hmin : computedPmin π σ < p := (targetRangeCheck_spec π σ p hR).1
  have hfidH : computedFidelity π σ (computedWaterHigh π σ) = computedPmin π σ :=
    computedFidelity_at_high π σ hπ hσ
  have hhigh : computedFidelity π σ (computedWaterHigh π σ) < p := by
    rw [hfidH]
    exact hmin
  have hmax : p ≤ computedPmax π σ := (targetRangeCheck_spec π σ p hR).2
  exact selectedLevel_inherits_frozen_schedule π σ p r.steps hπ (fun j => (hσ j).le)
    hπn hσn hhigh hmax hβ hβ1

/-- Collects amplitude positivity, mass and norm bounds, fidelity-preserving normalization, and
exact schedule bounds for a successful run. -/
theorem frontier5 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r) :

    0 < selectedBeta π σ r.level ∧
      (selectedBeta π σ r.level) ^ 2 = computedMass π σ r.level ∧
      selectedBeta π σ r.level ≤ Real.sqrt (sourceNormSq π) ∧

    0 < normalizationFactor π ∧ normalizationFactor π ≤ 1 ∧
      normalizationFactor π ^ 2 * sourceNormSq π ≤ 1 ∧

      selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) =
        normalizationFactor π * selectedBeta π σ r.level ∧
      0 < selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) ∧
      selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) ≤ 1 ∧

      computedFidelity (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) = computedFidelity π σ r.level ∧

      ScheduleWindows (selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level)) ∧
      selectedSchedule (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) =
        scheduleTriple (selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level)) := by
  have hβpos := certifiedBeta_pos π σ p ε hr hπ hσ
  have hβsq : (selectedBeta π σ r.level) ^ 2 = computedMass π σ r.level :=
    certifiedBeta_sq π σ r.level
  have hβnorm := certifiedBeta_le_norm π σ p ε hr hπ hσ
  obtain ⟨hident, hpos, hle, hfid⟩ := certifiedBeta_normalized π σ p ε hr hπ hσ
  obtain ⟨hw, hsch⟩ := selectedSchedule_windows (scaledSource π (normalizationFactor π)) σ
    ((normalizationFactor π) * r.level) hpos hle
  exact ⟨hβpos, hβsq, hβnorm, normalizationFactor_pos π, normalizationFactor_le_one π,
    normalizationFactor_spec π, hident, hpos, hle, hfid, hw, hsch⟩

/-- For a real number in `[0, 1]`, its inverse sine is at least the number itself. -/
theorem arcsin_ge_self {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) : β ≤ Real.arcsin β := by
  have hmem : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [Real.pi_pos]
    · have h1 : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
      linarith
  have hmem2 : β ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  exact (Real.le_arcsin_iff_sin_le hmem hmem2).mpr (Real.sin_le hβ)

/-- For a real number `β` in `[0, 1]`, its inverse sine is at most `Real.pi / 2 * β`. -/
theorem arcsin_le_half_pi_mul {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Real.arcsin β ≤ Real.pi / 2 * β := by
  have hmem : β ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmem2 : Real.pi / 2 * β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have h0 : 0 ≤ Real.pi / 2 * β := by positivity
      have hhalf : 0 ≤ Real.pi / 2 := Real.pi_div_two_pos.le
      linarith
    · have h1 : Real.pi / 2 * β ≤ Real.pi / 2 := by
        have hhalf : Real.pi / 2 ≥ 0 := Real.pi_div_two_pos.le
        calc Real.pi / 2 * β ≤ Real.pi / 2 * 1 := by
              apply mul_le_mul_of_nonneg_left hβ1 hhalf
          _ = Real.pi / 2 := by ring
      linarith
  exact (Real.arcsin_le_iff_le_sin hmem hmem2).mpr (Real.le_sin_mul hβ hβ1)

/-- A positive rational lower amplitude bound whose product with `2 * t + 1` is at least two. -/
def RoundBudget (lo : ℚ) (t : ℕ) : Prop :=
  0 < lo ∧ lo * (2 * (t : ℚ) + 1) ≥ 2

/-- A positive rational upper amplitude bound whose product with `2 * t - 1` is strictly less
than one. -/
def RoundFloor (hi : ℚ) (t : ℕ) : Prop :=
  0 < hi ∧ hi * (2 * (t : ℚ) - 1) < 1

instance decidableRoundBudget (lo : ℚ) : DecidablePred (RoundBudget lo) := fun _ => by
  unfold RoundBudget
  infer_instance

instance decidableRoundFloor (hi : ℚ) : DecidablePred (RoundFloor hi) := fun _ => by
  unfold RoundFloor
  infer_instance

/-- A valid rational round budget below an amplitude in `(0, 1]` bounds its exact resampling
round count from above. -/
theorem resamplingExactRounds_le_of_budget {β : ℝ} {lo : ℚ} {t : ℕ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hbudget : RoundBudget lo t) (hlo : lo ≤ β) :
    resamplingExactRounds β ≤ t := by
  have hθpos : 0 < Real.arcsin β := Real.arcsin_pos.mpr hβ
  have hθge : β ≤ Real.arcsin β := arcsin_ge_self hβ.le hβ1
  have hloθ : lo ≤ Real.arcsin β := hlo.trans hθge
  have htpos : 0 ≤ (t : ℝ) + 1 / 2 := by
    have h0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hbudgetR : (lo : ℝ) * (2 * (t : ℝ) + 1) ≥ 2 := by
    have h := hbudget.2
    exact_mod_cast h
  have hlohalf : (lo : ℝ) * ((t : ℝ) + 1 / 2) ≥ 1 := by
    have h1 : (lo : ℝ) * (2 * (t : ℝ) + 1) = 2 * ((lo : ℝ) * ((t : ℝ) + 1 / 2)) := by ring
    linarith
  have hfour : 4 ≤ 4 * Real.arcsin β * ((t : ℝ) + 1 / 2) := by
    have h1 : 4 ≤ 4 * (lo : ℝ) * ((t : ℝ) + 1 / 2) := by linarith
    have h2 : 4 * (lo : ℝ) * ((t : ℝ) + 1 / 2) ≤ 4 * Real.arcsin β * ((t : ℝ) + 1 / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hloθ htpos]
    linarith
  have hpi : Real.pi ≤ 4 * Real.arcsin β * ((t : ℝ) + 1 / 2) :=
    le_trans Real.pi_le_four hfour
  have hden : 0 < 4 * Real.arcsin β := mul_pos (by norm_num) hθpos
  have hq : Real.pi / (4 * Real.arcsin β) - 1 / 2 ≤ (t : ℝ) := by
    have h2 : Real.pi / (4 * Real.arcsin β) ≤ (t : ℝ) + 1 / 2 := by
      rw [div_le_iff₀ hden]
      linarith
    linarith
  unfold resamplingExactRounds
  exact Nat.ceil_le.mpr hq

/-- A valid rational round floor above an amplitude in `(0, 1]` bounds its exact resampling
round count from below when `t ≥ 1`. -/
theorem resamplingExactRounds_ge_of_floor {β : ℝ} {hi : ℚ} {t : ℕ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t) (hfloor : RoundFloor hi t)
    (hhi : β ≤ hi) :
    t ≤ resamplingExactRounds β := by
  have hθle : Real.arcsin β ≤ Real.pi / 2 * β := arcsin_le_half_pi_mul hβ.le hβ1
  have hkey : 2 * Real.arcsin β ≤ Real.pi * β := by
    nlinarith [hθle]
  have hden : 0 < 4 * Real.arcsin β := by
    have : 0 < Real.arcsin β := Real.arcsin_pos.mpr hβ
    nlinarith
  have hq1 : 1 / (2 * β) ≤ Real.pi / (4 * Real.arcsin β) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hβ) hden]
    nlinarith [hkey]
  have hhipos : (0 : ℝ) < (hi : ℝ) := by exact_mod_cast hfloor.1
  have hq2 : 1 / (2 * hi) ≤ 1 / (2 * β) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hhipos) (mul_pos (by norm_num) hβ)]
    nlinarith [hhi]
  have hfloorR : (hi : ℝ) * (2 * (t : ℝ) - 1) < 1 := by
    have h := hfloor.2
    exact_mod_cast h
  have hq : Real.pi / (4 * Real.arcsin β) - 1 / 2 > (t : ℝ) - 1 := by
    have h1 : (2 * (t : ℝ) - 1) / 2 < (1 : ℝ) / (2 * hi) := by
      rw [lt_div_iff₀ (mul_pos (by norm_num) hhipos)]
      have h2 : (2 * (t : ℝ) - 1) / 2 * (2 * (hi : ℝ))
          = (2 * (t : ℝ) - 1) * (hi : ℝ) := by ring
      rw [h2]
      linarith [hfloorR]
    linarith
  have hnot : ¬ resamplingExactRounds β ≤ t - 1 := by
    intro h
    have h' : Real.pi / (4 * Real.arcsin β) - 1 / 2 ≤ (t - 1 : ℕ) := by
      unfold resamplingExactRounds at h
      exact Nat.ceil_le.mp h
    have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub ht]
      ring
    rw [hcast] at h'
    linarith
  omega

/-- A nonnegative rational whose square is at most the computed mass bounds `selectedBeta` from
below. -/
theorem selectedBeta_lower {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} (lo : ℚ)
    (hlo : 0 ≤ lo) (hlo2 : lo ^ 2 ≤ computedMass π σ γ) :
    lo ≤ selectedBeta π σ γ := by
  have hR : ((lo ^ 2 : ℚ) : ℝ) ≤ ((computedMass π σ γ : ℚ) : ℝ) := by
    exact_mod_cast hlo2
  have h1 : Real.sqrt ((lo ^ 2 : ℚ) : ℝ) ≤ Real.sqrt ((computedMass π σ γ : ℚ) : ℝ) :=
    Real.sqrt_le_sqrt hR
  have hsq : ((lo ^ 2 : ℚ) : ℝ) = (lo : ℝ) ^ 2 := by push_cast; ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by exact_mod_cast hlo)] at h1
  exact h1

/-- A nonnegative rational whose square bounds the computed mass bounds `selectedBeta` from
above. -/
theorem selectedBeta_upper {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} (hi : ℚ)
    (hhi : 0 ≤ hi) (hhi2 : computedMass π σ γ ≤ hi ^ 2) :
    selectedBeta π σ γ ≤ hi := by
  have hR : ((computedMass π σ γ : ℚ) : ℝ) ≤ ((hi ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast hhi2
  have h1 : Real.sqrt ((computedMass π σ γ : ℚ) : ℝ) ≤ Real.sqrt ((hi ^ 2 : ℚ) : ℝ) :=
    Real.sqrt_le_sqrt hR
  have hsq : ((hi ^ 2 : ℚ) : ℝ) = (hi : ℝ) ^ 2 := by push_cast; ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by exact_mod_cast hhi)] at h1
  exact h1

/-- Nonnegative rational square bounds on the computed mass give a rational interval containing
`selectedBeta`. -/
theorem selectedBeta_interval {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} (lo hi : ℚ)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hlo2 : lo ^ 2 ≤ computedMass π σ γ)
    (hhi2 : computedMass π σ γ ≤ hi ^ 2) :
    lo ≤ selectedBeta π σ γ ∧ selectedBeta π σ γ ≤ hi :=
  ⟨selectedBeta_lower π σ lo hlo hlo2, selectedBeta_upper π σ hi hhi hhi2⟩

/-- Every positive rational lower amplitude bound has a natural round budget. -/
theorem exists_roundBudget {lo : ℚ} (hlo : 0 < lo) : ∃ t : ℕ, RoundBudget lo t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / lo)
  refine ⟨N, hlo, ?_⟩
  have h1 : lo * (N : ℚ) > 2 := by
    have h2 : lo * (2 / lo) = 2 := by field_simp
    have h3 : lo * (N : ℚ) > lo * (2 / lo) := mul_lt_mul_of_pos_left hN hlo
    linarith
  have h4 : lo * (2 * (N : ℚ) + 1) = 2 * (lo * (N : ℚ)) + lo := by ring
  linarith

/-- The least natural round count satisfying `RoundBudget` for a positive rational lower
amplitude bound. -/
noncomputable def roundBudgetSearch (lo : ℚ) (hlo : 0 < lo) : ℕ :=
  Nat.find (p := fun t => RoundBudget lo t) (exists_roundBudget hlo)

/-- The round count returned by `roundBudgetSearch` satisfies `RoundBudget`. -/
theorem roundBudgetSearch_spec {lo : ℚ} (hlo : 0 < lo) :
    RoundBudget lo (roundBudgetSearch lo hlo) := by
  unfold roundBudgetSearch
  exact Nat.find_spec (p := fun t => RoundBudget lo t) (exists_roundBudget hlo)

/-- The round budget search result is at most every count satisfying the same budget condition. -/
theorem roundBudgetSearch_le {lo : ℚ} (hlo : 0 < lo) {t : ℕ} (ht : RoundBudget lo t) :
    roundBudgetSearch lo hlo ≤ t := by
  unfold roundBudgetSearch
  exact Nat.find_le (p := fun t => RoundBudget lo t) (h := exists_roundBudget hlo) ht

/-- For every positive rational upper amplitude bound, some natural count fails `RoundFloor`. -/
theorem exists_not_roundFloor {hi : ℚ} (hhi : 0 < hi) : ∃ t : ℕ, ¬ RoundFloor hi t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / hi)
  refine ⟨N, ?_⟩
  intro hcontra
  rcases hcontra with ⟨_, hbad⟩
  have h1 : hi * (N : ℚ) > 1 := by
    have h2 : hi * (1 / hi) = 1 := by field_simp
    have h3 : hi * (N : ℚ) > hi * (1 / hi) := mul_lt_mul_of_pos_left hN hhi
    linarith
  have hN1 : 1 ≤ N := by
    have hz : N ≠ 0 := by
      intro hz
      rw [hz] at hN
      have : (0 : ℚ) < 1 / hi := by positivity
      linarith
    omega
  have hN1Q : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN1
  have h4 : hi * (2 * (N : ℚ) - 1) ≥ hi * (N : ℚ) := by nlinarith [hhi, hN1Q]
  linarith

/-- The least natural count failing `RoundFloor` for a positive rational upper amplitude bound. -/
noncomputable def roundFloorSearch (hi : ℚ) (hhi : 0 < hi) : ℕ :=
  Nat.find (p := fun t => ¬ RoundFloor hi t) (exists_not_roundFloor hhi)

/-- The count returned by `roundFloorSearch` fails `RoundFloor`. -/
theorem roundFloorSearch_spec {hi : ℚ} (hhi : 0 < hi) :
    ¬ RoundFloor hi (roundFloorSearch hi hhi) := by
  unfold roundFloorSearch
  exact Nat.find_spec (p := fun t => ¬ RoundFloor hi t) (exists_not_roundFloor hhi)

/-- The first count failing the round floor condition is at least one. -/
theorem roundFloorSearch_pos {hi : ℚ} (hhi : 0 < hi) : 1 ≤ roundFloorSearch hi hhi := by
  have h0 : RoundFloor hi 0 := by
    refine ⟨hhi, ?_⟩
    norm_num
    linarith [hhi]
  have hspec := roundFloorSearch_spec hhi
  by_contra hcon
  have hz : roundFloorSearch hi hhi = 0 := by omega
  rw [hz] at hspec
  exact hspec h0

/-- The predecessor of the first count failing `RoundFloor` satisfies `RoundFloor`. -/
theorem roundFloorSearch_prev {hi : ℚ} (hhi : 0 < hi) :
    RoundFloor hi (roundFloorSearch hi hhi - 1) := by
  by_contra hcon
  have hbad : ¬ RoundFloor hi (roundFloorSearch hi hhi - 1) := hcon
  have h1 := Nat.find_le (p := fun t => ¬ RoundFloor hi t)
    (h := exists_not_roundFloor hhi) hbad
  have hdef : Nat.find (p := fun t => ¬ RoundFloor hi t) (exists_not_roundFloor hhi)
      = roundFloorSearch hi hhi := rfl
  rw [hdef] at h1
  have h2 := roundFloorSearch_pos hhi
  omega

/-- Rational bounds `lo ≤ β ≤ hi` and `ScheduleWindows β` bound the schedule angle's sine
between `lo / 2` and `hi`. -/
theorem scheduleWindow_rational {β : ℝ} {lo hi : ℚ}
    (hlo : lo ≤ β) (hhi : β ≤ hi) (hw : ScheduleWindows β) :
    (lo : ℝ) / 2 ≤ Real.sin (resamplingExactAngle β) ∧
      Real.sin (resamplingExactAngle β) ≤ (hi : ℝ) := by
  unfold ScheduleWindows ScheduleClause scheduleTriple at hw
  simp only at hw
  have h9 : β / 2 ≤ Real.sin (resamplingExactAngle β) := hw.2.2.2.2.2.2.2.2.1
  have h10 : Real.sin (resamplingExactAngle β) ≤ β := hw.2.2.2.2.2.2.2.2.2.1
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by norm_num)).trans h9
  · exact h10.trans (by exact_mod_cast hhi)

/-- Positive rational bounds on `β` give ratio bounds on the exact schedule scale, together with
its bounds between one half and one. -/
theorem scheduleScale_rational {β : ℝ} {lo hi : ℚ}
    (hβ : 0 < β) (hlo : 0 < lo) (hhi : 0 < hi)
    (hlo' : lo ≤ β) (hhi' : β ≤ hi) (hw : ScheduleWindows β) :
    lo / (2 * hi) ≤ resamplingExactScale β ∧
      resamplingExactScale β ≤ hi / lo ∧
      (1 : ℝ) / 2 ≤ resamplingExactScale β ∧ resamplingExactScale β ≤ 1 := by
  unfold ScheduleWindows ScheduleClause scheduleTriple at hw
  simp only at hw
  have h9 : β / 2 ≤ Real.sin (resamplingExactAngle β) := hw.2.2.2.2.2.2.2.2.1
  have h10 : Real.sin (resamplingExactAngle β) ≤ β := hw.2.2.2.2.2.2.2.2.2.1
  have hs1 : (1 : ℝ) / 2 ≤ resamplingExactScale β := by
    have := hw.1
    simpa only [resamplingExactScale] using! this
  have hs2 : resamplingExactScale β ≤ 1 := by
    have := hw.2.1
    simpa only [resamplingExactScale] using! this
  have hloR : (lo : ℝ) > 0 := by exact_mod_cast hlo
  have hhiR : (hi : ℝ) > 0 := by exact_mod_cast hhi
  have hβR : (0 : ℝ) < β := hβ
  refine ⟨?_, ?_, hs1, hs2⟩
  · have hA : (lo : ℝ) / 2 ≤ Real.sin (resamplingExactAngle β) := by
      exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo') (by norm_num)).trans h9
    have hB : (lo : ℝ) / 2 / β ≤ Real.sin (resamplingExactAngle β) / β :=
      div_le_div_of_nonneg_right hA hβR.le
    have hC : (lo : ℝ) / 2 / (hi : ℝ) ≤ (lo : ℝ) / 2 / β :=
      div_le_div_of_nonneg_left
        (div_nonneg (le_of_lt hloR) (by norm_num : (0 : ℝ) ≤ 2)) hβR hhi'
    have hD : (lo : ℝ) / 2 / (hi : ℝ) = lo / (2 * hi) := by ring
    rw [← hD]
    exact hC.trans hB
  · have hA : Real.sin (resamplingExactAngle β) ≤ (hi : ℝ) := by
      exact h10.trans (by exact_mod_cast hhi')
    have hB : Real.sin (resamplingExactAngle β) / β ≤ (hi : ℝ) / β :=
      div_le_div_of_nonneg_right hA hβR.le
    have hC : (hi : ℝ) / β ≤ (hi : ℝ) / (lo : ℝ) :=
      div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (hi : ℝ) from le_of_lt hhiR)
        (by exact_mod_cast hlo) (by exact_mod_cast hlo')
    have hD : (hi : ℝ) / (lo : ℝ) = hi / lo := by ring
    rw [← hD]
    exact hB.trans hC

/-- An amplitude in `[1 / 2, 1)` has exactly one resampling round. -/
theorem resamplingExactRounds_eq_one_of_range {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hhalf : (1 : ℝ) / 2 ≤ β) :
    resamplingExactRounds β = 1 := by
  have hθpos : 0 < Real.arcsin β := Real.arcsin_pos.mpr hβ
  have hθlt : Real.arcsin β < Real.pi / 2 := by
    rw [← Real.arcsin_one]
    exact Real.arcsin_lt_arcsin (by linarith [hβ]) hβ1 (by norm_num)
  have hθhalf : Real.pi / 6 ≤ Real.arcsin β := by
    have h1 : Real.pi / 6 ≤ Real.arcsin (1 / 2 : ℝ) := by
      have hmem : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      have hmem2 : (1 / 2 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have h2 := (Real.le_arcsin_iff_sin_le hmem hmem2).mpr (by
        norm_num [Real.sin_pi_div_six])
      simpa using! h2
    exact h1.trans (Real.arcsin_le_arcsin hhalf)
  have hden : 0 < 4 * Real.arcsin β := mul_pos (by norm_num) hθpos
  have hqlo : 0 < Real.pi / (4 * Real.arcsin β) - 1 / 2 := by
    have h1 : (1 : ℝ) / 2 < Real.pi / (4 * Real.arcsin β) := by
      rw [lt_div_iff₀ hden]
      have h2 : 2 * Real.arcsin β < Real.pi := by linarith [hθlt]
      linarith
    linarith
  have hqhi : Real.pi / (4 * Real.arcsin β) - 1 / 2 ≤ 1 := by
    have h1 : Real.pi ≤ 6 * Real.arcsin β := by nlinarith [hθhalf]
    have h2 : Real.pi / (4 * Real.arcsin β) ≤ 3 / 2 := by
      rw [div_le_iff₀ hden]
      linarith
    linarith
  unfold resamplingExactRounds
  have h1 : Nat.ceil (Real.pi / (4 * Real.arcsin β) - 1 / 2) ≤ 1 := by
    exact Nat.ceil_le.mpr (by linarith [hqhi])
  have h2 : 1 ≤ Nat.ceil (Real.pi / (4 * Real.arcsin β) - 1 / 2) := by
    by_contra hcon
    have h3 : Nat.ceil (Real.pi / (4 * Real.arcsin β) - 1 / 2) ≤ 0 := by omega
    have h4 := Nat.ceil_le.mp h3
    linarith
  omega

/-- Positive rational square bounds on the normalized mass of a successful run give computable
round-count bounds and bounds on the schedule angle's sine. -/
theorem certifiedRoundBudget {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (lo hi : ℚ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hmass : lo ^ 2 ≤ computedMass (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level))
    (hmass2 : computedMass (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) ≤ hi ^ 2) :
    roundFloorSearch hi hhi - 1 ≤
        resamplingExactRounds (selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level)) ∧
      resamplingExactRounds (selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level)) ≤ roundBudgetSearch lo hlo ∧
      (lo : ℝ) / 2 ≤ Real.sin (resamplingExactAngle
          (selectedBeta (scaledSource π (normalizationFactor π)) σ
            ((normalizationFactor π) * r.level))) ∧
      Real.sin (resamplingExactAngle
          (selectedBeta (scaledSource π (normalizationFactor π)) σ
            ((normalizationFactor π) * r.level))) ≤ (hi : ℝ) := by
  obtain ⟨hident, hpos, hle, hfid⟩ := certifiedBeta_normalized π σ p ε hr hπ hσ
  obtain ⟨hlo', hhi'⟩ := selectedBeta_interval (scaledSource π (normalizationFactor π)) σ
    lo hi (le_of_lt hlo) (le_of_lt hhi) hmass hmass2
  have hw := selectedSchedule_windows (scaledSource π (normalizationFactor π)) σ
    ((normalizationFactor π) * r.level) hpos hle
  have hfloorres : roundFloorSearch hi hhi - 1 ≤
      resamplingExactRounds (selectedBeta (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level)) := by
    by_cases hz : roundFloorSearch hi hhi - 1 = 0
    · omega
    · have hpos' : 1 ≤ roundFloorSearch hi hhi - 1 := by omega
      exact resamplingExactRounds_ge_of_floor hpos hle hpos'
        (roundFloorSearch_prev hhi) hhi'
  have hbudgetres : resamplingExactRounds (selectedBeta (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level)) ≤ roundBudgetSearch lo hlo :=
    resamplingExactRounds_le_of_budget hpos hle (roundBudgetSearch_spec hlo) hlo'
  obtain ⟨hwin1, hwin2⟩ := scheduleWindow_rational hlo' hhi' hw.1
  exact ⟨hfloorres, hbudgetres, hwin1, hwin2⟩

/-- Collects rational amplitude bounds, round-count bounds, and bounds on the schedule angle's
sine from a successful run's normalized mass bounds. -/
theorem frontier6 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    {r : CertifiedFidelityRun m} (hr : certifiedFidelityRun π σ p ε = some r)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (lo hi : ℚ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hmass : lo ^ 2 ≤ computedMass (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level))
    (hmass2 : computedMass (scaledSource π (normalizationFactor π)) σ
        ((normalizationFactor π) * r.level) ≤ hi ^ 2) :
    lo ≤ selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) ∧
      selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level) ≤ hi ∧
      roundFloorSearch hi hhi - 1 ≤
        resamplingExactRounds (selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level)) ∧
      resamplingExactRounds (selectedBeta (scaledSource π (normalizationFactor π)) σ
          ((normalizationFactor π) * r.level)) ≤ roundBudgetSearch lo hlo ∧
      (lo : ℝ) / 2 ≤ Real.sin (resamplingExactAngle
          (selectedBeta (scaledSource π (normalizationFactor π)) σ
            ((normalizationFactor π) * r.level))) ∧
      Real.sin (resamplingExactAngle
          (selectedBeta (scaledSource π (normalizationFactor π)) σ
            ((normalizationFactor π) * r.level))) ≤ (hi : ℝ) := by
  obtain ⟨hlo', hhi'⟩ := selectedBeta_interval (scaledSource π (normalizationFactor π)) σ
    lo hi (le_of_lt hlo) (le_of_lt hhi) hmass hmass2
  obtain ⟨hf, hb, hw1, hw2⟩ :=
    certifiedRoundBudget π σ p ε hr hπ hσ lo hi hlo hhi hmass hmass2
  exact ⟨hlo', hhi', hf, hb, hw1, hw2⟩

/-- Casting a rational difference to the reals commutes with subtraction. -/
theorem rat_sub_cast (a b : ℚ) : ((a - b : ℚ) : ℝ) = (a : ℝ) - (b : ℝ) := Rat.cast_sub a b

/-- A rational absolute-value bound remains valid after casting to the reals. -/
theorem abs_rat_le {a b : ℚ} (h : |a| ≤ b) : |(a : ℝ)| ≤ (b : ℝ) := by
  by_cases hpos : 0 ≤ a
  · have hpos' : 0 ≤ (a : ℝ) := by exact_mod_cast hpos
    rw [abs_of_nonneg hpos] at h
    rw [abs_of_nonneg hpos']
    exact_mod_cast h
  · have hneg : a ≤ 0 := le_of_not_ge hpos
    have hneg' : (a : ℝ) ≤ 0 := by exact_mod_cast hneg
    rw [abs_of_nonpos hneg] at h
    rw [abs_of_nonpos hneg']
    exact_mod_cast h

/-- For nonnegative real masses, the absolute difference of their square roots times the sum of
their square roots equals their absolute difference. -/
theorem sqrt_sub_mul_sum {M1 M2 : ℝ} (h1 : 0 ≤ M1) (h2 : 0 ≤ M2) :
    |Real.sqrt M2 - Real.sqrt M1| * (Real.sqrt M2 + Real.sqrt M1) = |M2 - M1| := by
  have hsq1 : Real.sqrt M1 ^ 2 = M1 := Real.sq_sqrt h1
  have hsq2 : Real.sqrt M2 ^ 2 = M2 := Real.sq_sqrt h2
  have hsum0 : 0 ≤ Real.sqrt M2 + Real.sqrt M1 := by positivity
  calc |Real.sqrt M2 - Real.sqrt M1| * (Real.sqrt M2 + Real.sqrt M1)
      = |(Real.sqrt M2 - Real.sqrt M1) * (Real.sqrt M2 + Real.sqrt M1)| := by
        rw [abs_mul, abs_of_nonneg hsum0]
    _ = |Real.sqrt M2 ^ 2 - Real.sqrt M1 ^ 2| := by
      congr 1
      ring
    _ = |M2 - M1| := by rw [hsq2, hsq1]

/-- Two masses above a positive lower bound have square-root error at most their mass error
divided by twice the square root of that bound. -/
theorem precisionSqrt_error {mLo dm mass massHat : ℚ} (hmLo : 0 < mLo) (hdm : 0 ≤ dm)
    (hmass : mLo ≤ mass) (hhat : mLo ≤ massHat)
    (herr : |massHat - mass| ≤ dm) :
    |Real.sqrt (massHat : ℝ) - Real.sqrt (mass : ℝ)| ≤
      (dm : ℝ) / (2 * Real.sqrt (mLo : ℝ)) := by
  have hmass0 : 0 ≤ (mass : ℝ) := by exact_mod_cast (le_trans (le_of_lt hmLo) hmass)
  have hhat0 : 0 ≤ (massHat : ℝ) := by exact_mod_cast (le_trans (le_of_lt hmLo) hhat)
  have hsq1 : Real.sqrt (massHat : ℝ) ^ 2 = (massHat : ℝ) := Real.sq_sqrt hhat0
  have hsq2 : Real.sqrt (mass : ℝ) ^ 2 = (mass : ℝ) := Real.sq_sqrt hmass0
  have hx : Real.sqrt (mLo : ℝ) ≤ Real.sqrt (massHat : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hhat)
  have hy : Real.sqrt (mLo : ℝ) ≤ Real.sqrt (mass : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmass)
  have hsum0 : 0 ≤ Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ) := by positivity
  have hsum : 2 * Real.sqrt (mLo : ℝ) ≤ Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ) := by
    linarith
  have hid : |Real.sqrt (massHat : ℝ) - Real.sqrt (mass : ℝ)| *
      (Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ)) = |(massHat : ℝ) - (mass : ℝ)| := by
    calc |Real.sqrt (massHat : ℝ) - Real.sqrt (mass : ℝ)| *
          (Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ))
        = |(Real.sqrt (massHat : ℝ) - Real.sqrt (mass : ℝ)) *
            (Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ))| := by
          rw [abs_mul, abs_of_nonneg hsum0]
        _ = |Real.sqrt (massHat : ℝ) ^ 2 - Real.sqrt (mass : ℝ) ^ 2| := by
          congr 1
          ring
        _ = |(massHat : ℝ) - (mass : ℝ)| := by rw [hsq1, hsq2]
  have herrR : |(massHat : ℝ) - (mass : ℝ)| ≤ (dm : ℝ) := by
    have h2 := abs_rat_le herr
    push_cast at h2 ⊢
    exact h2
  have hprod : |Real.sqrt (massHat : ℝ) - Real.sqrt (mass : ℝ)| *
      (Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ)) ≤ (dm : ℝ) := by
    rw [hid]
    exact herrR
  have hsumpos : 0 < Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ) := by
    have hhatpos : 0 < (massHat : ℝ) := by
      have h1 : (0 : ℝ) < (mLo : ℝ) := by exact_mod_cast hmLo
      have h2 : (mLo : ℝ) ≤ (massHat : ℝ) := by exact_mod_cast hhat
      exact lt_of_lt_of_le h1 h2
    have h1 : 0 < Real.sqrt (massHat : ℝ) := Real.sqrt_pos.2 hhatpos
    have h2 : 0 ≤ Real.sqrt (mass : ℝ) := Real.sqrt_nonneg _
    linarith
  have h1 : |Real.sqrt (massHat : ℝ) - Real.sqrt (mass : ℝ)| ≤
      (dm : ℝ) / (Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ)) := by
    rw [le_div_iff₀ hsumpos]
    linarith [hprod]
  have hdmR : (0 : ℝ) ≤ (dm : ℝ) := by exact_mod_cast hdm
  have h2 : (dm : ℝ) / (Real.sqrt (massHat : ℝ) + Real.sqrt (mass : ℝ)) ≤
      (dm : ℝ) / (2 * Real.sqrt (mLo : ℝ)) :=
    div_le_div_of_nonneg_left hdmR (by positivity) hsum
  exact h1.trans h2

/-- Under the strict initial bracket inequality, the endpoint mass difference is at most twice
the source-target dot product times the dyadic bracket width. -/
theorem certifiedMass_width {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2)) :
    computedMass π σ (fidelityBracket π σ p k).2 -
        computedMass π σ (fidelityBracket π σ p k).1
      ≤ 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  obtain ⟨hlo, hle, hhi, hwidth, hreach, hnotreach⟩ := hbr
  have hinc := computedWaterEnergy_increment π σ (fun j => ⟨hπ j, (hσ j).le⟩) hlo hle
  calc
    computedMass π σ (fidelityBracket π σ p k).2 -
        computedMass π σ (fidelityBracket π σ p k).1
        = computedWaterEnergy π σ (fidelityBracket π σ p k).2 -
          computedWaterEnergy π σ (fidelityBracket π σ p k).1 := rfl
    _ ≤ 2 * (∑ j, π j * σ j) *
          ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1) := hinc
    _ = 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
      rw [hwidth]

/-- A margin witness and the stated refinement-depth bound control the difference of the
endpoint amplitudes by `ε * π i / p`. -/
theorem certifiedBeta_precision {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k) :
    |selectedBeta π σ (fidelityBracket π σ p k).2 -
        selectedBeta π σ (fidelityBracket π σ p k).1| ≤ ((ε * π i / p : ℚ) : ℝ) := by
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  obtain ⟨hlo, hle, hhi, hwidth, hreach, hnotreach⟩ := hbr

  have hgc : 0 < π i / σ i := div_pos hpi (hσ i)
  have hb0 : 0 ≤ (fidelityBracket π σ p k).2 := hlo.trans hle
  have hgc_lt : π i / σ i < (fidelityBracket π σ p k).2 := by
    by_contra hcon
    have hle' : (fidelityBracket π σ p k).2 ≤ π i / σ i := le_of_not_gt hcon
    exact hnotreach (fidelityReaches_mono π σ p hπ hσ' hb0 hle' hmargin)

  have hfill : waterFill π σ (π i / σ i) i = π i := by
    rw [waterFill]
    have hne : σ i ≠ 0 := (hσ i).ne'
    have heq : (π i / σ i) * σ i = π i := by field_simp
    rw [heq, min_eq_left (le_refl _)]
  have hmass_gc : (π i) ^ 2 ≤ computedMass π σ (π i / σ i) := by
    unfold computedMass
    have hle : (waterFill π σ (π i / σ i) i) ^ 2 ≤
        ∑ j, (waterFill π σ (π i / σ i) j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rwa [hfill] at hle
  have hmass_mono : computedMass π σ (π i / σ i) ≤
      computedMass π σ (fidelityBracket π σ p k).2 :=
    computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hgc.le hgc_lt.le
  have hmass2 : (π i) ^ 2 ≤ computedMass π σ (fidelityBracket π σ p k).2 :=
    le_trans hmass_gc hmass_mono

  have hwidth' : computedMass π σ (fidelityBracket π σ p k).2 -
        computedMass π σ (fidelityBracket π σ p k).1
      ≤ 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
    have hinc := computedWaterEnergy_increment π σ (fun j => ⟨hπ j, hσ' j⟩) hlo hle
    calc
      computedMass π σ (fidelityBracket π σ p k).2 -
          computedMass π σ (fidelityBracket π σ p k).1
          = computedWaterEnergy π σ (fidelityBracket π σ p k).2 -
            computedWaterEnergy π σ (fidelityBracket π σ p k).1 := rfl
      _ ≤ 2 * (∑ j, π j * σ j) *
            ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1) := hinc
      _ = 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
        rw [hwidth]

  have hp2k : 0 < p * (2 : ℚ) ^ k := by positivity
  have hW : 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k)
      ≤ ε * (π i) ^ 2 / p := by
    have h1 : 2 * (∑ j, π j * σ j) * computedWaterHigh π σ
        ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k / p := by
      rw [le_div_iff₀ hp]
      calc 2 * (∑ j, π j * σ j) * computedWaterHigh π σ * p
          = 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ := by ring
        _ ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k := hsteps
    have h2 : (2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k))
        = (2 * (∑ j, π j * σ j) * computedWaterHigh π σ) / (2 : ℚ) ^ k := by ring
    rw [h2]
    have h3 : (2 * (∑ j, π j * σ j) * computedWaterHigh π σ) / (2 : ℚ) ^ k
        ≤ (ε * (π i) ^ 2 * (2 : ℚ) ^ k / p) / (2 : ℚ) ^ k :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h4 : (ε * (π i) ^ 2 * (2 : ℚ) ^ k / p) / (2 : ℚ) ^ k = ε * (π i) ^ 2 / p := by
      field_simp [ne_of_gt hp, ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ k)]
    rw [h4] at h3
    exact h3

  have hM1 : 0 ≤ (computedMass π σ (fidelityBracket π σ p k).1 : ℚ) := by
    unfold computedMass
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hM1' : 0 ≤ ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ) := by
    exact_mod_cast hM1
  have hM2' : 0 ≤ ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) := by
    have h1 : (0 : ℝ) ≤ (π i : ℝ) := by exact_mod_cast hpi.le
    have h2 : ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ)
        ≥ (π i : ℝ) ^ 2 := by exact_mod_cast hmass2
    have h3 : 0 ≤ (π i : ℝ) ^ 2 := sq_nonneg _
    linarith
  have hid := sqrt_sub_mul_sum hM1' hM2'
  have hsqrt2 : (π i : ℝ) ≤
      Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) := by
    refine (Real.le_sqrt (x := (π i : ℝ))
      (y := ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ))
      (by exact_mod_cast hpi.le) hM2').mpr ?_
    exact_mod_cast hmass2
  have hsum : (π i : ℝ) ≤
      Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) +
        Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ) := by
    have h3 : 0 ≤ Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ) :=
      Real.sqrt_nonneg _
    linarith [h3]
  have hmono : computedMass π σ (fidelityBracket π σ p k).1 ≤
      computedMass π σ (fidelityBracket π σ p k).2 :=
    computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hlo hle
  have hdiff0 : 0 ≤
      ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
        ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ) := by
    have h1 : ((computedMass π σ (fidelityBracket π σ p k).2 -
        computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)
        = ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
          ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ) := by
      exact rat_sub_cast (computedMass π σ (fidelityBracket π σ p k).2)
        (computedMass π σ (fidelityBracket π σ p k).1)
    rw [← h1]
    exact_mod_cast (sub_nonneg.mpr hmono)
  have hwidthR : ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
        ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)
      ≤ ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) : ℚ) : ℝ) := by
    have h1 : ((computedMass π σ (fidelityBracket π σ p k).2 -
        computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)
        = ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
          ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ) := by
      exact rat_sub_cast (computedMass π σ (fidelityBracket π σ p k).2)
        (computedMass π σ (fidelityBracket π σ p k).1)
    rw [← h1]
    exact_mod_cast hwidth'

  have hprod : |Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
      Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)| * (π i : ℝ)
      ≤ ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) : ℚ) : ℝ) := by
    have h1 : |Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
        Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)| *
          ((Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ)) +
            Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ))
        ≤ ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) : ℚ) : ℝ) := by
      rw [hid, abs_of_nonneg hdiff0]
      exact hwidthR
    have h2 : |Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
        Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)| * (π i : ℝ)
        ≤ |Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
          Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)| *
            ((Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ)) +
              Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    exact h2.trans h1
  have hpiR : 0 < (π i : ℝ) := by exact_mod_cast hpi
  have hdiv : |Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
      Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)|
      ≤ ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) / (π i) : ℚ) : ℝ) := by
    have h1 : ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) / (π i) : ℚ) : ℝ)
        = ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) : ℚ) : ℝ) / (π i : ℝ) :=
      Rat.cast_div _ _
    rw [h1, le_div_iff₀ hpiR]
    exact hprod
  have hQ : (2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) / (π i) : ℚ)
      ≤ ε * π i / p := by
    rw [div_le_iff₀ (by exact_mod_cast hpi)]
    calc 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k)
        ≤ ε * (π i) ^ 2 / p := hW
      _ = (ε * π i / p) * (π i) := by field_simp [ne_of_gt hp]
  have hQ' : ((2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) / (π i) : ℚ) : ℝ)
      ≤ ((ε * π i / p : ℚ) : ℝ) := by
    exact_mod_cast hQ
  have hfinal : |Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).2 : ℚ) : ℝ) -
      Real.sqrt ((computedMass π σ (fidelityBracket π σ p k).1 : ℚ) : ℝ)|
      ≤ ((ε * π i / p : ℚ) : ℝ) := hdiv.trans hQ'
  simpa only [selectedBeta] using! hfinal

/-- The difference between a rational lower amplitude bound and the threshold `2 / (2 * t + 1)`
for a round budget. -/
def roundBudgetMargin (lo : ℚ) (t : ℕ) : ℚ := lo - 2 / (2 * (t : ℚ) + 1)

/-- Decreasing a lower amplitude bound by at most its round budget margin preserves the same
round budget. -/
theorem roundBudget_margin_stable {lo δ : ℚ} {t : ℕ}
    (ht : RoundBudget lo t) (hm : δ ≤ roundBudgetMargin lo t) :
    RoundBudget (lo - δ) t := by
  have hpos : 0 < 2 * (t : ℚ) + 1 := by positivity
  have hm' : δ ≤ lo - 2 / (2 * (t : ℚ) + 1) := by
    simpa only [roundBudgetMargin] using! hm
  have hkey : δ * (2 * (t : ℚ) + 1) ≤ lo * (2 * (t : ℚ) + 1) - 2 := by
    have h1 := mul_le_mul_of_nonneg_right hm' (le_of_lt hpos)
    have h2 : (lo - 2 / (2 * (t : ℚ) + 1)) * (2 * (t : ℚ) + 1)
        = lo * (2 * (t : ℚ) + 1) - 2 := by
      calc (lo - 2 / (2 * (t : ℚ) + 1)) * (2 * (t : ℚ) + 1)
          = lo * (2 * (t : ℚ) + 1) - (2 / (2 * (t : ℚ) + 1)) * (2 * (t : ℚ) + 1) := by ring
        _ = lo * (2 * (t : ℚ) + 1) - 2 := by rw [div_mul_cancel₀ _ hpos.ne']
    linarith
  refine ⟨?_, ?_⟩
  · have h1 : 2 / (2 * (t : ℚ) + 1) ≤ lo := by
      rw [div_le_iff₀ hpos]
      linarith [ht.2]
    have h2 : 2 / (2 * (t : ℚ) + 1) ≤ lo - δ := by linarith [hm']
    have h3 : 0 < 2 / (2 * (t : ℚ) + 1) := div_pos (by norm_num) hpos
    linarith
  · linarith [ht.2, hkey]

/-- The difference between the round floor threshold `1 / (2 * t - 1)` and a rational upper
amplitude bound. -/
def roundFloorMargin (hi : ℚ) (t : ℕ) : ℚ := 1 / (2 * (t : ℚ) - 1) - hi

/-- For `t ≥ 1`, increasing an upper amplitude bound by a nonnegative amount strictly below its
floor margin preserves `RoundFloor`. -/
theorem roundFloor_margin_stable {hi δ : ℚ} {t : ℕ} (hδ : 0 ≤ δ) (ht : 1 ≤ t)
    (hfloor : RoundFloor hi t) (hm : δ < roundFloorMargin hi t) :
    RoundFloor (hi + δ) t := by
  have hpos : 0 < 2 * (t : ℚ) - 1 := by
    have h1 : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
    linarith
  have hm' : δ < 1 / (2 * (t : ℚ) - 1) - hi := by
    simpa only [roundFloorMargin] using! hm
  have hkey : δ * (2 * (t : ℚ) - 1) < 1 - hi * (2 * (t : ℚ) - 1) := by
    have h1 := mul_lt_mul_of_pos_right hm' hpos
    have h2 : (1 / (2 * (t : ℚ) - 1) - hi) * (2 * (t : ℚ) - 1)
        = 1 - hi * (2 * (t : ℚ) - 1) := by
      calc (1 / (2 * (t : ℚ) - 1) - hi) * (2 * (t : ℚ) - 1)
          = (1 / (2 * (t : ℚ) - 1)) * (2 * (t : ℚ) - 1) - hi * (2 * (t : ℚ) - 1) := by ring
        _ = 1 - hi * (2 * (t : ℚ) - 1) := by rw [div_mul_cancel₀ _ hpos.ne']
    linarith
  refine ⟨?_, ?_⟩
  · linarith [hfloor.1, hδ]
  · linarith [hfloor.2, hkey]

/-- A round budget for the perturbed lower bound `lo - δ` bounds the exact resampling rounds
when that bound is at most the amplitude. -/
theorem resamplingExactRounds_le_of_budget_precision {β : ℝ} {lo δ : ℚ} {t : ℕ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hbudget : RoundBudget (lo - δ) t)
    (hlo : (lo - δ : ℚ) ≤ β) :
    resamplingExactRounds β ≤ t :=
  resamplingExactRounds_le_of_budget hβ hβ1 hbudget hlo

/-- For `t ≥ 1`, a round floor for the perturbed upper bound `hi + δ` gives a lower bound on
exact resampling rounds. -/
theorem resamplingExactRounds_ge_of_floor_precision {β : ℝ} {hi δ : ℚ} {t : ℕ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t) (hfloor : RoundFloor (hi + δ) t)
    (hhi : β ≤ (hi + δ : ℚ)) :
    t ≤ resamplingExactRounds β :=
  resamplingExactRounds_ge_of_floor hβ hβ1 ht hfloor hhi

/-- Rational amplitude bounds and `ScheduleWindows` bound the schedule angle's sine between half
the lower bound and the upper bound. -/
theorem scheduleWindow_rational_precision {β : ℝ} {lo hi : ℚ}
    (hlo : lo ≤ β) (hhi : β ≤ hi) (hw : ScheduleWindows β) :
    (lo : ℝ) / 2 ≤ Real.sin (resamplingExactAngle β) ∧
      Real.sin (resamplingExactAngle β) ≤ (hi : ℝ) := by
  unfold ScheduleWindows ScheduleClause scheduleTriple at hw
  simp only at hw
  have h9 : β / 2 ≤ Real.sin (resamplingExactAngle β) := hw.2.2.2.2.2.2.2.2.1
  have h10 : Real.sin (resamplingExactAngle β) ≤ β := hw.2.2.2.2.2.2.2.2.2.1
  constructor
  · exact (div_le_div_of_nonneg_right hlo (by norm_num)).trans h9
  · exact h10.trans hhi

/-- Combines fidelity and endpoint-amplitude error bounds with a round budget and sine window
enlarged by the amplitude error. -/
theorem frontier7 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hβ : 0 < selectedBeta π σ (fidelityBracket π σ p k).2)
    (hβ1 : selectedBeta π σ (fidelityBracket π σ p k).2 ≤ 1)
    (lo hi : ℚ)
    (hloβ : lo ≤ selectedBeta π σ (fidelityBracket π σ p k).1)
    (hhiβ : selectedBeta π σ (fidelityBracket π σ p k).1 ≤ hi)
    (t : ℕ) (htbudget : RoundBudget (lo - ε * π i / p) t) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε ∧
    |selectedBeta π σ (fidelityBracket π σ p k).2 -
        selectedBeta π σ (fidelityBracket π σ p k).1| ≤ ((ε * π i / p : ℚ) : ℝ) ∧
    resamplingExactRounds (selectedBeta π σ (fidelityBracket π σ p k).2) ≤ t ∧
    ((lo - ε * π i / p : ℚ) : ℝ) / 2 ≤
        Real.sin (resamplingExactAngle (selectedBeta π σ (fidelityBracket π σ p k).2)) ∧
    Real.sin (resamplingExactAngle (selectedBeta π σ (fidelityBracket π σ p k).2))
        ≤ (hi + ε * π i / p : ℚ) := by
  have hfid := certifiedFidelity_error π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  have hprec := certifiedBeta_precision π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  obtain ⟨hneg, hpos⟩ := abs_le.mp hprec
  have hβ2loR : ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ)
      ≤ selectedBeta π σ (fidelityBracket π σ p k).2 := by
    linarith
  have hβ2hiR : selectedBeta π σ (fidelityBracket π σ p k).2
      ≤ ((hi : ℚ) : ℝ) + ((ε * π i / p : ℚ) : ℝ) := by
    linarith
  have hβ2lo : (lo - ε * π i / p : ℚ)
      ≤ selectedBeta π σ (fidelityBracket π σ p k).2 := by
    have h1 : ((lo - ε * π i / p : ℚ) : ℝ)
        = ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ) := rat_sub_cast _ _
    rw [h1]
    exact hβ2loR
  have hβ2hi : selectedBeta π σ (fidelityBracket π σ p k).2
      ≤ (hi + ε * π i / p : ℚ) := by
    have h1 : ((hi + ε * π i / p : ℚ) : ℝ)
        = ((hi : ℚ) : ℝ) + ((ε * π i / p : ℚ) : ℝ) := Rat.cast_add _ _
    rw [h1]
    exact hβ2hiR
  have hrounds : resamplingExactRounds (selectedBeta π σ (fidelityBracket π σ p k).2) ≤ t :=
    resamplingExactRounds_le_of_budget hβ hβ1 htbudget hβ2lo
  have hw := (selectedSchedule_windows π σ (fidelityBracket π σ p k).2 hβ hβ1).1
  obtain ⟨hw1, hw2⟩ := scheduleWindow_rational_precision
    (β := selectedBeta π σ (fidelityBracket π σ p k).2)
    (lo := lo - ε * π i / p) (hi := hi + ε * π i / p) hβ2lo hβ2hi hw
  exact ⟨hfid, hprec, hrounds, hw1, hw2⟩

/-- The spacing `1 / 2 ^ b` of the rational dyadic grid. -/
def gridStep (b : ℕ) : ℚ := 1 / (2 : ℚ) ^ b

/-- The dyadic grid spacing is strictly positive. -/
theorem gridStep_pos (b : ℕ) : 0 < gridStep b := by
  unfold gridStep
  positivity

/-- Rounds a rational to the nearest dyadic grid point, choosing the upper point at a tie. -/
def gridRound (b : ℕ) (x : ℚ) : ℚ :=
  ((⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℤ) : ℚ) / (2 : ℚ) ^ b

/-- Nearest-grid rounding changes a rational by at most half the grid spacing. -/
theorem gridRound_error (b : ℕ) (x : ℚ) :
    |gridRound b x - x| ≤ gridStep b / 2 := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  have hfl := Int.floor_le (x * (2 : ℚ) ^ b + 1 / 2)
  have h2 : (⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℚ) ≤ x * (2 : ℚ) ^ b + 1 / 2 := by
    exact_mod_cast hfl
  have h3 : x * (2 : ℚ) ^ b + 1 / 2 < (⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℚ) + 1 := by
    have h := (Int.floor_lt (a := x * (2 : ℚ) ^ b + 1 / 2)
      (z := ⌊x * (2 : ℚ) ^ b + 1 / 2⌋ + 1)).mp (Int.lt_succ _)
    exact_mod_cast h
  have hlo : (⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℚ) - 1 / 2 ≤ x * (2 : ℚ) ^ b := by linarith
  have hhi : x * (2 : ℚ) ^ b < (⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℚ) + 1 / 2 := by linarith
  have habs : |(⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℚ) - x * (2 : ℚ) ^ b| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hd : gridRound b x - x =
      ((⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℚ) - x * (2 : ℚ) ^ b) / (2 : ℚ) ^ b := by
    unfold gridRound
    field_simp [hne]
  rw [hd, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  have hkey : (gridStep b / 2) * (2 : ℚ) ^ b = 1 / 2 := by
    unfold gridStep
    field_simp [hne]
  linarith

/-- Every rounded rational is an integer multiple of the grid spacing. -/
theorem gridRound_onGrid (b : ℕ) (x : ℚ) :
    ∃ n : ℤ, gridRound b x = (n : ℚ) * gridStep b := by
  refine ⟨(⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℤ), ?_⟩
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  unfold gridRound gridStep
  field_simp [hne]

/-- The filled mass obtained by rounding each squared water-fill entry before summing exactly. -/
def computedMassRounded (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  ∑ j, gridRound b (waterFill π σ γ j ^ 2)

/-- Entrywise nearest rounding changes the filled mass by at most `m` times half the grid
spacing. -/
theorem computedMassRounded_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    |computedMassRounded b π σ γ - computedMass π σ γ| ≤ (m : ℚ) * (gridStep b / 2) := by
  have hsum : computedMassRounded b π σ γ - computedMass π σ γ
      = ∑ j, (gridRound b (waterFill π σ γ j ^ 2) - (waterFill π σ γ j) ^ 2) := by
    unfold computedMassRounded computedMass computedWaterEnergy
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  have h1 : |∑ j, (gridRound b (waterFill π σ γ j ^ 2) - (waterFill π σ γ j) ^ 2)|
      ≤ ∑ j, |gridRound b (waterFill π σ γ j ^ 2) - (waterFill π σ γ j) ^ 2| :=
    Finset.abs_sum_le_sum_abs
      (fun j => gridRound b (waterFill π σ γ j ^ 2) - (waterFill π σ γ j) ^ 2)
      (Finset.univ : Finset (Fin m))
  have h2 : (∑ j, |gridRound b (waterFill π σ γ j ^ 2) - (waterFill π σ γ j) ^ 2|)
      ≤ ∑ _j : Fin m, gridStep b / 2 :=
    Finset.sum_le_sum fun j _ => gridRound_error b _
  have h3 : (∑ _j : Fin m, gridStep b / 2) = (m : ℚ) * (gridStep b / 2) := by
    simp [Finset.sum_const, Finset.card_univ]
  linarith

/-- The real square root of the entrywise rounded filled mass. -/
noncomputable def selectedBetaRounded (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℝ :=
  Real.sqrt (computedMassRounded b π σ γ)

/-- The rational amplitude error allowance obtained by dividing the entrywise mass error bound
by `πi`. -/
def betaRoundingError (b : ℕ) (πi : ℚ) (m : ℕ) : ℚ :=
  (m : ℚ) * (gridStep b / 2) / πi

/-- The real-valued expression for the entrywise rounding error allowance divided by `πi`. -/
noncomputable def betaRoundingErrorR (b : ℕ) (πi : ℚ) (m : ℕ) : ℝ :=
  ((m : ℚ) : ℝ) * (((gridStep b : ℚ) : ℝ) / 2) / ((πi : ℚ) : ℝ)

/-- The real amplitude rounding allowance equals the real cast of its rational counterpart. -/
theorem betaRoundingErrorR_eq (b : ℕ) (πi : ℚ) (m : ℕ) :
    betaRoundingErrorR b πi m = ((betaRoundingError b πi m : ℚ) : ℝ) := by
  unfold betaRoundingErrorR betaRoundingError
  push_cast
  ring

/-- A positive witness mass lower bound and sufficiently small entrywise mass error bound the
rounded amplitude error by `betaRoundingErrorR`. -/
theorem certifiedBeta_rounded {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (γ : ℚ) (i : Fin m)
    (hpi : 0 < π i) (hmass : (π i) ^ 2 ≤ computedMass π σ γ)
    (hdmsmall : (m : ℚ) * (gridStep b / 2) ≤ (π i) ^ 2 / 2) :
    |selectedBetaRounded b π σ γ - selectedBeta π σ γ| ≤ betaRoundingErrorR b (π i) m := by
  have hdm : 0 ≤ (m : ℚ) * (gridStep b / 2) := by
    have h1 : 0 ≤ (m : ℚ) := by exact_mod_cast Nat.zero_le m
    have h2 : 0 ≤ gridStep b / 2 := div_nonneg (gridStep_pos b).le (by norm_num)
    exact mul_nonneg h1 h2
  have hlo : (π i) ^ 2 / 2 ≤ computedMass π σ γ := by linarith
  have herr0 : |computedMassRounded b π σ γ - computedMass π σ γ|
      ≤ (m : ℚ) * (gridStep b / 2) := computedMassRounded_error b π σ γ
  have hhat : (π i) ^ 2 / 2 ≤ computedMassRounded b π σ γ := by
    obtain ⟨hneg, hpos⟩ := abs_le.mp herr0
    linarith
  have hpi2 : 0 < (π i) ^ 2 := sq_pos_of_pos hpi
  have hpi2half : 0 < (π i) ^ 2 / 2 := div_pos hpi2 (by norm_num)
  have hsqr := precisionSqrt_error (mLo := (π i) ^ 2 / 2) (dm := (m : ℚ) * (gridStep b / 2))
    (mass := computedMass π σ γ) (massHat := computedMassRounded b π σ γ)
    hpi2half hdm hlo hhat herr0

  have hpiR : 0 < (π i : ℝ) := by exact_mod_cast hpi
  have hmon : Real.sqrt (((π i : ℚ) ^ 2 / 4 : ℝ))
      ≤ Real.sqrt (((π i : ℚ) ^ 2 / 2 : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hhalf : Real.sqrt (((π i : ℚ) ^ 2 / 4 : ℝ)) = (π i : ℝ) / 2 := by
    have h1 : ((π i : ℚ) ^ 2 / 4 : ℝ) = ((π i : ℝ) / 2) ^ 2 := by
      ring
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  have hden : (π i : ℝ) ≤ 2 * Real.sqrt (((π i : ℚ) ^ 2 / 2 : ℝ)) := by
    have := hmon
    rw [hhalf] at this
    linarith
  have hdmcast : (((m : ℚ) * (gridStep b / 2) : ℚ) : ℝ)
      = ((m : ℚ) : ℝ) * (((gridStep b : ℚ) : ℝ) / 2) := by
    push_cast
    ring
  have hcast2 : (((π i : ℚ) ^ 2 / 2 : ℚ) : ℝ) = ((π i : ℝ) ^ 2 / 2) := by
    push_cast
    ring
  rw [hdmcast, hcast2] at hsqr
  have hdmR : (0 : ℝ) ≤ ((m : ℚ) : ℝ) * (((gridStep b : ℚ) : ℝ) / 2) := by
    have h1 : 0 ≤ ((m : ℚ) : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h2 : 0 ≤ ((gridStep b : ℚ) : ℝ) := by exact_mod_cast (gridStep_pos b).le
    have h3 : 0 ≤ ((gridStep b : ℚ) : ℝ) / 2 := div_nonneg h2 (by norm_num)
    exact mul_nonneg h1 h3
  have hdiv1 := div_le_div_of_nonneg_left hdmR hpiR hden
  unfold betaRoundingErrorR
  exact hsqr.trans hdiv1

/-- The minimum grid-spacing allowance ensuring the desired amplitude error and a mass error at
most half the squared witness entry. -/
def bitBudget (ε p : ℚ) (πi : ℚ) (m : ℕ) : ℚ :=
  min (2 * ε * πi ^ 2 / ((m : ℚ) * p)) (πi ^ 2 / (m : ℚ))

/-- The bit budget is positive when the tolerance, target, witness entry, and table size are
positive. -/
theorem bitBudget_pos {ε p πi : ℚ} {m : ℕ} (hm : 0 < m) (hε : 0 < ε) (hp : 0 < p)
    (hπi : 0 < πi) : 0 < bitBudget ε p πi m := by
  unfold bitBudget
  apply lt_min
  · positivity
  · positivity

/-- Every positive rational spacing allowance is reached by some dyadic grid precision. -/
theorem exists_bitBudget {B : ℚ} (hB : 0 < B) : ∃ b : ℕ, gridStep b ≤ B := by
  obtain ⟨N, hN⟩ := exists_two_pow_ge (X := 1 / B)
  have h1 : (1 : ℚ) ≤ (2 : ℚ) ^ N * B := by
    have h := mul_le_mul_of_nonneg_right hN hB.le
    have h2 : (1 / B) * B = 1 := by field_simp
    rw [h2] at h
    exact h
  refine ⟨N, ?_⟩
  have hne : (0 : ℚ) < (2 : ℚ) ^ N := by positivity
  unfold gridStep
  rw [div_le_iff₀ hne]
  have h2 : B * (2 : ℚ) ^ N = (2 : ℚ) ^ N * B := by ring
  rw [h2]
  linarith

/-- The least natural precision whose dyadic grid spacing is at most a given positive rational
allowance. -/
noncomputable def bitBudgetSearch (B : ℚ) (hB : 0 < B) : ℕ :=
  Nat.find (p := fun b => gridStep b ≤ B) (exists_bitBudget hB)

/-- The precision chosen by `bitBudgetSearch` has grid spacing at most the requested allowance. -/
theorem bitBudgetSearch_spec {B : ℚ} (hB : 0 < B) : gridStep (bitBudgetSearch B hB) ≤ B :=
  Nat.find_spec (p := fun b => gridStep b ≤ B) (exists_bitBudget hB)

/-- The bit budget search chooses no larger a precision than any precision meeting its spacing
allowance. -/
theorem bitBudgetSearch_le {B : ℚ} (hB : 0 < B) {b : ℕ} (hb : gridStep b ≤ B) :
    bitBudgetSearch B hB ≤ b :=
  Nat.find_le (p := fun b => gridStep b ≤ B) (h := exists_bitBudget hB) hb

/-- Positive tolerance, target, witness entry, and table size ensure existence of a precision
meeting `bitBudget`. -/
theorem exists_bitBudgetSufficient {ε p πi : ℚ} {m : ℕ} (hm : 0 < m) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) : ∃ b : ℕ, gridStep b ≤ bitBudget ε p πi m := by
  refine ⟨bitBudgetSearch (bitBudget ε p πi m) (bitBudget_pos hm hε hp hπi), ?_⟩
  exact bitBudgetSearch_spec (bitBudget_pos hm hε hp hπi)

/-- Meeting the bit budget bounds the amplitude error allowance by `ε * πi / p` and the mass
error allowance by `πi ^ 2 / 2`. -/
theorem bitBudget_sufficient {ε p πi : ℚ} {m : ℕ} (hm : 0 < m) (hε : 0 < ε) (hp : 0 < p)
    (hπi : 0 < πi) (b : ℕ) (hb : gridStep b ≤ bitBudget ε p πi m) :
    (m : ℚ) * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (m : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  have hbA : gridStep b ≤ 2 * ε * πi ^ 2 / ((m : ℚ) * p) :=
    le_trans hb (min_le_left _ _)
  have hbB : gridStep b ≤ πi ^ 2 / (m : ℚ) :=
    le_trans hb (min_le_right _ _)
  have hmp : 0 < ((m : ℚ) * p) := mul_pos (by exact_mod_cast hm) hp
  have h1 : (m : ℚ) * (gridStep b / 2) * p ≤ ε * πi ^ 2 := by
    have h2 : gridStep b * ((m : ℚ) * p) ≤ 2 * ε * πi ^ 2 := by
      have hb' := mul_le_mul_of_nonneg_right hbA hmp.le
      have h3 : (2 * ε * πi ^ 2 / ((m : ℚ) * p)) * ((m : ℚ) * p) = 2 * ε * πi ^ 2 := by
        field_simp [ne_of_gt hmp]
      rwa [h3] at hb'
    have h4 : (m : ℚ) * (gridStep b / 2) * p = gridStep b * ((m : ℚ) * p) / 2 := by ring
    rw [h4]
    linarith
  have h2 : (m : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
    have h4 : (m : ℚ) * (gridStep b / 2) = (m : ℚ) * gridStep b / 2 := by ring
    rw [h4]
    have h5 : (m : ℚ) * gridStep b ≤ (m : ℚ) * (πi ^ 2 / (m : ℚ)) :=
      mul_le_mul_of_nonneg_left hbB (by exact_mod_cast (Nat.zero_le m))
    have h6 : (m : ℚ) * (πi ^ 2 / (m : ℚ)) = πi ^ 2 := by field_simp
    rw [h6] at h5
    linarith
  refine ⟨?_, h2⟩
  rw [div_le_div_iff₀ hπi hp]
  linarith

/-- The combined amplitude loss from the fidelity tolerance and a mass error allowance `dm`. -/
def precisionLoss (ε p : ℚ) (πi : ℚ) (dm : ℚ) : ℚ := ε * πi / p + dm / πi

/-- A valid round budget has nonnegative round budget margin. -/
theorem roundBudgetMargin_nonneg {lo : ℚ} {t : ℕ} (ht : RoundBudget lo t) :
    0 ≤ roundBudgetMargin lo t := by
  have hpos : 0 < 2 * (t : ℚ) + 1 := by positivity
  have h1 : 2 / (2 * (t : ℚ) + 1) ≤ lo := by
    rw [div_le_iff₀ hpos]
    linarith [ht.2]
  simpa only [roundBudgetMargin] using! sub_nonneg.mpr h1

/-- An error allowance no larger than the round budget margin preserves the budget after
subtracting that allowance from the lower amplitude bound. -/
theorem roundBudget_of_precisionLoss {lo : ℚ} {t : ℕ} {δ : ℚ}
    (htbudget : RoundBudget lo t) (hmargin : δ ≤ roundBudgetMargin lo t) :
    RoundBudget (lo - δ) t :=
  roundBudget_margin_stable htbudget hmargin

/-- A margin witness gives a lower bound of `(π i) ^ 2` on the filled mass at the upper fidelity
bracket endpoint. -/
theorem certifiedMass_at_certifiedLevel {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i : Fin m) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i)) :
    (π i) ^ 2 ≤ computedMass π σ (fidelityBracket π σ p k).2 := by
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  obtain ⟨hlo, hle, hhi, hwidth, hreach, hnotreach⟩ := hbr
  have hgc : 0 < π i / σ i := div_pos hpi (hσ i)
  have hb0 : 0 ≤ (fidelityBracket π σ p k).2 := hlo.trans hle
  have hgc_lt : π i / σ i < (fidelityBracket π σ p k).2 := by
    by_contra hcon
    have hle' : (fidelityBracket π σ p k).2 ≤ π i / σ i := le_of_not_gt hcon
    exact hnotreach (fidelityReaches_mono π σ p hπ hσ' hb0 hle' hmargin)
  have hfill : waterFill π σ (π i / σ i) i = π i := by
    rw [waterFill]
    have hne : σ i ≠ 0 := (hσ i).ne'
    have heq : (π i / σ i) * σ i = π i := by field_simp
    rw [heq, min_eq_left (le_refl _)]
  have hmass_gc : (π i) ^ 2 ≤ computedMass π σ (π i / σ i) := by
    unfold computedMass
    have hle : (waterFill π σ (π i / σ i) i) ^ 2 ≤
        ∑ j, (waterFill π σ (π i / σ i) j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rwa [hfill] at hle
  have hmass_mono : computedMass π σ (π i / σ i) ≤
      computedMass π σ (fidelityBracket π σ p k).2 :=
    computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hgc.le hgc_lt.le
  exact le_trans hmass_gc hmass_mono

/-- The bit budget bounds the upper endpoint's rounded amplitude error and gives a lower bound
obtained from the lower endpoint amplitude and both error allowances. -/
theorem certifiedRoundBudget_bitBudget {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m)
    (k b : ℕ) (lo : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hm : 0 < m)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hloβ : lo ≤ selectedBeta π σ (fidelityBracket π σ p k).1)
    (hbits : gridStep b ≤ bitBudget ε p (π i) m) :
    |selectedBetaRounded b π σ (fidelityBracket π σ p k).2 - selectedBeta π σ (fidelityBracket π σ p k).2|
        ≤ betaRoundingErrorR b (π i) m ∧
    (m : ℚ) * (gridStep b / 2) / (π i) ≤ ε * π i / p ∧
    ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ) - betaRoundingErrorR b (π i) m
      ≤ selectedBetaRounded b π σ (fidelityBracket π σ p k).2 := by
  have hparts := bitBudget_sufficient hm hε hp (by exact_mod_cast hpi) b hbits
  have hdm : (m : ℚ) * (gridStep b / 2) ≤ (π i) ^ 2 / 2 := hparts.2
  have hmass := certifiedMass_at_certifiedLevel π σ p i k hπ hσ hpi hrange hmargin
  have hround := certifiedBeta_rounded π σ b (fidelityBracket π σ p k).2 i hpi hmass hdm
  have hprec := certifiedBeta_precision π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  refine ⟨hround, hparts.1, ?_⟩
  obtain ⟨hneg, _⟩ := abs_le.mp hprec
  have hloR : ((lo : ℚ) : ℝ) ≤ selectedBeta π σ (fidelityBracket π σ p k).1 := by
    exact_mod_cast hloβ
  obtain ⟨hneg2, _⟩ := abs_le.mp hround
  have h1 : ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ)
      ≤ selectedBeta π σ (fidelityBracket π σ p k).2 := by linarith
  have h2 : selectedBeta π σ (fidelityBracket π σ p k).2 - betaRoundingErrorR b (π i) m
      ≤ selectedBetaRounded b π σ (fidelityBracket π σ p k).2 := by linarith
  linarith

/-- Combines fidelity, endpoint-amplitude, and entrywise rounding error bounds with preservation
of a round budget under the combined precision loss. -/
theorem frontier8 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k b : ℕ)
    (lo : ℚ) (t : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hm : 0 < m)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hloβ : lo ≤ selectedBeta π σ (fidelityBracket π σ p k).1)
    (htbudget : RoundBudget lo t)
    (hbits : gridStep b ≤ bitBudget ε p (π i) m)
    (hmarginbudget : precisionLoss ε p (π i) ((m : ℚ) * (gridStep b / 2))
                     ≤ roundBudgetMargin lo t) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε ∧
    |selectedBeta π σ (fidelityBracket π σ p k).2 -
        selectedBeta π σ (fidelityBracket π σ p k).1| ≤ ((ε * π i / p : ℚ) : ℝ) ∧
    |selectedBetaRounded b π σ (fidelityBracket π σ p k).2 -
        selectedBeta π σ (fidelityBracket π σ p k).2| ≤ betaRoundingErrorR b (π i) m ∧
    (m : ℚ) * (gridStep b / 2) / (π i) ≤ ε * π i / p ∧
    RoundBudget (lo - precisionLoss ε p (π i) ((m : ℚ) * (gridStep b / 2))) t := by
  have hfid := certifiedFidelity_error π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  have hprec := certifiedBeta_precision π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  obtain ⟨hround, hbudget', _⟩ :=
    certifiedRoundBudget_bitBudget π σ p ε i k b lo hπ hσ hp hε hpi hm hrange hmargin
      hsteps hloβ hbits
  have hweakened : RoundBudget (lo - precisionLoss ε p (π i) ((m : ℚ) * (gridStep b / 2))) t :=
    roundBudget_of_precisionLoss htbudget hmarginbudget
  exact ⟨hfid, hprec, hround, hbudget', hweakened⟩

/-- The absolute difference between two rationals is bounded by the sum of their absolute
differences through a third rational. -/
theorem abs_sub_triangle (a b c : ℚ) : |a - c| ≤ |a - b| + |b - c| := by
  have h1 : -|a - b| ≤ a - b ∧ a - b ≤ |a - b| := abs_le.mp (le_refl (|a - b|))
  have h2 : -|b - c| ≤ b - c ∧ b - c ≤ |b - c| := abs_le.mp (le_refl (|b - c|))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A left fold of a rational binary operation through a list from a given accumulator. -/
def exactFold (f : ℚ → ℚ → ℚ) : ℚ → List ℚ → ℚ
  | acc, [] => acc
  | acc, x :: xs => exactFold f (f acc x) xs

/-- A left fold that rounds the accumulator to the dyadic grid after each application of a
rational binary operation. -/
def roundedFold (b : ℕ) (f : ℚ → ℚ → ℚ) : ℚ → List ℚ → ℚ
  | acc, [] => acc
  | acc, x :: xs => roundedFold b f (gridRound b (f acc x)) xs

/-- If each operation is nonexpansive in its accumulator, its exact fold is nonexpansive in the
initial accumulator. -/
theorem exactFold_lipschitz {f : ℚ → ℚ → ℚ}
    (hf : ∀ a a' x : ℚ, |f a x - f a' x| ≤ |a - a'|) :
    ∀ (a a' : ℚ) (xs : List ℚ), |exactFold f a xs - exactFold f a' xs| ≤ |a - a'| := by
  intro a a' xs
  induction xs generalizing a a' with
  | nil => simp [exactFold]
  | cons x xs ih =>
      simp only [exactFold]
      calc
        |exactFold f (f a x) xs - exactFold f (f a' x) xs| ≤ |f a x - f a' x| :=
          ih (f a x) (f a' x)
        _ ≤ |a - a'| := hf a a' x

/-- For an operation nonexpansive in its accumulator, the rounded fold differs from the exact
fold by at most half a grid spacing per list entry. -/
theorem roundedFold_error (b : ℕ) (f : ℚ → ℚ → ℚ)
    (hf : ∀ a a' x : ℚ, |f a x - f a' x| ≤ |a - a'|)
    (acc : ℚ) (xs : List ℚ) :
    |roundedFold b f acc xs - exactFold f acc xs| ≤ (xs.length : ℚ) * (gridStep b / 2) := by
  induction xs generalizing acc with
  | nil => simp [roundedFold, exactFold]
  | cons x xs ih =>
      have hstep : |gridRound b (f acc x) - f acc x| ≤ gridStep b / 2 := gridRound_error b _
      have hlip : |exactFold f (gridRound b (f acc x)) xs - exactFold f (f acc x) xs|
          ≤ |gridRound b (f acc x) - f acc x| := exactFold_lipschitz hf _ _ _
      have hind : |roundedFold b f (gridRound b (f acc x)) xs
          - exactFold f (gridRound b (f acc x)) xs| ≤ (xs.length : ℚ) * (gridStep b / 2) :=
        ih (gridRound b (f acc x))
      have htri : |roundedFold b f (gridRound b (f acc x)) xs - exactFold f (f acc x) xs|
          ≤ |roundedFold b f (gridRound b (f acc x)) xs
              - exactFold f (gridRound b (f acc x)) xs|
            + |exactFold f (gridRound b (f acc x)) xs - exactFold f (f acc x) xs| :=
        abs_sub_triangle _ _ _
      simp only [roundedFold, exactFold]
      calc
        |roundedFold b f (gridRound b (f acc x)) xs - exactFold f (f acc x) xs|
            ≤ |roundedFold b f (gridRound b (f acc x)) xs
                  - exactFold f (gridRound b (f acc x)) xs|
              + |exactFold f (gridRound b (f acc x)) xs - exactFold f (f acc x) xs| := htri
        _ ≤ (xs.length : ℚ) * (gridStep b / 2) + |gridRound b (f acc x) - f acc x| :=
              add_le_add hind hlip
        _ ≤ (xs.length : ℚ) * (gridStep b / 2) + (gridStep b / 2) := by
              linarith [hstep]
        _ = ((x :: xs).length : ℚ) * (gridStep b / 2) := by
              simp only [List.length_cons]
              push_cast
              ring

/-- The sum computed by adding list entries sequentially and rounding the accumulator after
every addition. -/
def gridSum (b : ℕ) (xs : List ℚ) : ℚ := roundedFold b (fun a x => a + x) 0 xs

/-- Folding rational addition adds the list sum to the initial accumulator. -/
theorem exactFold_add (acc : ℚ) (xs : List ℚ) :
    exactFold (fun a x => a + x) acc xs = acc + (xs.sum : ℚ) := by
  induction xs generalizing acc with
  | nil => simp [exactFold]
  | cons x xs ih =>
      simp only [exactFold, List.sum_cons]
      rw [ih]
      ring

/-- Sequentially rounded summation differs from the exact sum by at most half a grid spacing per
entry. -/
theorem gridSum_error (b : ℕ) (xs : List ℚ) :
    |gridSum b xs - (xs.sum : ℚ)| ≤ (xs.length : ℚ) * (gridStep b / 2) := by
  have h := roundedFold_error b (fun a x => a + x) (fun a a' x => by
      have h1 : a + x - (a' + x) = a - a' := by ring
      rw [h1]) 0 xs
  rw [exactFold_add, zero_add] at h
  exact h

/-- The filled mass computed by rounding each square and then summing with a rounded
accumulator. -/
def computedMassSeq (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  gridSum b (List.ofFn fun j => gridRound b ((waterFill π σ γ j) ^ 2))

/-- The count `2 * m` assigned to rounded square and accumulation operations for a mass
computation. -/
def massRoundedOps (m : ℕ) : ℕ := 2 * m

/-- The sequentially rounded filled mass has absolute error at most `2 * m` times half the grid
spacing. -/
theorem computedMassSeq_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    |computedMassSeq b π σ γ - computedMass π σ γ| ≤ (2 * m : ℚ) * (gridStep b / 2) := by
  unfold computedMassSeq
  have h1 : |gridSum b (List.ofFn fun j => gridRound b ((waterFill π σ γ j) ^ 2))
      - ∑ j, gridRound b ((waterFill π σ γ j) ^ 2)| ≤ (m : ℚ) * (gridStep b / 2) := by
    have h := gridSum_error b (List.ofFn fun j => gridRound b ((waterFill π σ γ j) ^ 2))
    rw [List.sum_ofFn, List.length_ofFn] at h
    exact h
  have h2 : |(∑ j, gridRound b ((waterFill π σ γ j) ^ 2))
      - ∑ j, (waterFill π σ γ j) ^ 2| ≤ (m : ℚ) * (gridStep b / 2) := by
    have hsum' : (∑ j, gridRound b ((waterFill π σ γ j) ^ 2))
        - ∑ j, (waterFill π σ γ j) ^ 2
        = ∑ j, (gridRound b ((waterFill π σ γ j) ^ 2) - (waterFill π σ γ j) ^ 2) := by
      rw [Finset.sum_sub_distrib]
    rw [hsum']
    have h3 : |∑ j, (gridRound b ((waterFill π σ γ j) ^ 2) - (waterFill π σ γ j) ^ 2)|
        ≤ ∑ j, |gridRound b ((waterFill π σ γ j) ^ 2) - (waterFill π σ γ j) ^ 2| :=
      Finset.abs_sum_le_sum_abs
        (fun j => gridRound b ((waterFill π σ γ j) ^ 2) - (waterFill π σ γ j) ^ 2)
        (Finset.univ : Finset (Fin m))
    have h4 : (∑ j, |gridRound b ((waterFill π σ γ j) ^ 2) - (waterFill π σ γ j) ^ 2|)
        ≤ ∑ _j : Fin m, gridStep b / 2 :=
      Finset.sum_le_sum fun j _ => gridRound_error b _
    have h5 : (∑ _j : Fin m, gridStep b / 2) = (m : ℚ) * (gridStep b / 2) := by
      simp [Finset.sum_const, Finset.card_univ]
    linarith
  have hmass : computedMass π σ γ = ∑ j, (waterFill π σ γ j) ^ 2 := by
    simp only [computedMass, computedWaterEnergy]
  have htri : |gridSum b (List.ofFn fun j => gridRound b ((waterFill π σ γ j) ^ 2))
      - computedMass π σ γ|
      ≤ |gridSum b (List.ofFn fun j => gridRound b ((waterFill π σ γ j) ^ 2))
          - ∑ j, gridRound b ((waterFill π σ γ j) ^ 2)|
        + |(∑ j, gridRound b ((waterFill π σ γ j) ^ 2))
            - ∑ j, (waterFill π σ γ j) ^ 2| := by
    rw [hmass]
    exact abs_sub_triangle _ _ _
  linarith

/-- Twice half the grid spacing equals the grid spacing. -/
theorem gridStep_half (b : ℕ) : 2 * (gridStep b / 2) = gridStep b := by
  unfold gridStep
  ring

/-- Compares two rationals after rounding each to the dyadic grid. -/
def gridCompare (b : ℕ) (x y : ℚ) : Bool := decide (gridRound b x ≤ gridRound b y)

/-- If two rationals are separated by more than one grid spacing, their rounded comparison
equals their exact comparison. -/
theorem gridCompare_exact_of_sep (b : ℕ) {x y : ℚ} (h : gridStep b < |x - y|) :
    gridCompare b x y = decide (x ≤ y) := by
  have hx : x - gridStep b / 2 ≤ gridRound b x ∧ gridRound b x ≤ x + gridStep b / 2 := by
    have h1 := gridRound_error b x
    rw [abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have hy : y - gridStep b / 2 ≤ gridRound b y ∧ gridRound b y ≤ y + gridStep b / 2 := by
    have h1 := gridRound_error b y
    rw [abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have hhalf : 2 * (gridStep b / 2) = gridStep b := gridStep_half b
  unfold gridCompare
  by_cases hxy : x ≤ y
  · have habs : |x - y| = y - x := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    have hsep : gridStep b ≤ y - x := by
      rw [habs] at h
      linarith
    have hgap : x + gridStep b / 2 ≤ y - gridStep b / 2 := by linarith
    have h1 : gridRound b x ≤ gridRound b y := by linarith
    have hdec : (decide (gridRound b x ≤ gridRound b y) : Bool) = true := decide_eq_true h1
    have hd : (decide (x ≤ y) : Bool) = true := decide_eq_true hxy
    rw [hdec, hd]
  · have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
    have hsep : gridStep b ≤ x - y := by
      rw [habs] at h
      linarith
    have hgap : y + gridStep b / 2 < x - gridStep b / 2 := by linarith
    have hnot : ¬ (gridRound b x ≤ gridRound b y) := by linarith
    have hdec : (decide (gridRound b x ≤ gridRound b y) : Bool) = false := decide_eq_false hnot
    have hd : (decide (x ≤ y) : Bool) = false := decide_eq_false hxy
    rw [hdec, hd]

/-- Disagreement between rounded and exact comparisons implies separation at most one grid
spacing. -/
theorem gridCompare_ambiguous (b : ℕ) {x y : ℚ}
    (h : gridCompare b x y ≠ decide (x ≤ y)) : |x - y| ≤ gridStep b := by
  by_contra hcon
  exact h (gridCompare_exact_of_sep b (by linarith))

/-- The fidelity test obtained by comparing the rounded target-weighted mass and rounded squared
dot product. -/
def predicateRounded (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : Bool :=
  gridCompare b (p * computedMass π σ γ) (computedDot π σ γ ^ 2)

/-- If the fidelity comparison gap exceeds one grid spacing, the rounded predicate agrees with
the exact squared-dot-product test. -/
theorem predicateRounded_agrees_of_gap (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ)
    (h : gridStep b < |p * computedMass π σ γ - computedDot π σ γ ^ 2|) :
    predicateRounded b π σ p γ = decide (computedDot π σ γ ^ 2 ≥ p * computedMass π σ γ) := by
  unfold predicateRounded
  rw [gridCompare_exact_of_sep b h]

/-- If the fidelity comparison gap exceeds one grid spacing, the rounded predicate is true
exactly when `fidelityReaches` holds. -/
theorem predicateRounded_agrees_of_gap_reaches (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ)
    (h : gridStep b < |p * computedMass π σ γ - computedDot π σ γ ^ 2|) :
    predicateRounded b π σ p γ = true ↔ fidelityReaches π σ p γ := by
  rw [predicateRounded_agrees_of_gap b π σ p γ h]
  constructor
  · intro hh
    have hh2 : computedDot π σ γ ^ 2 ≥ p * computedMass π σ γ := of_decide_eq_true hh
    exact hh2
  · intro hh
    have hh2 : computedDot π σ γ ^ 2 ≥ p * computedMass π σ γ := hh
    exact decide_eq_true hh2

/-- Disagreement between the rounded and exact fidelity tests implies a comparison gap at most
one grid spacing. -/
theorem predicateRounded_ambiguous (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ)
    (h : predicateRounded b π σ p γ ≠ decide (computedDot π σ γ ^ 2 ≥ p * computedMass π σ γ)) :
    |p * computedMass π σ γ - computedDot π σ γ ^ 2| ≤ gridStep b := by
  unfold predicateRounded at h
  have h' : gridCompare b (p * computedMass π σ γ) (computedDot π σ γ ^ 2)
      ≠ decide (p * computedMass π σ γ ≤ computedDot π σ γ ^ 2) := h
  exact gridCompare_ambiguous b h'

/-- A level inside the certified bracket, above the witness ratio, and satisfying
`fidelityReaches` has fidelity error at most `ε` under the stated depth bound. -/
theorem certifiedFidelity_error_at {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k : ℕ)
    (γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hγlo : (fidelityBracket π σ p k).1 ≤ γ)
    (hγhi : γ ≤ (fidelityBracket π σ p k).2)
    (hγgc : π i / σ i ≤ γ)
    (hγreach : fidelityReaches π σ p γ) :
    |computedFidelity π σ γ - p| ≤ ε := by
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  have hb0 : 0 ≤ (fidelityBracket π σ p k).1 := hbr.1
  have hb1 : (fidelityBracket π σ p k).1 ≤ (fidelityBracket π σ p k).2 := hbr.2.1
  have hwidth : (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1 =
      computedWaterHigh π σ / (2 : ℚ) ^ k := hbr.2.2.2.1
  have hnotreach : ¬ (computedDot π σ (fidelityBracket π σ p k).2 ^ 2 ≥
      p * computedMass π σ (fidelityBracket π σ p k).2) := hbr.2.2.2.2.2
  have hγ0 : 0 ≤ γ := le_trans hb0 hγlo

  have hgc : 0 < π i / σ i := div_pos hpi (hσ i)
  have hmass_gc : (π i) ^ 2 ≤ computedMass π σ (π i / σ i) := by
    unfold computedMass
    have hfill : waterFill π σ (π i / σ i) i = π i := by
      rw [waterFill]
      have hne : σ i ≠ 0 := (hσ i).ne'
      have heq : (π i / σ i) * σ i = π i := by field_simp
      rw [heq, min_eq_left (le_refl _)]
    have hle : (waterFill π σ (π i / σ i) i) ^ 2 ≤
        ∑ j, (waterFill π σ (π i / σ i) j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rwa [hfill] at hle
  have hmass_mono : computedMass π σ (π i / σ i) ≤ computedMass π σ γ :=
    computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hgc.le hγgc
  have hmass_b : (π i) ^ 2 ≤ computedMass π σ γ := le_trans hmass_gc hmass_mono
  have hmass_pos : 0 < computedMass π σ γ := lt_of_lt_of_le (sq_pos_of_pos hpi) hmass_b

  have hdot_mono2 : computedDot π σ γ ≤ computedDot π σ (fidelityBracket π σ p k).2 :=
    computedDot_mono π σ hσ' hγhi

  have hmass_inc : computedMass π σ (fidelityBracket π σ p k).2 - computedMass π σ γ ≤
      2 * (∑ j, π j * σ j) * ((fidelityBracket π σ p k).2 - γ) :=
    computedWaterEnergy_increment π σ (fun j => ⟨hπ j, hσ' j⟩) hγ0 hγhi

  have hgap : computedDot π σ γ ^ 2 - p * computedMass π σ γ ≤
      p * (2 * (∑ j, π j * σ j) * ((fidelityBracket π σ p k).2 - γ)) := by
    have hsq : computedDot π σ γ ^ 2 ≤ computedDot π σ (fidelityBracket π σ p k).2 ^ 2 := by
      have h1 : 0 ≤ computedDot π σ γ := computedDot_nonneg π σ hπ hσ' hγ0
      have h2 : 0 ≤ computedDot π σ (fidelityBracket π σ p k).2 :=
        computedDot_nonneg π σ hπ hσ' (le_trans hb0 hb1)
      nlinarith [sq_nonneg (computedDot π σ γ),
        sq_nonneg (computedDot π σ (fidelityBracket π σ p k).2), hdot_mono2, h1, h2]
    have hneg : computedDot π σ (fidelityBracket π σ p k).2 ^ 2 -
        p * computedMass π σ (fidelityBracket π σ p k).2 < 0 :=
      sub_neg.mpr (lt_of_not_ge hnotreach)
    have hmass_diff : 0 ≤ computedMass π σ (fidelityBracket π σ p k).2 - computedMass π σ γ :=
      sub_nonneg.mpr (computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hγ0 hγhi)
    have hp0 : 0 ≤ p := hp.le
    nlinarith [hsq, hneg, hmass_inc, hmass_diff]

  have hwin : p * (2 * (∑ j, π j * σ j) * ((fidelityBracket π σ p k).2 - γ))
      ≤ ε * (π i) ^ 2 := by
    have hwidth' : (fidelityBracket π σ p k).2 - γ ≤ computedWaterHigh π σ / (2 : ℚ) ^ k := by
      rw [← hwidth]
      have h1 : (fidelityBracket π σ p k).1 ≤ γ := hγlo
      linarith
    have h2 : 2 * (∑ j, π j * σ j) * p * (computedWaterHigh π σ / (2 : ℚ) ^ k)
        ≤ ε * (π i) ^ 2 := by
      have hpos2 : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
      have heq : 2 * (∑ j, π j * σ j) * p * (computedWaterHigh π σ / (2 : ℚ) ^ k)
          = (2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ) / (2 : ℚ) ^ k := by
        field_simp
      rw [heq]
      exact (div_le_iff₀ hpos2).2 hsteps
    have hD : 0 ≤ (∑ j, π j * σ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ' j)
    have hp0 : 0 ≤ p := hp.le
    have hA : p * (2 * (∑ j, π j * σ j) * ((fidelityBracket π σ p k).2 - γ))
        ≤ p * (2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k)) := by
      have hnonneg : 0 ≤ p * (2 * (∑ j, π j * σ j)) := mul_nonneg hp0 (by linarith)
      have hC : p * (2 * (∑ j, π j * σ j) * ((fidelityBracket π σ p k).2 - γ))
          = (p * (2 * (∑ j, π j * σ j))) * ((fidelityBracket π σ p k).2 - γ) := by ring
      have hD' : p * (2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k))
          = (p * (2 * (∑ j, π j * σ j))) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by ring
      rw [hC, hD']
      exact mul_le_mul_of_nonneg_left hwidth' hnonneg
    have hB : p * (2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k))
        = (2 * (∑ j, π j * σ j)) * p * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by ring
    exact hA.trans (by rw [hB]; exact h2)

  have hfid : computedFidelity π σ γ =
      computedDot π σ γ ^ 2 / computedMass π σ γ := by
    unfold computedFidelity
    rw [if_neg (ne_of_gt hmass_pos)]
  have hsub : computedDot π σ γ ^ 2 / computedMass π σ γ - p =
      (computedDot π σ γ ^ 2 - p * computedMass π σ γ) / computedMass π σ γ := by
    field_simp
  rw [hfid, hsub, abs_div, abs_of_nonneg (le_of_lt hmass_pos)]
  refine (div_le_iff₀ hmass_pos).2 ?_
  have hnonneg : 0 ≤ computedDot π σ γ ^ 2 - p * computedMass π σ γ := by
    unfold fidelityReaches at hγreach
    linarith
  have habs : |computedDot π σ γ ^ 2 - p * computedMass π σ γ|
      = computedDot π σ γ ^ 2 - p * computedMass π σ γ := abs_of_nonneg hnonneg
  rw [habs]
  nlinarith [hgap, hwin, hmass_b, hε.le]

/-- A successful level above the witness ratio and within one bracket width below the upper
endpoint has fidelity error at most `ε` under the stated depth bound. -/
theorem certifiedFidelity_error_ambiguous {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m)
    (k : ℕ) (γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hγhi : γ ≤ (fidelityBracket π σ p k).2)
    (hγlo : (fidelityBracket π σ p k).2 - computedWaterHigh π σ / (2 : ℚ) ^ k ≤ γ)
    (hγgc : π i / σ i ≤ γ)
    (hγreach : fidelityReaches π σ p γ) :
    |computedFidelity π σ γ - p| ≤ ε := by
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  have hwidth : (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1 =
      computedWaterHigh π σ / (2 : ℚ) ^ k := hbr.2.2.2.1
  have hγlo' : (fidelityBracket π σ p k).1 ≤ γ := by
    have h1 : (fidelityBracket π σ p k).1 =
        (fidelityBracket π σ p k).2 - computedWaterHigh π σ / (2 : ℚ) ^ k := by
      linarith [hwidth]
    rw [h1]
    exact hγlo
  exact certifiedFidelity_error_at π σ p ε i k γ hπ hσ hp hε hpi hrange hsteps
    hγlo' hγhi hγgc hγreach

/-- The upper bracket endpoint lies strictly above any witness ratio satisfying the margin
inequality, under the strict initial bracket inequality. -/
theorem certifiedLevel_above_breakpoint {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i : Fin m) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i)) :
    π i / σ i < (fidelityBracket π σ p k).2 := by
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  have hnotreach : ¬ (computedDot π σ (fidelityBracket π σ p k).2 ^ 2 ≥
      p * computedMass π σ (fidelityBracket π σ p k).2) := hbr.2.2.2.2.2
  have hb0 : 0 ≤ (fidelityBracket π σ p k).2 := hbr.1.trans hbr.2.1
  by_contra hcon
  have hle : (fidelityBracket π σ p k).2 ≤ π i / σ i := le_of_not_gt hcon
  exact hnotreach
    (fidelityReaches_mono π σ p hπ (fun j => (hσ j).le) hb0 hle hmargin)

/-- The real square root of the sequentially rounded filled mass. -/
noncomputable def selectedBetaRoundedSeq (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℝ :=
  Real.sqrt (computedMassSeq b π σ γ)

/-- The rational amplitude error allowance for `2 * m` rounded operations divided by `πi`. -/
def betaRoundingErrorSeq (b : ℕ) (πi : ℚ) (m : ℕ) : ℚ :=
  (2 * m : ℚ) * (gridStep b / 2) / πi

/-- The real-valued amplitude error allowance for `2 * m` rounded operations divided by `πi`. -/
noncomputable def betaRoundingErrorSeqR (b : ℕ) (πi : ℚ) (m : ℕ) : ℝ :=
  ((2 * m : ℚ) : ℝ) * (((gridStep b : ℚ) : ℝ) / 2) / ((πi : ℚ) : ℝ)

/-- The real sequential rounding allowance equals the real cast of its rational counterpart. -/
theorem betaRoundingErrorSeqR_eq (b : ℕ) (πi : ℚ) (m : ℕ) :
    betaRoundingErrorSeqR b πi m = ((betaRoundingErrorSeq b πi m : ℚ) : ℝ) := by
  unfold betaRoundingErrorSeqR betaRoundingErrorSeq
  push_cast
  ring

/-- A positive witness mass lower bound and sufficiently small sequential mass error bound the
amplitude error by `betaRoundingErrorSeqR`. -/
theorem certifiedBeta_roundedSeq {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (γ : ℚ) (i : Fin m)
    (hpi : 0 < π i) (hmass : (π i) ^ 2 ≤ computedMass π σ γ)
    (hdmsmall : (2 * m : ℚ) * (gridStep b / 2) ≤ (π i) ^ 2 / 2) :
    |selectedBetaRoundedSeq b π σ γ - selectedBeta π σ γ| ≤ betaRoundingErrorSeqR b (π i) m := by
  have hdm : 0 ≤ (2 * m : ℚ) * (gridStep b / 2) := by
    have h1 : 0 ≤ (2 * m : ℚ) := by positivity
    have h2 : 0 ≤ gridStep b / 2 := div_nonneg (gridStep_pos b).le (by norm_num)
    exact mul_nonneg h1 h2
  have hlo : (π i) ^ 2 / 2 ≤ computedMass π σ γ := by linarith
  have herr0 : |computedMassSeq b π σ γ - computedMass π σ γ|
      ≤ (2 * m : ℚ) * (gridStep b / 2) := computedMassSeq_error b π σ γ
  have hhat : (π i) ^ 2 / 2 ≤ computedMassSeq b π σ γ := by
    obtain ⟨hneg, hpos⟩ := abs_le.mp herr0
    linarith
  have hpi2 : 0 < (π i) ^ 2 := sq_pos_of_pos hpi
  have hpi2half : 0 < (π i) ^ 2 / 2 := div_pos hpi2 (by norm_num)
  have hsqr := precisionSqrt_error (mLo := (π i) ^ 2 / 2) (dm := (2 * m : ℚ) * (gridStep b / 2))
    (mass := computedMass π σ γ) (massHat := computedMassSeq b π σ γ)
    hpi2half hdm hlo hhat herr0
  have hpiR : 0 < (π i : ℝ) := by exact_mod_cast hpi
  have hmon : Real.sqrt (((π i : ℚ) ^ 2 / 4 : ℝ))
      ≤ Real.sqrt (((π i : ℚ) ^ 2 / 2 : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hhalf : Real.sqrt (((π i : ℚ) ^ 2 / 4 : ℝ)) = (π i : ℝ) / 2 := by
    have h1 : ((π i : ℚ) ^ 2 / 4 : ℝ) = ((π i : ℝ) / 2) ^ 2 := by
      ring
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  have hden : (π i : ℝ) ≤ 2 * Real.sqrt (((π i : ℚ) ^ 2 / 2 : ℝ)) := by
    have := hmon
    rw [hhalf] at this
    linarith
  have hdmcast : (((2 * m : ℚ) * (gridStep b / 2) : ℚ) : ℝ)
      = ((2 * m : ℚ) : ℝ) * (((gridStep b : ℚ) : ℝ) / 2) := by
    push_cast
    ring
  have hcast2 : (((π i : ℚ) ^ 2 / 2 : ℚ) : ℝ) = ((π i : ℝ) ^ 2 / 2) := by
    push_cast
    ring
  rw [hdmcast, hcast2] at hsqr
  have hdmR : (0 : ℝ) ≤ ((2 * m : ℚ) : ℝ) * (((gridStep b : ℚ) : ℝ) / 2) := by
    have h1 : 0 ≤ ((2 * m : ℚ) : ℝ) := by positivity
    have h2 : 0 ≤ ((gridStep b : ℚ) : ℝ) := by exact_mod_cast (gridStep_pos b).le
    have h3 : 0 ≤ ((gridStep b : ℚ) : ℝ) / 2 := div_nonneg h2 (by norm_num)
    exact mul_nonneg h1 h3
  have hdiv1 := div_le_div_of_nonneg_left hdmR hpiR hden
  unfold betaRoundingErrorSeqR
  exact hsqr.trans hdiv1

/-- The sum of the division, mass-read, dot-read, and comparison counts in the total run ledger. -/
def runOperationCount (m k : ℕ) : ℕ :=
  (runLedger m k).divisions + (runLedger m k).massReads
    + (runLedger m k).dotReads + (runLedger m k).comparisons

/-- The total operation count equals `2 * m * m + 2 * m * k + 2 * k + 8 * m + 2`. -/
theorem runOperationCount_eq (m k : ℕ) :
    runOperationCount m k = 2 * m * m + 2 * m * k + 2 * k + 8 * m + 2 := by
  have hd : (runLedger m k).divisions = 2 * m + k := by
    rw [runLedger_counts]
  have hm : (runLedger m k).massReads = m * k + m * m + 2 * m := by
    rw [runLedger_counts]
  have hdot : (runLedger m k).dotReads = m * k + m * m + 2 * m := by
    rw [runLedger_counts]
  have hc : (runLedger m k).comparisons = k + 2 * m + 2 := by
    rw [runLedger_counts]
  unfold runOperationCount
  rw [hd, hm, hdot, hc]
  ring

/-- The total run operation count is strictly positive. -/
theorem runOperationCount_pos (m k : ℕ) : 0 < runOperationCount m k := by
  rw [runOperationCount_eq]
  omega

/-- The sequential filled-mass error is bounded by the total run operation count times half the
grid spacing. -/
theorem computedMassSeq_error_le_runOps (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) (k : ℕ) :
    |computedMassSeq b π σ γ - computedMass π σ γ|
      ≤ (runOperationCount m k : ℚ) * (gridStep b / 2) := by
  have h2m : 2 * m ≤ runOperationCount m k := by
    rw [runOperationCount_eq]
    omega
  have h := computedMassSeq_error b π σ γ
  have hnonneg : 0 ≤ (gridStep b / 2) := by
    have h1 : 0 ≤ gridStep b := (gridStep_pos b).le
    exact div_nonneg h1 (by norm_num)
  calc
    |computedMassSeq b π σ γ - computedMass π σ γ| ≤ (2 * m : ℚ) * (gridStep b / 2) := h
    _ ≤ (runOperationCount m k : ℚ) * (gridStep b / 2) := by
      have hcast : (2 : ℚ) * (m : ℚ) ≤ (runOperationCount m k : ℚ) := by
        have h1 : (2 * m : ℕ) ≤ runOperationCount m k := h2m
        exact_mod_cast h1
      exact mul_le_mul_of_nonneg_right hcast hnonneg

/-- The grid-spacing allowance for a positive operation count, combining amplitude-error and
witness-mass requirements. -/
def opBitBudget (ε p : ℚ) (πi : ℚ) (n : ℕ) : ℚ :=
  min (2 * ε * πi ^ 2 / ((n : ℚ) * p)) (πi ^ 2 / (n : ℚ))

/-- The table-size bit budget is the operation bit budget evaluated at that table size. -/
theorem bitBudget_eq_opBitBudget (ε p πi : ℚ) (m : ℕ) :
    bitBudget ε p πi m = opBitBudget ε p πi m := rfl

/-- The operation bit budget is positive when its operation count, tolerance, target, and
witness entry are positive. -/
theorem opBitBudget_pos {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε) (hp : 0 < p)
    (hπi : 0 < πi) : 0 < opBitBudget ε p πi n := by
  unfold opBitBudget
  apply lt_min
  · positivity
  · positivity

/-- Meeting the operation bit budget bounds the accumulated amplitude error allowance and keeps
the mass error allowance below half the squared witness entry. -/
theorem opBitBudget_sufficient {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε) (hp : 0 < p)
    (hπi : 0 < πi) (b : ℕ) (hb : gridStep b ≤ opBitBudget ε p πi n) :
    (n : ℚ) * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (n : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  have hbA : gridStep b ≤ 2 * ε * πi ^ 2 / ((n : ℚ) * p) :=
    le_trans hb (min_le_left _ _)
  have hbB : gridStep b ≤ πi ^ 2 / (n : ℚ) :=
    le_trans hb (min_le_right _ _)
  have hnp : 0 < ((n : ℚ) * p) := mul_pos (by exact_mod_cast hn) hp
  have h1 : (n : ℚ) * (gridStep b / 2) * p ≤ ε * πi ^ 2 := by
    have h2 : gridStep b * ((n : ℚ) * p) ≤ 2 * ε * πi ^ 2 := by
      have hb' := mul_le_mul_of_nonneg_right hbA hnp.le
      have h3 : (2 * ε * πi ^ 2 / ((n : ℚ) * p)) * ((n : ℚ) * p) = 2 * ε * πi ^ 2 := by
        field_simp [ne_of_gt hnp]
      rwa [h3] at hb'
    have h4 : (n : ℚ) * (gridStep b / 2) * p = gridStep b * ((n : ℚ) * p) / 2 := by ring
    rw [h4]
    linarith
  have h2 : (n : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
    have h4 : (n : ℚ) * (gridStep b / 2) = (n : ℚ) * gridStep b / 2 := by ring
    rw [h4]
    have h5 : (n : ℚ) * gridStep b ≤ (n : ℚ) * (πi ^ 2 / (n : ℚ)) :=
      mul_le_mul_of_nonneg_left hbB (by exact_mod_cast (Nat.zero_le n))
    have h6 : (n : ℚ) * (πi ^ 2 / (n : ℚ)) = πi ^ 2 := by field_simp
    rw [h6] at h5
    linarith
  refine ⟨?_, h2⟩
  rw [div_le_div_iff₀ hπi hp]
  linarith

/-- The least grid precision meeting the operation bit budget under the stated positivity
assumptions. -/
noncomputable def opBitBudgetSearch {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) : ℕ :=
  bitBudgetSearch (opBitBudget ε p πi n) (opBitBudget_pos hn hε hp hπi)

/-- The precision chosen by `opBitBudgetSearch` meets the operation bit budget. -/
theorem opBitBudgetSearch_spec {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) :
    gridStep (opBitBudgetSearch (hn := hn) (hε := hε) (hp := hp) (hπi := hπi))
      ≤ opBitBudget ε p πi n :=
  bitBudgetSearch_spec (opBitBudget_pos hn hε hp hπi)

/-- The operation bit budget search result is at most every precision meeting the same spacing
allowance. -/
theorem opBitBudgetSearch_le {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) {b : ℕ} (hb : gridStep b ≤ opBitBudget ε p πi n) :
    opBitBudgetSearch (hn := hn) (hε := hε) (hp := hp) (hπi := hπi) ≤ b :=
  bitBudgetSearch_le (opBitBudget_pos hn hε hp hπi) hb

/-- A precision meeting the operation bit budget exists under the stated positivity assumptions. -/
theorem exists_opBitBudgetSufficient {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) : ∃ b : ℕ, gridStep b ≤ opBitBudget ε p πi n :=
  ⟨opBitBudgetSearch (hn := hn) (hε := hε) (hp := hp) (hπi := hπi),
    opBitBudgetSearch_spec hn hε hp hπi⟩

/-- An operation bit budget bounds the sequentially rounded endpoint amplitude error and gives a
lower bound after subtracting bracket and rounding losses. -/
theorem certifiedRoundBudget_bitBudgetSeq {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m)
    (k b : ℕ) (lo : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hloβ : lo ≤ selectedBeta π σ (fidelityBracket π σ p k).1)
    (hbits : gridStep b ≤ opBitBudget ε p (π i) (runOperationCount m k)) :
    |selectedBetaRoundedSeq b π σ (fidelityBracket π σ p k).2
        - selectedBeta π σ (fidelityBracket π σ p k).2| ≤ betaRoundingErrorSeqR b (π i) m ∧
    ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ) - betaRoundingErrorSeqR b (π i) m
      ≤ selectedBetaRoundedSeq b π σ (fidelityBracket π σ p k).2 := by
  have hparts := opBitBudget_sufficient (runOperationCount_pos m k) hε hp (by exact_mod_cast hpi)
    b hbits
  have h2m : 2 * m ≤ runOperationCount m k := by
    rw [runOperationCount_eq]
    omega
  have hnonneg : 0 ≤ (gridStep b / 2) := by
    have h1 : 0 ≤ gridStep b := (gridStep_pos b).le
    exact div_nonneg h1 (by norm_num)
  have hdmle : (2 * m : ℚ) * (gridStep b / 2) ≤ (π i) ^ 2 / 2 := by
    have hcast : (2 : ℚ) * (m : ℚ) ≤ (runOperationCount m k : ℚ) := by
      have h1 : (2 * m : ℕ) ≤ runOperationCount m k := h2m
      exact_mod_cast h1
    calc
      (2 * m : ℚ) * (gridStep b / 2) ≤ (runOperationCount m k : ℚ) * (gridStep b / 2) :=
        mul_le_mul_of_nonneg_right hcast hnonneg
      _ ≤ (π i) ^ 2 / 2 := hparts.2
  have hmass := certifiedMass_at_certifiedLevel π σ p i k hπ hσ hpi hrange hmargin
  have hround := certifiedBeta_roundedSeq π σ b (fidelityBracket π σ p k).2 i hpi hmass hdmle
  have hprec := certifiedBeta_precision π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  obtain ⟨hneg, hpos⟩ := abs_le.mp hprec
  have hloR : ((lo : ℚ) : ℝ) ≤ selectedBeta π σ (fidelityBracket π σ p k).1 := by
    exact_mod_cast hloβ
  obtain ⟨hneg2, hpos2⟩ := abs_le.mp hround
  have h1 : ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ)
      ≤ selectedBeta π σ (fidelityBracket π σ p k).2 := by linarith
  have h2 : selectedBeta π σ (fidelityBracket π σ p k).2 - betaRoundingErrorSeqR b (π i) m
      ≤ selectedBetaRoundedSeq b π σ (fidelityBracket π σ p k).2 := by linarith
  exact ⟨hround, by linarith⟩

/-- Combines fidelity and endpoint-amplitude accuracy, sequential mass error, a rounded
amplitude lower bound, and round budget stability under the operation bit budget. -/
theorem frontier9 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k b : ℕ) (lo : ℚ) (t : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hloβ : lo ≤ selectedBeta π σ (fidelityBracket π σ p k).1)
    (htbudget : RoundBudget lo t)
    (hbits : gridStep b ≤ opBitBudget ε p (π i) (runOperationCount m k))
    (hmarginbudget : precisionLoss ε p (π i) ((runOperationCount m k : ℚ) * (gridStep b / 2))
                     ≤ roundBudgetMargin lo t) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε ∧
    |selectedBeta π σ (fidelityBracket π σ p k).2 - selectedBeta π σ (fidelityBracket π σ p k).1|
      ≤ ((ε * π i / p : ℚ) : ℝ) ∧
    |computedMassSeq b π σ (fidelityBracket π σ p k).2 - computedMass π σ (fidelityBracket π σ p k).2|
      ≤ ((runOperationCount m k : ℚ) * (gridStep b / 2) : ℝ) ∧
    (runOperationCount m k : ℚ) * (gridStep b / 2) / (π i) ≤ ε * π i / p ∧
    ((lo : ℚ) : ℝ) - ((ε * π i / p : ℚ) : ℝ) - betaRoundingErrorSeqR b (π i) m
      ≤ selectedBetaRoundedSeq b π σ (fidelityBracket π σ p k).2 ∧
    RoundBudget (lo - precisionLoss ε p (π i) ((runOperationCount m k : ℚ) * (gridStep b / 2))) t := by
  have hfid := certifiedFidelity_error π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  have hprec := certifiedBeta_precision π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  have hmass := computedMassSeq_error_le_runOps b π σ (fidelityBracket π σ p k).2 k
  have hparts := opBitBudget_sufficient (runOperationCount_pos m k) hε hp (by exact_mod_cast hpi)
    b hbits
  have hweakened : RoundBudget
      (lo - precisionLoss ε p (π i) ((runOperationCount m k : ℚ) * (gridStep b / 2))) t :=
    roundBudget_of_precisionLoss htbudget hmarginbudget
  have hcert := certifiedRoundBudget_bitBudgetSeq π σ p ε i k b lo hπ hσ hp hε hpi hrange
    hmargin hsteps hloβ hbits
  refine ⟨hfid, hprec, ?_, hparts.1, hcert.2, hweakened⟩
  exact_mod_cast hmass

/-- Rounds a rational downward to the dyadic grid. -/
def gridFloor (b : ℕ) (x : ℚ) : ℚ :=
  ((⌊x * (2 : ℚ) ^ b⌋ : ℤ) : ℚ) / (2 : ℚ) ^ b

/-- Downward rounding has nonnegative error strictly less than one grid spacing. -/
theorem gridFloor_error (b : ℕ) (x : ℚ) :
    0 ≤ x - gridFloor b x ∧ x - gridFloor b x < gridStep b := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  have hfl := Int.floor_le (x * (2 : ℚ) ^ b)
  have h2 : (⌊x * (2 : ℚ) ^ b⌋ : ℚ) ≤ x * (2 : ℚ) ^ b := by
    exact_mod_cast hfl
  have h3 : x * (2 : ℚ) ^ b < (⌊x * (2 : ℚ) ^ b⌋ : ℚ) + 1 := by
    have h := (Int.floor_lt (a := x * (2 : ℚ) ^ b)
      (z := ⌊x * (2 : ℚ) ^ b⌋ + 1)).mp (Int.lt_succ _)
    exact_mod_cast h
  have hd : x - gridFloor b x =
      (x * (2 : ℚ) ^ b - (⌊x * (2 : ℚ) ^ b⌋ : ℚ)) / (2 : ℚ) ^ b := by
    unfold gridFloor
    field_simp [hne]
  rw [hd]
  constructor
  · exact div_nonneg (sub_nonneg.mpr h2) (le_of_lt hpow)
  · rw [div_lt_iff₀ hpow]
    have hkey : gridStep b * (2 : ℚ) ^ b = 1 := by
      unfold gridStep
      field_simp [hne]
    linarith

/-- Downward grid rounding is monotone. -/
theorem gridFloor_mono (b : ℕ) {x y : ℚ} (h : x ≤ y) : gridFloor b x ≤ gridFloor b y := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  have hxy : x * (2 : ℚ) ^ b ≤ y * (2 : ℚ) ^ b :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h4z : ⌊x * (2 : ℚ) ^ b⌋ ≤ ⌊y * (2 : ℚ) ^ b⌋ := Int.floor_mono hxy
  have h4 : (⌊x * (2 : ℚ) ^ b⌋ : ℚ) ≤ (⌊y * (2 : ℚ) ^ b⌋ : ℚ) := by
    exact_mod_cast h4z
  unfold gridFloor
  rw [div_le_div_iff₀ hpow hpow]
  exact mul_le_mul_of_nonneg_right h4 hpow.le

/-- Every downward-rounded rational is an integer multiple of the grid spacing. -/
theorem gridFloor_onGrid (b : ℕ) (x : ℚ) :
    ∃ n : ℤ, gridFloor b x = (n : ℚ) * gridStep b := by
  refine ⟨(⌊x * (2 : ℚ) ^ b⌋ : ℤ), ?_⟩
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  unfold gridFloor gridStep
  field_simp [hne]

/-- Nearest-grid rounding fixes every integer multiple of the grid spacing. -/
theorem gridRound_gridPoint (b : ℕ) (n : ℤ) :
    gridRound b ((n : ℚ) * gridStep b) = (n : ℚ) * gridStep b := by
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  have hkey : ((n : ℚ) * gridStep b) * (2 : ℚ) ^ b = (n : ℚ) := by
    unfold gridStep
    field_simp [hne]
  have hhalf : ⌊(1 / 2 : ℚ)⌋ = 0 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · norm_num
    · norm_num
  have hfloor : ⌊(n : ℚ) + 1 / 2⌋ = n := by
    rw [Int.floor_intCast_add, hhalf]
    ring
  unfold gridRound
  rw [hkey, hfloor]
  unfold gridStep
  field_simp [hne]

/-- Downward grid rounding fixes every integer multiple of the grid spacing. -/
theorem gridFloor_gridPoint (b : ℕ) (n : ℤ) :
    gridFloor b ((n : ℚ) * gridStep b) = (n : ℚ) * gridStep b := by
  have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
  have hkey : ((n : ℚ) * gridStep b) * (2 : ℚ) ^ b = (n : ℚ) := by
    unfold gridStep
    field_simp [hne]
  have hfloor : ⌊(n : ℚ)⌋ = n := Int.floor_intCast n
  unfold gridFloor
  rw [hkey, hfloor]
  unfold gridStep
  field_simp [hne]

/-- Nearest-grid rounding is idempotent. -/
theorem gridRound_idem (b : ℕ) (x : ℚ) : gridRound b (gridRound b x) = gridRound b x := by
  obtain ⟨n, hn⟩ := gridRound_onGrid b x
  rw [hn, gridRound_gridPoint]

/-- Downward grid rounding is idempotent. -/
theorem gridFloor_idem (b : ℕ) (x : ℚ) : gridFloor b (gridFloor b x) = gridFloor b x := by
  obtain ⟨n, hn⟩ := gridFloor_onGrid b x
  rw [hn, gridFloor_gridPoint]

/-- Sequential nearest-rounded addition is exact when the accumulator and every list entry lie
on the grid. -/
theorem roundedFold_add_of_gridPoints (b : ℕ) :
    ∀ (acc : ℚ) (xs : List ℚ),
      (∃ n : ℤ, acc = (n : ℚ) * gridStep b) →
      (∀ x ∈ xs, ∃ n : ℤ, x = (n : ℚ) * gridStep b) →
      roundedFold b (fun a x => a + x) acc xs = acc + (xs.sum : ℚ) := by
  intro acc xs
  induction xs generalizing acc with
  | nil =>
      intro _ _
      simp [roundedFold]
  | cons x xs ih =>
      intro hacc h
      obtain ⟨n, hn⟩ := h x (by simp)
      obtain ⟨m, hm⟩ := hacc
      have hsum : ∃ k : ℤ, acc + x = (k : ℚ) * gridStep b := by
        refine ⟨m + n, ?_⟩
        rw [hm, hn]
        push_cast
        ring
      have hgrid : gridRound b (acc + x) = acc + x := by
        obtain ⟨k, hk⟩ := hsum
        rw [hk, gridRound_gridPoint]
      have hrest : ∀ y ∈ xs, ∃ k : ℤ, y = (k : ℚ) * gridStep b := fun y hy => h y (by simp [hy])
      simp only [roundedFold, List.sum_cons]
      rw [hgrid]
      have hrec := ih (acc + x) hsum hrest
      linarith

/-- Sequential nearest-rounded summation is exact for a list of grid points. -/
theorem gridSum_of_gridPoints (b : ℕ) (xs : List ℚ)
    (h : ∀ x ∈ xs, ∃ n : ℤ, x = (n : ℚ) * gridStep b) :
    gridSum b xs = (xs.sum : ℚ) := by
  unfold gridSum
  have h0 : ∃ n : ℤ, (0 : ℚ) = (n : ℚ) * gridStep b := ⟨0, by simp [gridStep]⟩
  have hrec := roundedFold_add_of_gridPoints b 0 xs h0 h
  simpa using! hrec

/-- Sequential summation of the rounded mass entries equals their exact sum because all entries
lie on the same grid. -/
theorem computedMassSeq_eq_computedMassRounded (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassSeq b π σ γ = computedMassRounded b π σ γ := by
  unfold computedMassSeq
  have h : gridSum b (List.ofFn fun j => gridRound b ((waterFill π σ γ j) ^ 2))
      = ∑ j, gridRound b ((waterFill π σ γ j) ^ 2) := by
    rw [← List.sum_ofFn]
    apply gridSum_of_gridPoints
    intro x hx
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
    obtain ⟨n, hn⟩ := gridRound_onGrid b ((waterFill π σ γ j) ^ 2)
    refine ⟨n, ?_⟩
    rw [← hj]
    exact hn
  rw [h]
  rfl

/-- The sequentially rounded mass has the sharper error bound of `m` times half the grid
spacing. -/
theorem computedMassSeq_error_sharp (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    |computedMassSeq b π σ γ - computedMass π σ γ| ≤ (m : ℚ) * (gridStep b / 2) := by
  rw [computedMassSeq_eq_computedMassRounded]
  exact computedMassRounded_error b π σ γ

/-- Multiplies two rationals and rounds the product downward to the dyadic grid. -/
def gridMul (b : ℕ) (x y : ℚ) : ℚ := gridFloor b (x * y)

/-- Squares a rational and rounds the square downward to the dyadic grid. -/
def gridSq (b : ℕ) (x : ℚ) : ℚ := gridFloor b (x * x)

/-- Adds two rationals and rounds the sum downward to the dyadic grid. -/
def gridAdd (b : ℕ) (x y : ℚ) : ℚ := gridFloor b (x + y)

/-- Downward-rounded multiplication underestimates the product by a nonnegative amount strictly
below one grid spacing. -/
theorem gridMul_error (b : ℕ) (x y : ℚ) :
    0 ≤ x * y - gridMul b x y ∧ x * y - gridMul b x y < gridStep b := by
  exact gridFloor_error b (x * y)

/-- Downward-rounded squaring underestimates the square by a nonnegative amount strictly below
one grid spacing. -/
theorem gridSq_error (b : ℕ) (x : ℚ) :
    0 ≤ x * x - gridSq b x ∧ x * x - gridSq b x < gridStep b := by
  exact gridFloor_error b (x * x)

/-- Downward-rounded addition underestimates the sum by a nonnegative amount strictly below one
grid spacing. -/
theorem gridAdd_error (b : ℕ) (x y : ℚ) :
    0 ≤ x + y - gridAdd b x y ∧ x + y - gridAdd b x y < gridStep b := by
  exact gridFloor_error b (x + y)

/-- Sequentially sums a rational list using downward-rounded addition from a given accumulator. -/
def gridSumDown (b : ℕ) : ℚ → List ℚ → ℚ
  | acc, [] => acc
  | acc, x :: xs => gridSumDown b (gridAdd b acc x) xs

/-- Sequential downward summation underestimates the exact accumulator-plus-sum by at most one
grid spacing per entry. -/
theorem gridSumDown_error (b : ℕ) :
    ∀ (acc : ℚ) (xs : List ℚ),
      0 ≤ acc + (xs.sum : ℚ) - gridSumDown b acc xs ∧
        acc + (xs.sum : ℚ) - gridSumDown b acc xs ≤ (xs.length : ℚ) * gridStep b := by
  intro acc xs
  induction xs generalizing acc with
  | nil =>
      simp [gridSumDown]
  | cons x xs ih =>
      have hstep := gridAdd_error b acc x
      have hrec := ih (gridAdd b acc x)
      simp only [gridSumDown, List.sum_cons]
      constructor
      · linarith
      · have h1 : ((x :: xs).length : ℚ) = (xs.length : ℚ) + 1 := by
          simp only [List.length_cons]
          push_cast
          ring
        rw [h1]
        linarith

/-- Sequential downward summation is exact when its initial accumulator and all list entries lie
on the grid. -/
theorem gridSumDown_of_gridPoints (b : ℕ) :
    ∀ (acc : ℚ) (xs : List ℚ),
      (∃ n : ℤ, acc = (n : ℚ) * gridStep b) →
      (∀ x ∈ xs, ∃ n : ℤ, x = (n : ℚ) * gridStep b) →
      gridSumDown b acc xs = acc + (xs.sum : ℚ) := by
  intro acc xs
  induction xs generalizing acc with
  | nil =>
      intro _ _
      simp [gridSumDown]
  | cons x xs ih =>
      intro hacc h
      obtain ⟨n, hn⟩ := h x (by simp)
      obtain ⟨m, hm⟩ := hacc
      have hsum : ∃ k : ℤ, acc + x = (k : ℚ) * gridStep b := by
        refine ⟨m + n, ?_⟩
        rw [hm, hn]
        push_cast
        ring
      have hgrid : gridAdd b acc x = acc + x := by
        obtain ⟨k, hk⟩ := hsum
        have hfl : gridFloor b ((k : ℚ) * gridStep b) = (k : ℚ) * gridStep b :=
          gridFloor_gridPoint b k
        calc
          gridAdd b acc x = gridFloor b (acc + x) := rfl
          _ = gridFloor b ((k : ℚ) * gridStep b) := by rw [hk]
          _ = (k : ℚ) * gridStep b := hfl
          _ = acc + x := hk.symm
      have hrest : ∀ y ∈ xs, ∃ k : ℤ, y = (k : ℚ) * gridStep b := fun y hy => h y (by simp [hy])
      simp only [gridSumDown, List.sum_cons]
      rw [hgrid]
      have hrec := ih (acc + x) hsum hrest
      linarith

/-- The filled mass computed by downward rounding each squared entry and accumulating with
downward-rounded addition. -/
def computedMassDown (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  gridSumDown b 0 (List.ofFn fun j => gridSq b (waterFill π σ γ j))

/-- The downward mass computation equals the exact sum of its downward-rounded squared entries. -/
theorem computedMassDown_eq_sum (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassDown b π σ γ = ∑ j, gridSq b (waterFill π σ γ j) := by
  unfold computedMassDown
  have hrec : gridSumDown b 0 (List.ofFn fun j => gridSq b (waterFill π σ γ j))
      = 0 + (List.ofFn fun j => gridSq b (waterFill π σ γ j)).sum := by
    apply gridSumDown_of_gridPoints
    · exact ⟨0, by simp [gridStep]⟩
    · intro x hx
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
      obtain ⟨n, hn⟩ := gridFloor_onGrid b (waterFill π σ γ j * waterFill π σ γ j)
      refine ⟨n, ?_⟩
      rw [← hj]
      show gridSq b (waterFill π σ γ j) = (n : ℚ) * gridStep b
      exact hn
  rw [List.sum_ofFn] at hrec
  simpa using! hrec

/-- The downward mass computation is at most the exact filled mass. -/
theorem computedMassDown_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassDown b π σ γ ≤ computedMass π σ γ := by
  rw [computedMassDown_eq_sum]
  unfold computedMass computedWaterEnergy
  refine Finset.sum_le_sum fun j _ => ?_
  have h := (gridSq_error b (waterFill π σ γ j)).1
  linarith

/-- The downward mass computation underestimates the exact mass by at most `m` grid spacings. -/
theorem computedMassDown_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    0 ≤ computedMass π σ γ - computedMassDown b π σ γ ∧
      computedMass π σ γ - computedMassDown b π σ γ ≤ (m : ℚ) * gridStep b := by
  have hsum : computedMass π σ γ - computedMassDown b π σ γ
      = ∑ j, ((waterFill π σ γ j) ^ 2 - gridSq b (waterFill π σ γ j)) := by
    rw [computedMassDown_eq_sum]
    unfold computedMass computedWaterEnergy
    rw [← Finset.sum_sub_distrib]
  rw [hsum]
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      by simpa only [pow_two] using! (gridSq_error b (waterFill π σ γ j)).1
  · have h1 : (∑ j, ((waterFill π σ γ j) ^ 2 - gridSq b (waterFill π σ γ j)))
        ≤ ∑ _j : Fin m, gridStep b :=
      Finset.sum_le_sum fun j _ =>
        by simpa only [pow_two] using! (gridSq_error b (waterFill π σ γ j)).2.le
    have h2 : (∑ _j : Fin m, gridStep b) = (m : ℚ) * gridStep b := by
      simp [Finset.sum_const, Finset.card_univ]
    linarith

/-- For nonnegative source and target entries, the downward mass is monotone in nonnegative
levels. -/
theorem computedMassDown_mono (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ γ' : ℚ} (hγ : 0 ≤ γ) (h : γ ≤ γ') :
    computedMassDown b π σ γ ≤ computedMassDown b π σ γ' := by
  rw [computedMassDown_eq_sum, computedMassDown_eq_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hfill : waterFill π σ γ j ≤ waterFill π σ γ' j :=
    min_le_min (le_refl _) (mul_le_mul_of_nonneg_right h (hσ j))
  have hnonneg : 0 ≤ waterFill π σ γ j := by
    rw [waterFill]
    exact le_min (hπ j) (mul_nonneg hγ (hσ j))
  have hsq : (waterFill π σ γ j) ^ 2 ≤ (waterFill π σ γ' j) ^ 2 := by
    nlinarith [sq_nonneg (waterFill π σ γ' j - waterFill π σ γ j)]
  have hfloor : gridFloor b ((waterFill π σ γ j) ^ 2)
      ≤ gridFloor b ((waterFill π σ γ' j) ^ 2) := gridFloor_mono b hsq
  simpa only [gridSq, pow_two] using! hfloor

/-- The real square root of the downward-rounded filled mass. -/
noncomputable def selectedBetaDown (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℝ :=
  Real.sqrt (computedMassDown b π σ γ)

/-- The downward-rounded amplitude is at most the exact selected amplitude. -/
theorem selectedBetaDown_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    selectedBetaDown b π σ γ ≤ selectedBeta π σ γ := by
  have hle : computedMassDown b π σ γ ≤ computedMass π σ γ := computedMassDown_le b π σ γ
  have hR : ((computedMassDown b π σ γ : ℚ) : ℝ) ≤ ((computedMass π σ γ : ℚ) : ℝ) := by
    exact_mod_cast hle
  have h1 : Real.sqrt ((computedMassDown b π σ γ : ℚ) : ℝ)
      ≤ Real.sqrt ((computedMass π σ γ : ℚ) : ℝ) := Real.sqrt_le_sqrt hR
  unfold selectedBetaDown selectedBeta
  exact h1

/-- A nonnegative rational whose square is at most the downward-rounded mass bounds the
downward-rounded amplitude from below. -/
theorem selectedBetaDown_lower (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) (lo : ℚ)
    (hlo : 0 ≤ lo) (hlo2 : lo ^ 2 ≤ computedMassDown b π σ γ) :
    lo ≤ selectedBetaDown b π σ γ := by
  have hR : ((lo ^ 2 : ℚ) : ℝ) ≤ ((computedMassDown b π σ γ : ℚ) : ℝ) := by
    exact_mod_cast hlo2
  have h1 : Real.sqrt ((lo ^ 2 : ℚ) : ℝ)
      ≤ Real.sqrt ((computedMassDown b π σ γ : ℚ) : ℝ) := Real.sqrt_le_sqrt hR
  have hsq : ((lo ^ 2 : ℚ) : ℝ) = (lo : ℝ) ^ 2 := by push_cast; ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by exact_mod_cast hlo)] at h1
  unfold selectedBetaDown
  exact h1

/-- A joint budget recording grid precision, operation count, and resampling round count. -/
structure JointBudget where
  bits : ℕ
  ops : ℕ
  rounds : ℕ
  deriving DecidableEq, Repr

/-- The stated joint budget certifies fidelity accuracy, downward mass and amplitude bounds, an
exact round-count upper bound, and operation-based error allowances. -/
theorem jointBudget_certifies {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k : ℕ)
    (lo : ℚ) (jb : JointBudget)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hops : jb.ops = runOperationCount m k)
    (hbits : gridStep jb.bits ≤ opBitBudget ε p (π i) (runOperationCount m k))
    (hlo : 0 ≤ lo)
    (hlo2 : lo ^ 2 ≤ computedMassDown jb.bits π σ (fidelityBracket π σ p k).2)
    (ht : RoundBudget lo jb.rounds)
    (hβ1 : selectedBeta π σ (fidelityBracket π σ p k).2 ≤ 1) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε ∧
    0 ≤ computedMass π σ (fidelityBracket π σ p k).2
        - computedMassDown jb.bits π σ (fidelityBracket π σ p k).2 ∧
    selectedBetaDown jb.bits π σ (fidelityBracket π σ p k).2
        ≤ selectedBeta π σ (fidelityBracket π σ p k).2 ∧
    resamplingExactRounds (selectedBeta π σ (fidelityBracket π σ p k).2) ≤ jb.rounds ∧
    (jb.ops : ℚ) * (gridStep jb.bits / 2) / (π i) ≤ ε * π i / p ∧
    (jb.ops : ℚ) * (gridStep jb.bits / 2) ≤ (π i) ^ 2 / 2 := by
  have hfid := certifiedFidelity_error π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  have hmass := certifiedMass_at_certifiedLevel π σ p i k hπ hσ hpi hrange hmargin
  have hβpos : 0 < selectedBeta π σ (fidelityBracket π σ p k).2 := by
    have h1 : 0 < computedMass π σ (fidelityBracket π σ p k).2 :=
      lt_of_lt_of_le (sq_pos_of_pos hpi) hmass
    unfold selectedBeta
    exact Real.sqrt_pos_of_pos (by exact_mod_cast h1)
  have hloβ : lo ≤ selectedBeta π σ (fidelityBracket π σ p k).2 := by
    have h1 : lo ≤ selectedBetaDown jb.bits π σ (fidelityBracket π σ p k).2 :=
      selectedBetaDown_lower jb.bits π σ (fidelityBracket π σ p k).2 lo hlo hlo2
    exact h1.trans (selectedBetaDown_le jb.bits π σ (fidelityBracket π σ p k).2)
  have hrounds : resamplingExactRounds (selectedBeta π σ (fidelityBracket π σ p k).2)
      ≤ jb.rounds := resamplingExactRounds_le_of_budget hβpos hβ1 ht hloβ
  have hparts := opBitBudget_sufficient (runOperationCount_pos m k) hε hp
    (by exact_mod_cast hpi) jb.bits hbits
  have herr : (jb.ops : ℚ) * (gridStep jb.bits / 2) / (π i) ≤ ε * π i / p := by
    rw [hops]
    exact hparts.1
  have herr2 : (jb.ops : ℚ) * (gridStep jb.bits / 2) ≤ (π i) ^ 2 / 2 := by
    rw [hops]
    exact hparts.2
  exact ⟨hfid, (computedMassDown_error jb.bits π σ (fidelityBracket π σ p k).2).1,
    selectedBetaDown_le jb.bits π σ (fidelityBracket π σ p k).2, hrounds, herr, herr2⟩

/-- Combines joint budget guarantees with equality of sequential and entrywise rounded masses
and the sharper sequential mass error bound. -/
theorem frontier10 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k : ℕ)
    (lo : ℚ) (jb : JointBudget)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hops : jb.ops = runOperationCount m k)
    (hbits : gridStep jb.bits ≤ opBitBudget ε p (π i) (runOperationCount m k))
    (hlo : 0 ≤ lo)
    (hlo2 : lo ^ 2 ≤ computedMassDown jb.bits π σ (fidelityBracket π σ p k).2)
    (ht : RoundBudget lo jb.rounds)
    (hβ1 : selectedBeta π σ (fidelityBracket π σ p k).2 ≤ 1) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε ∧
    computedMassSeq jb.bits π σ (fidelityBracket π σ p k).2
        = computedMassRounded jb.bits π σ (fidelityBracket π σ p k).2 ∧
    |computedMassSeq jb.bits π σ (fidelityBracket π σ p k).2
        - computedMass π σ (fidelityBracket π σ p k).2| ≤ (m : ℚ) * (gridStep jb.bits / 2) ∧
    0 ≤ computedMass π σ (fidelityBracket π σ p k).2
        - computedMassDown jb.bits π σ (fidelityBracket π σ p k).2 ∧
    selectedBetaDown jb.bits π σ (fidelityBracket π σ p k).2
        ≤ selectedBeta π σ (fidelityBracket π σ p k).2 ∧
    resamplingExactRounds (selectedBeta π σ (fidelityBracket π σ p k).2) ≤ jb.rounds ∧
    (jb.ops : ℚ) * (gridStep jb.bits / 2) / (π i) ≤ ε * π i / p ∧
    (jb.ops : ℚ) * (gridStep jb.bits / 2) ≤ (π i) ^ 2 / 2 := by
  obtain ⟨hfid, hmass, hβ, hrounds, herr, herr2⟩ :=
    jointBudget_certifies π σ p ε i k lo jb hπ hσ hp hε hpi hrange hmargin hsteps hops
      hbits hlo hlo2 ht hβ1
  exact ⟨hfid,
    computedMassSeq_eq_computedMassRounded jb.bits π σ (fidelityBracket π σ p k).2,
    computedMassSeq_error_sharp jb.bits π σ (fidelityBracket π σ p k).2,
    hmass, hβ, hrounds, herr, herr2⟩

/-- Downward grid rounding preserves nonnegativity. -/
theorem gridFloor_nonneg (b : ℕ) {x : ℚ} (hx : 0 ≤ x) : 0 ≤ gridFloor b x := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hx' : 0 ≤ x * (2 : ℚ) ^ b := mul_nonneg hx (by positivity)
  have hf : (0 : ℤ) ≤ ⌊x * (2 : ℚ) ^ b⌋ := (Int.floor_nonneg).2 hx'
  have hcast : (0 : ℚ) ≤ ((⌊x * (2 : ℚ) ^ b⌋ : ℤ) : ℚ) := by exact_mod_cast hf
  unfold gridFloor
  exact div_nonneg hcast (le_of_lt hpow)

/-- Nearest-grid rounding preserves nonnegativity. -/
theorem gridRound_nonneg (b : ℕ) {x : ℚ} (hx : 0 ≤ x) : 0 ≤ gridRound b x := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hx' : 0 ≤ x * (2 : ℚ) ^ b + 1 / 2 := by
    have h1 : 0 ≤ x * (2 : ℚ) ^ b := mul_nonneg hx (by positivity)
    linarith
  have hf : (0 : ℤ) ≤ ⌊x * (2 : ℚ) ^ b + 1 / 2⌋ := (Int.floor_nonneg).2 hx'
  have hcast : (0 : ℚ) ≤ ((⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℤ) : ℚ) := by exact_mod_cast hf
  unfold gridRound
  exact div_nonneg hcast (le_of_lt hpow)

/-- The downward mass is nonnegative for nonnegative source entries, target entries, and level. -/
theorem computedMassDown_nonneg (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ : ℚ} (hγ : 0 ≤ γ) :
    0 ≤ computedMassDown b π σ γ := by
  rw [computedMassDown_eq_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  have hw : 0 ≤ waterFill π σ γ j := by
    rw [waterFill]
    exact le_min (hπ j) (mul_nonneg hγ (hσ j))
  exact gridFloor_nonneg b (mul_nonneg hw hw)

/-- For nonnegative source and target entries, the exact filled mass is monotone in nonnegative
levels. -/
theorem computedMass_mono {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    {γ γ' : ℚ} (hγ : 0 ≤ γ) (h : γ ≤ γ') :
    computedMass π σ γ ≤ computedMass π σ γ' := by
  exact computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ j⟩) hγ h

/-- The target dot product computed with downward-rounded products and downward-rounded
summation. -/
def computedDotDown (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  gridSumDown b 0 (List.ofFn fun j => gridMul b (σ j) (waterFill π σ γ j))

/-- The downward dot computation equals the exact sum of its downward-rounded products. -/
theorem computedDotDown_eq_sum (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedDotDown b π σ γ = ∑ j, gridMul b (σ j) (waterFill π σ γ j) := by
  unfold computedDotDown
  have hrec : gridSumDown b 0 (List.ofFn fun j => gridMul b (σ j) (waterFill π σ γ j))
      = 0 + (List.ofFn fun j => gridMul b (σ j) (waterFill π σ γ j)).sum := by
    apply gridSumDown_of_gridPoints
    · exact ⟨0, by simp [gridStep]⟩
    · intro x hx
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
      obtain ⟨n, hn⟩ := gridFloor_onGrid b (σ j * waterFill π σ γ j)
      refine ⟨n, ?_⟩
      rw [← hj]
      show gridMul b (σ j) (waterFill π σ γ j) = (n : ℚ) * gridStep b
      exact hn
  rw [List.sum_ofFn] at hrec
  simpa using! hrec

/-- The downward dot computation is at most the exact dot product. -/
theorem computedDotDown_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedDotDown b π σ γ ≤ computedDot π σ γ := by
  rw [computedDotDown_eq_sum]
  unfold computedDot
  refine Finset.sum_le_sum fun j _ => ?_
  exact sub_nonneg.mp (gridMul_error b (σ j) (waterFill π σ γ j)).1

/-- The downward dot computation underestimates the exact dot product by at most `m` grid
spacings. -/
theorem computedDotDown_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    0 ≤ computedDot π σ γ - computedDotDown b π σ γ ∧
      computedDot π σ γ - computedDotDown b π σ γ ≤ (m : ℚ) * gridStep b := by
  have hsum : computedDot π σ γ - computedDotDown b π σ γ
      = ∑ j, (σ j * waterFill π σ γ j - gridMul b (σ j) (waterFill π σ γ j)) := by
    rw [computedDotDown_eq_sum]
    unfold computedDot
    rw [← Finset.sum_sub_distrib]
  rw [hsum]
  constructor
  · exact Finset.sum_nonneg fun j _ => (gridMul_error b (σ j) (waterFill π σ γ j)).1
  · have h1 : (∑ j, (σ j * waterFill π σ γ j - gridMul b (σ j) (waterFill π σ γ j)))
        ≤ ∑ _j : Fin m, gridStep b :=
      Finset.sum_le_sum fun j _ => (gridMul_error b (σ j) (waterFill π σ γ j)).2.le
    have h2 : (∑ _j : Fin m, gridStep b) = (m : ℚ) * gridStep b := by
      simp [Finset.sum_const, Finset.card_univ]
    linarith

/-- The downward dot computation is nonnegative for nonnegative source entries, target entries,
and level. -/
theorem computedDotDown_nonneg (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ : ℚ} (hγ : 0 ≤ γ) :
    0 ≤ computedDotDown b π σ γ := by
  rw [computedDotDown_eq_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  have hw : 0 ≤ waterFill π σ γ j := by
    rw [waterFill]
    exact le_min (hπ j) (mul_nonneg hγ (hσ j))
  exact gridFloor_nonneg b (mul_nonneg (hσ j) hw)

/-- For nonnegative target entries, the downward dot computation is monotone in the water level. -/
theorem computedDotDown_mono (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hσ : ∀ j, 0 ≤ σ j) {γ γ' : ℚ} (h : γ ≤ γ') :
    computedDotDown b π σ γ ≤ computedDotDown b π σ γ' := by
  rw [computedDotDown_eq_sum, computedDotDown_eq_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hfill : waterFill π σ γ j ≤ waterFill π σ γ' j :=
    min_le_min (le_refl _) (mul_le_mul_of_nonneg_right h (hσ j))
  have hprod : σ j * waterFill π σ γ j ≤ σ j * waterFill π σ γ' j :=
    mul_le_mul_of_nonneg_left hfill (hσ j)
  unfold gridMul
  exact gridFloor_mono b hprod

/-- The dot product obtained by nearest rounding each target-weighted water-fill entry and then
summing exactly. -/
def computedDotRounded (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  ∑ j, gridRound b (σ j * waterFill π σ γ j)

/-- The entrywise rounded dot product differs from the exact dot product by at most `m` times
half the grid spacing. -/
theorem computedDotRounded_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    |computedDotRounded b π σ γ - computedDot π σ γ| ≤ (m : ℚ) * (gridStep b / 2) := by
  have hsum : computedDotRounded b π σ γ - computedDot π σ γ
      = ∑ j, (gridRound b (σ j * waterFill π σ γ j) - σ j * waterFill π σ γ j) := by
    unfold computedDotRounded computedDot
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  have h1 : |∑ j, (gridRound b (σ j * waterFill π σ γ j) - σ j * waterFill π σ γ j)|
      ≤ ∑ j, |gridRound b (σ j * waterFill π σ γ j) - σ j * waterFill π σ γ j| :=
    Finset.abs_sum_le_sum_abs
      (fun j => gridRound b (σ j * waterFill π σ γ j) - σ j * waterFill π σ γ j)
      (Finset.univ : Finset (Fin m))
  have h2 : (∑ j, |gridRound b (σ j * waterFill π σ γ j) - σ j * waterFill π σ γ j|)
      ≤ ∑ _j : Fin m, gridStep b / 2 :=
    Finset.sum_le_sum fun j _ => gridRound_error b _
  have h3 : (∑ _j : Fin m, gridStep b / 2) = (m : ℚ) * (gridStep b / 2) := by
    simp [Finset.sum_const, Finset.card_univ]
  linarith

/-- An upper rational bound obtained by adding half a grid spacing to the nearest-rounded value. -/
def gridUpper (b : ℕ) (x : ℚ) : ℚ := gridRound b x + gridStep b / 2

/-- Every rational is at most its `gridUpper` bound. -/
theorem gridUpper_le (b : ℕ) (x : ℚ) : x ≤ gridUpper b x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (gridRound_error b x)
  unfold gridUpper
  linarith

/-- The upper grid bound exceeds its argument by at most one grid spacing. -/
theorem gridUpper_error (b : ℕ) (x : ℚ) : gridUpper b x - x ≤ gridStep b := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (gridRound_error b x)
  unfold gridUpper
  have hkey : gridStep b / 2 + gridStep b / 2 = gridStep b := by
    unfold gridStep
    ring
  linarith

/-- An upper mass estimate formed by adding the entrywise rounding error allowance to the
rounded mass. -/
def computedMassUp (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  computedMassRounded b π σ γ + (m : ℚ) * (gridStep b / 2)

/-- The upper mass estimate bounds the exact filled mass from above. -/
theorem computedMassUp_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMass π σ γ ≤ computedMassUp b π σ γ := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedMassRounded_error b π σ γ)
  unfold computedMassUp
  linarith

/-- The upper mass estimate exceeds the exact mass by at most `m` grid spacings. -/
theorem computedMassUp_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassUp b π σ γ - computedMass π σ γ ≤ (m : ℚ) * gridStep b := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedMassRounded_error b π σ γ)
  unfold computedMassUp
  have hkey : (m : ℚ) * (gridStep b / 2) + (m : ℚ) * (gridStep b / 2) = (m : ℚ) * gridStep b := by
    unfold gridStep
    ring
  linarith

/-- An upper dot-product estimate formed by adding the entrywise rounding error allowance to the
rounded dot product. -/
def computedDotUp (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  computedDotRounded b π σ γ + (m : ℚ) * (gridStep b / 2)

/-- The upper dot-product estimate bounds the exact dot product from above. -/
theorem computedDotUp_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedDot π σ γ ≤ computedDotUp b π σ γ := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedDotRounded_error b π σ γ)
  unfold computedDotUp
  linarith

/-- The upper dot-product estimate exceeds the exact dot product by at most `m` grid spacings. -/
theorem computedDotUp_error (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedDotUp b π σ γ - computedDot π σ γ ≤ (m : ℚ) * gridStep b := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedDotRounded_error b π σ γ)
  unfold computedDotUp
  have hkey : (m : ℚ) * (gridStep b / 2) + (m : ℚ) * (gridStep b / 2) = (m : ℚ) * gridStep b := by
    unfold gridStep
    ring
  linarith

/-- The upper dot-product estimate is nonnegative for nonnegative source entries, target
entries, and level. -/
theorem computedDotUp_nonneg (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ : ℚ} (hγ : 0 ≤ γ) :
    0 ≤ computedDotUp b π σ γ := by
  unfold computedDotUp
  have h1 : 0 ≤ computedDotRounded b π σ γ := by
    unfold computedDotRounded
    refine Finset.sum_nonneg fun j _ => ?_
    have hw : 0 ≤ waterFill π σ γ j := by
      rw [waterFill]
      exact le_min (hπ j) (mul_nonneg hγ (hσ j))
    exact gridRound_nonneg b (mul_nonneg (hσ j) hw)
  have h2 : 0 ≤ (m : ℚ) * (gridStep b / 2) := by
    have h3 : 0 ≤ (m : ℚ) := by exact_mod_cast Nat.zero_le m
    have h4 : 0 ≤ gridStep b / 2 := div_nonneg (gridStep_pos b).le (by norm_num)
    exact mul_nonneg h3 h4
  linarith

/-- The downward and upper mass estimates enclose the exact filled mass. -/
theorem computedMass_interval (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassDown b π σ γ ≤ computedMass π σ γ ∧
      computedMass π σ γ ≤ computedMassUp b π σ γ :=
  ⟨computedMassDown_le b π σ γ, computedMassUp_le b π σ γ⟩

/-- The downward and upper dot-product estimates enclose the exact dot product. -/
theorem computedDot_interval (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedDotDown b π σ γ ≤ computedDot π σ γ ∧
      computedDot π σ γ ≤ computedDotUp b π σ γ :=
  ⟨computedDotDown_le b π σ γ, computedDotUp_le b π σ γ⟩

/-- The nearest-rounded mass and its half-spacing error allowance give a two-sided interval for
the exact mass. -/
theorem computedMass_nearest_interval (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassRounded b π σ γ - (m : ℚ) * (gridStep b / 2) ≤ computedMass π σ γ ∧
      computedMass π σ γ ≤ computedMassRounded b π σ γ + (m : ℚ) * (gridStep b / 2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedMassRounded_error b π σ γ)
  constructor <;> linarith

/-- The nearest-rounded dot product and its half-spacing error allowance give a two-sided
interval for the exact dot product. -/
theorem computedDot_nearest_interval (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedDotRounded b π σ γ - (m : ℚ) * (gridStep b / 2) ≤ computedDot π σ γ ∧
      computedDot π σ γ ≤ computedDotRounded b π σ γ + (m : ℚ) * (gridStep b / 2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedDotRounded_error b π σ γ)
  constructor <;> linarith

/-- The mass interval centered at the nearest-rounded mass has width `m * gridStep b`. -/
theorem computedMass_interval_width (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassUp b π σ γ - (computedMassRounded b π σ γ - (m : ℚ) * (gridStep b / 2))
      = (m : ℚ) * gridStep b := by
  unfold computedMassUp
  have hkey : (m : ℚ) * (gridStep b / 2) + (m : ℚ) * (gridStep b / 2) = (m : ℚ) * gridStep b := by
    unfold gridStep
    ring
  linarith

/-- Tests whether the squared lower dot estimate is at least the target times the upper mass
estimate. -/
def intervalReaches (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : Bool :=
  decide (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ)

/-- Tests whether the squared upper dot estimate is strictly below the target times the downward
mass estimate. -/
def intervalFails (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : Bool :=
  decide (computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ)

/-- For nonnegative data, target, and level, a successful interval reach test implies
`fidelityReaches`. -/
theorem intervalReaches_sound {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : intervalReaches b π σ p γ = true) : fidelityReaches π σ p γ := by
  simp only [intervalReaches, decide_eq_true_eq] at h
  unfold fidelityReaches
  have hdown0 : 0 ≤ computedDotDown b π σ γ := computedDotDown_nonneg b π σ hπ hσ hγ
  have hdot : computedDotDown b π σ γ ≤ computedDot π σ γ := computedDotDown_le b π σ γ
  have hmass : computedMass π σ γ ≤ computedMassUp b π σ γ := computedMassUp_le b π σ γ
  have hpm : p * computedMass π σ γ ≤ p * computedMassUp b π σ γ :=
    mul_le_mul_of_nonneg_left hmass hp
  have h1 : 0 ≤ computedDot π σ γ - computedDotDown b π σ γ := by linarith
  have h2 : 0 ≤ computedDot π σ γ + computedDotDown b π σ γ := by linarith
  have h3 : (computedDot π σ γ - computedDotDown b π σ γ) *
      (computedDot π σ γ + computedDotDown b π σ γ) =
      computedDot π σ γ ^ 2 - computedDotDown b π σ γ ^ 2 := by ring
  have h4 : 0 ≤ (computedDot π σ γ - computedDotDown b π σ γ) *
      (computedDot π σ γ + computedDotDown b π σ γ) := mul_nonneg h1 h2
  have hsq : computedDotDown b π σ γ ^ 2 ≤ computedDot π σ γ ^ 2 := by nlinarith
  calc
    computedDot π σ γ ^ 2 ≥ computedDotDown b π σ γ ^ 2 := hsq
    _ ≥ p * computedMassUp b π σ γ := h
    _ ≥ p * computedMass π σ γ := hpm

/-- For nonnegative data, target, and level, a successful interval failure test implies failure
of `fidelityReaches`. -/
theorem intervalFails_sound {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : intervalFails b π σ p γ = true) : ¬ fidelityReaches π σ p γ := by
  simp only [intervalFails, decide_eq_true_eq] at h
  unfold fidelityReaches
  have hdot0 : 0 ≤ computedDot π σ γ := computedDot_nonneg π σ hπ hσ hγ
  have hup0 : 0 ≤ computedDotUp b π σ γ := computedDotUp_nonneg b π σ hπ hσ hγ
  have hdot : computedDot π σ γ ≤ computedDotUp b π σ γ := computedDotUp_le b π σ γ
  have hmass : computedMassDown b π σ γ ≤ computedMass π σ γ := computedMassDown_le b π σ γ
  have hpm : p * computedMassDown b π σ γ ≤ p * computedMass π σ γ :=
    mul_le_mul_of_nonneg_left hmass hp
  have h1 : 0 ≤ computedDotUp b π σ γ - computedDot π σ γ := by linarith
  have h2 : 0 ≤ computedDotUp b π σ γ + computedDot π σ γ := by linarith
  have h3 : (computedDotUp b π σ γ - computedDot π σ γ) *
      (computedDotUp b π σ γ + computedDot π σ γ) =
      computedDotUp b π σ γ ^ 2 - computedDot π σ γ ^ 2 := by ring
  have h4 : 0 ≤ (computedDotUp b π σ γ - computedDot π σ γ) *
      (computedDotUp b π σ γ + computedDot π σ γ) := mul_nonneg h1 h2
  have hsq : computedDot π σ γ ^ 2 ≤ computedDotUp b π σ γ ^ 2 := by nlinarith
  have hlt : computedDot π σ γ ^ 2 < p * computedMass π σ γ := by
    calc
      computedDot π σ γ ^ 2 ≤ computedDotUp b π σ γ ^ 2 := hsq
      _ < p * computedMassDown b π σ γ := h
      _ ≤ p * computedMass π σ γ := hpm
  exact not_le_of_gt hlt

/-- For nonnegative data and target, a successful interval reach test implies exact reachability
at every smaller nonnegative level. -/
theorem intervalReaches_downward {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : intervalReaches b π σ p γ = true) :
    ∀ γ' : ℚ, 0 ≤ γ' → γ' ≤ γ → fidelityReaches π σ p γ' := by
  intro γ' hγ'0 hγ'le
  have hreaches := intervalReaches_sound π σ b p γ hπ hσ hγ hp h
  exact fidelityReaches_mono π σ p hπ hσ hγ'0 hγ'le hreaches

/-- For nonnegative data, target, and level, the interval reach and failure tests cannot both
succeed. -/
theorem intervalReaches_fails_exclusive {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h1 : intervalReaches b π σ p γ = true) (h2 : intervalFails b π σ p γ = true) : False := by
  have hreach := intervalReaches_sound π σ b p γ hπ hσ hγ hp h1
  have hfail := intervalFails_sound π σ b p γ hπ hσ hγ hp h2
  exact hfail hreach

/-- The nonnegative lower mass bound obtained by subtracting the nearest-rounding error
allowance and truncating at zero. -/
def computedMassLo (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  max 0 (computedMassRounded b π σ γ - (m : ℚ) * (gridStep b / 2))

/-- The truncated lower mass estimate is at most the exact mass. -/
theorem computedMassLo_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    computedMassLo b π σ γ ≤ computedMass π σ γ := by
  unfold computedMassLo
  refine max_le_iff.mpr ⟨?_, ?_⟩
  · linarith [computedMass_nonneg π σ γ]
  · obtain ⟨hlo, hhi⟩ := abs_le.mp (computedMassRounded_error b π σ γ)
    linarith

/-- The real square root of the truncated lower mass estimate. -/
noncomputable def selectedBetaIntervalLo (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℝ :=
  Real.sqrt ((computedMassLo b π σ γ : ℚ) : ℝ)

/-- The square root of the truncated lower mass estimate bounds the selected amplitude from
below. -/
theorem selectedBetaIntervalLo_le (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    selectedBetaIntervalLo b π σ γ ≤ selectedBeta π σ γ := by
  have hle : computedMassLo b π σ γ ≤ computedMass π σ γ := computedMassLo_le b π σ γ
  have hR : ((computedMassLo b π σ γ : ℚ) : ℝ) ≤ ((computedMass π σ γ : ℚ) : ℝ) := by
    exact_mod_cast hle
  have h1 : Real.sqrt ((computedMassLo b π σ γ : ℚ) : ℝ)
      ≤ Real.sqrt ((computedMass π σ γ : ℚ) : ℝ) := Real.sqrt_le_sqrt hR
  unfold selectedBetaIntervalLo selectedBeta
  exact h1

/-- The grid-spacing allowance for interval certification, combining the amplitude tolerance
with a stricter witness-mass requirement. -/
def intervalOpBitBudget (ε p : ℚ) (πi : ℚ) (n : ℕ) : ℚ :=
  min (2 * ε * πi ^ 2 / ((n : ℚ) * p)) (πi ^ 2 / (n : ℚ) / 2)

/-- The interval operation bit budget is positive when its operation count, tolerance, target,
and witness entry are positive. -/
theorem intervalOpBitBudget_pos {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε) (hp : 0 < p)
    (hπi : 0 < πi) : 0 < intervalOpBitBudget ε p πi n := by
  unfold intervalOpBitBudget
  apply lt_min
  · have hnp : 0 < ((n : ℚ) * p) := mul_pos (by exact_mod_cast hn) hp
    have h1 : 0 < 2 * ε * πi ^ 2 := by positivity
    exact div_pos h1 hnp
  · have h1 : 0 < πi ^ 2 := sq_pos_of_pos hπi
    have hn' : 0 < (n : ℚ) := by exact_mod_cast hn
    have h2 : 0 < πi ^ 2 / (n : ℚ) := div_pos h1 hn'
    exact div_pos h2 (by norm_num)

/-- Meeting the interval operation bit budget bounds the amplitude allowance by `ε * πi / p` and
the mass allowance by `πi ^ 2 / 4`. -/
theorem intervalOpBitBudget_sufficient {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) (b : ℕ) (hb : gridStep b ≤ intervalOpBitBudget ε p πi n) :
    (n : ℚ) * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (n : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 4 := by
  have hbA : gridStep b ≤ 2 * ε * πi ^ 2 / ((n : ℚ) * p) :=
    le_trans hb (min_le_left _ _)
  have hbB : gridStep b ≤ πi ^ 2 / (n : ℚ) / 2 :=
    le_trans hb (min_le_right _ _)
  have hnp : 0 < ((n : ℚ) * p) := mul_pos (by exact_mod_cast hn) hp
  have h1 : (n : ℚ) * (gridStep b / 2) * p ≤ ε * πi ^ 2 := by
    have h2 : gridStep b * ((n : ℚ) * p) ≤ 2 * ε * πi ^ 2 := by
      have hb' := mul_le_mul_of_nonneg_right hbA hnp.le
      have h3 : (2 * ε * πi ^ 2 / ((n : ℚ) * p)) * ((n : ℚ) * p) = 2 * ε * πi ^ 2 := by
        field_simp [ne_of_gt hnp]
      rwa [h3] at hb'
    have h4 : (n : ℚ) * (gridStep b / 2) * p = gridStep b * ((n : ℚ) * p) / 2 := by ring
    rw [h4]
    linarith
  have h2 : (n : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 4 := by
    have h4 : (n : ℚ) * (gridStep b / 2) = (n : ℚ) * gridStep b / 2 := by ring
    rw [h4]
    have h5 : (n : ℚ) * gridStep b ≤ (n : ℚ) * (πi ^ 2 / (n : ℚ) / 2) :=
      mul_le_mul_of_nonneg_left hbB (by exact_mod_cast (Nat.zero_le n))
    have h6 : (n : ℚ) * (πi ^ 2 / (n : ℚ) / 2) = πi ^ 2 / 2 := by field_simp
    rw [h6] at h5
    linarith
  refine ⟨?_, h2⟩
  rw [div_le_div_iff₀ hπi hp]
  linarith

/-- Under the stated positivity assumptions, the interval operation bit budget is at least half
the operation bit budget. -/
theorem intervalOpBitBudget_half {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε) (hp : 0 < p)
    (hπi : 0 < πi) : opBitBudget ε p πi n / 2 ≤ intervalOpBitBudget ε p πi n := by
  unfold opBitBudget intervalOpBitBudget
  have hA : 0 ≤ 2 * ε * πi ^ 2 / ((n : ℚ) * p) := by
    have hnp : 0 ≤ ((n : ℚ) * p) := by
      have : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
      exact mul_nonneg this hp.le
    have hnum : 0 ≤ 2 * ε * πi ^ 2 := by positivity
    exact div_nonneg hnum hnp
  have hB : 0 ≤ πi ^ 2 / (n : ℚ) := by
    have : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
    positivity
  have hscale : min (2 * ε * πi ^ 2 / ((n : ℚ) * p)) (πi ^ 2 / (n : ℚ)) / 2
      = min ((2 * ε * πi ^ 2 / ((n : ℚ) * p)) / 2) (πi ^ 2 / (n : ℚ) / 2) := by
    by_cases h : 2 * ε * πi ^ 2 / ((n : ℚ) * p) ≤ πi ^ 2 / (n : ℚ)
    · calc
        min (2 * ε * πi ^ 2 / ((n : ℚ) * p)) (πi ^ 2 / (n : ℚ)) / 2
            = (2 * ε * πi ^ 2 / ((n : ℚ) * p)) / 2 := by rw [min_eq_left h]
        _ = min ((2 * ε * πi ^ 2 / ((n : ℚ) * p)) / 2) (πi ^ 2 / (n : ℚ) / 2) := by
            rw [min_eq_left (by linarith)]
    · have h2 : πi ^ 2 / (n : ℚ) < 2 * ε * πi ^ 2 / ((n : ℚ) * p) := lt_of_not_ge h
      calc
        min (2 * ε * πi ^ 2 / ((n : ℚ) * p)) (πi ^ 2 / (n : ℚ)) / 2
            = πi ^ 2 / (n : ℚ) / 2 := by rw [min_eq_right (le_of_lt h2)]
        _ = min ((2 * ε * πi ^ 2 / ((n : ℚ) * p)) / 2) (πi ^ 2 / (n : ℚ) / 2) := by
            rw [min_eq_right (by linarith [hB])]
  rw [hscale]
  exact min_le_min (by linarith [hA]) le_rfl

/-- One additional bit beyond a precision meeting the operation bit budget suffices to meet the
interval operation bit budget. -/
theorem intervalOpBitBudget_oneMoreBit {ε p πi : ℚ} {n : ℕ} (hn : 0 < n) (hε : 0 < ε)
    (hp : 0 < p) (hπi : 0 < πi) {b : ℕ} (hb : gridStep b ≤ opBitBudget ε p πi n) :
    gridStep (b + 1) ≤ intervalOpBitBudget ε p πi n := by
  have hhalf : opBitBudget ε p πi n / 2 ≤ intervalOpBitBudget ε p πi n :=
    intervalOpBitBudget_half hn hε hp hπi
  have hstep : gridStep (b + 1) = gridStep b / 2 := by
    unfold gridStep
    rw [pow_succ]
    field_simp
  linarith

/-- If the operation count bounds the table size and the interval bit budget holds, a witness
mass lower bound yields `computedMassLo ≥ (π i) ^ 2 / 2`. -/
theorem computedMassLo_pos_of_budget {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (γ : ℚ) (i : Fin m)
    (ε p : ℚ) (n : ℕ) (hπi : 0 < π i) (hε : 0 < ε) (hp : 0 < p) (hn : 0 < n)
    (hmn : (m : ℚ) ≤ (n : ℚ))
    (hmass : (π i) ^ 2 ≤ computedMass π σ γ)
    (hb : gridStep b ≤ intervalOpBitBudget ε p (π i) n) :
    (π i) ^ 2 / 2 ≤ computedMassLo b π σ γ := by
  obtain ⟨h1, h2⟩ := intervalOpBitBudget_sufficient hn hε hp hπi b hb
  have hstep : 0 ≤ gridStep b / 2 := div_nonneg (gridStep_pos b).le (by norm_num)
  have hmerr : (m : ℚ) * (gridStep b / 2) ≤ (π i) ^ 2 / 4 := by
    have hmn' : (m : ℚ) * (gridStep b / 2) ≤ (n : ℚ) * (gridStep b / 2) :=
      mul_le_mul_of_nonneg_right hmn hstep
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp (computedMassRounded_error b π σ γ)
  have hmassR : computedMass π σ γ - (m : ℚ) * (gridStep b / 2)
      ≤ computedMassRounded b π σ γ := by linarith
  have hmassR' : computedMassRounded b π σ γ - (m : ℚ) * (gridStep b / 2)
      ≤ computedMass π σ γ := by linarith
  have hX0 : (0 : ℚ) ≤ computedMassRounded b π σ γ - (m : ℚ) * (gridStep b / 2) := by
    linarith [hmass, hmerr, hmassR]
  unfold computedMassLo
  rw [max_eq_right hX0]
  linarith [hmassR']

/-- Collects fidelity accuracy, mass and dot enclosures, a positive lower mass bound, and an
amplitude error allowance under the interval bit budget. -/
theorem frontier11 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k b n : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hn : 0 < n) (hmn : (m : ℚ) ≤ (n : ℚ))
    (hbits : gridStep b ≤ intervalOpBitBudget ε p (π i) n) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε ∧
    computedMassDown b π σ (fidelityBracket π σ p k).2
        ≤ computedMass π σ (fidelityBracket π σ p k).2 ∧
    computedMass π σ (fidelityBracket π σ p k).2
        ≤ computedMassUp b π σ (fidelityBracket π σ p k).2 ∧
    computedDotDown b π σ (fidelityBracket π σ p k).2
        ≤ computedDot π σ (fidelityBracket π σ p k).2 ∧
    computedDot π σ (fidelityBracket π σ p k).2
        ≤ computedDotUp b π σ (fidelityBracket π σ p k).2 ∧
    (π i) ^ 2 / 2 ≤ computedMassLo b π σ (fidelityBracket π σ p k).2 ∧
    selectedBetaIntervalLo b π σ (fidelityBracket π σ p k).2
        ≤ selectedBeta π σ (fidelityBracket π σ p k).2 ∧
    (n : ℚ) * (gridStep b / 2) / (π i) ≤ ε * π i / p := by
  have hfid := certifiedFidelity_error π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  have hmass := certifiedMass_at_certifiedLevel π σ p i k hπ hσ hpi hrange hmargin
  obtain ⟨h1, h2⟩ := intervalOpBitBudget_sufficient hn hε hp hpi b hbits
  have hlo := computedMassLo_pos_of_budget π σ b (fidelityBracket π σ p k).2 i ε p n
    hpi hε hp hn hmn hmass hbits
  exact ⟨hfid,
    (computedMass_interval b π σ (fidelityBracket π σ p k).2).1,
    (computedMass_interval b π σ (fidelityBracket π σ p k).2).2,
    (computedDot_interval b π σ (fidelityBracket π σ p k).2).1,
    (computedDot_interval b π σ (fidelityBracket π σ p k).2).2,
    hlo,
    selectedBetaIntervalLo_le b π σ (fidelityBracket π σ p k).2,
    h1⟩

/-- The three outcomes of an interval fidelity test: certified reach, certified failure, or
ambiguity. -/
inductive IntervalDecision where

  | reaches : IntervalDecision

  | fails : IntervalDecision

  | ambiguous : IntervalDecision
  deriving DecidableEq, Repr

/-- Decides the interval fidelity test, prioritizing certified reach, then certified failure,
and reporting ambiguity when neither inequality holds. -/
def intervalDecision (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : IntervalDecision :=
  if computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ then IntervalDecision.reaches
  else if computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ then IntervalDecision.fails
  else IntervalDecision.ambiguous

/-- The interval reach test is true exactly when its lower-dot and upper-mass comparison holds. -/
theorem intervalReaches_eq_true {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ) :
    intervalReaches b π σ p γ = true ↔
      computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ := by
  unfold intervalReaches
  simp only [decide_eq_true_eq]

/-- The interval failure test is true exactly when its upper-dot and lower-mass comparison
holds. -/
theorem intervalFails_eq_true {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ) :
    intervalFails b π σ p γ = true ↔
      computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ := by
  unfold intervalFails
  simp only [decide_eq_true_eq]

/-- For nonnegative data, target, and level, the numerical interval reach and failure
inequalities are incompatible. -/
theorem interval_certified_exclusive {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h1 : computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ)
    (h2 : computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ) : False := by
  have hD0 : 0 ≤ computedDotDown b π σ γ := computedDotDown_nonneg b π σ hπ hσ hγ
  have hU0 : 0 ≤ computedDotUp b π σ γ := computedDotUp_nonneg b π σ hπ hσ hγ
  have hL0 : 0 ≤ computedMassDown b π σ γ := computedMassDown_nonneg b π σ hπ hσ hγ
  have hV0 : 0 ≤ computedMassUp b π σ γ := by
    have h1 := computedMassUp_le b π σ γ
    have h2 := computedMass_nonneg π σ γ
    linarith
  have hDU : computedDotDown b π σ γ ≤ computedDotUp b π σ γ := by
    have h1 := computedDotDown_le b π σ γ
    have h2 := computedDotUp_le b π σ γ
    linarith
  have hLV : computedMassDown b π σ γ ≤ computedMassUp b π σ γ := by
    have h1 := computedMassDown_le b π σ γ
    have h2 := computedMassUp_le b π σ γ
    linarith
  have hsq : computedDotDown b π σ γ ^ 2 ≤ computedDotUp b π σ γ ^ 2 := by nlinarith
  have hmul : p * computedMassDown b π σ γ ≤ p * computedMassUp b π σ γ :=
    mul_le_mul_of_nonneg_left hLV hp
  nlinarith [hsq, hmul]

/-- Characterizes all three interval decision outcomes by the two comparison inequalities and
their priority order. -/
theorem intervalDecision_spec {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ) :
    (intervalDecision b π σ p γ = .reaches ↔
        computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) ∧
    (intervalDecision b π σ p γ = .fails ↔
        ¬ (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) ∧
          computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ) ∧
    (intervalDecision b π σ p γ = .ambiguous ↔
        ¬ (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) ∧
          ¬ (computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ)) := by
  by_cases hr : computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ
  · by_cases hf : computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ
    · simp [intervalDecision, hr, hf]
    · simp [intervalDecision, hr, hf]
  · by_cases hf : computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ
    · simp [intervalDecision, hr, hf]
    · simp [intervalDecision, hr, hf]

/-- An interval decision is ambiguous exactly when both certification inequalities fail. -/
theorem intervalDecision_ambiguous_iff {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ) :
    intervalDecision b π σ p γ = .ambiguous ↔
      ¬ (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) ∧
        ¬ (computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ) :=
  (intervalDecision_spec π σ b p γ).2.2

/-- A nonambiguous interval decision rules out simultaneous failure of both certification
inequalities. -/
theorem not_ambiguous_of_decision {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (h : intervalDecision b π σ p γ ≠ .ambiguous) :
    ¬ (¬ (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) ∧
       ¬ (computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ)) := by
  intro hA
  exact h ((intervalDecision_ambiguous_iff π σ b p γ).mpr hA)

/-- The interval decision is `reaches` exactly when the Boolean interval reach test is true. -/
theorem intervalDecision_eq_reaches {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ) :
    intervalDecision b π σ p γ = .reaches ↔ intervalReaches b π σ p γ = true := by
  rw [(intervalDecision_spec π σ b p γ).1, intervalReaches_eq_true]

/-- For nonnegative data, target, and level, the interval decision is `fails` exactly when the
Boolean interval failure test is true. -/
theorem intervalDecision_eq_fails {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p) :
    intervalDecision b π σ p γ = .fails ↔ intervalFails b π σ p γ = true := by
  rw [(intervalDecision_spec π σ b p γ).2.1, intervalFails_eq_true]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro hr
    exact interval_certified_exclusive π σ b p γ hπ hσ hγ hp hr h

/-- For nonnegative data, target, and level, a `reaches` decision implies exact fidelity
reachability. -/
theorem intervalDecision_sound_reaches {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : intervalDecision b π σ p γ = .reaches) : fidelityReaches π σ p γ := by
  have hh : intervalReaches b π σ p γ = true :=
    (intervalDecision_eq_reaches π σ b p γ).mp h
  exact intervalReaches_sound π σ b p γ hπ hσ hγ hp hh

/-- For nonnegative data, target, and level, a `fails` decision implies failure of exact
fidelity reachability. -/
theorem intervalDecision_sound_fails {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : intervalDecision b π σ p γ = .fails) : ¬ fidelityReaches π σ p γ := by
  have hh : intervalFails b π σ p γ = true :=
    (intervalDecision_eq_fails π σ b p γ hπ hσ hγ hp).mp h
  exact intervalFails_sound π σ b p γ hπ hσ hγ hp hh

/-- The gap between the upper and lower interval bounds on the squared-dot-minus-target-mass
expression. -/
def intervalBandWidth (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : ℚ :=
  (computedDotUp b π σ γ ^ 2 - computedDotDown b π σ γ ^ 2) +
    p * (computedMassUp b π σ γ - computedMassDown b π σ γ)

/-- For nonnegative data, target, and level, the lower interval gap bounds the exact fidelity
comparison gap from below. -/
theorem intervalBand_lower {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p) :
    computedDotDown b π σ γ ^ 2 - p * computedMassUp b π σ γ
      ≤ computedDot π σ γ ^ 2 - p * computedMass π σ γ := by
  have hD0 : 0 ≤ computedDotDown b π σ γ := computedDotDown_nonneg b π σ hπ hσ hγ
  have hdot0 : 0 ≤ computedDot π σ γ := computedDot_nonneg π σ hπ hσ hγ
  have h1 : computedDotDown b π σ γ ≤ computedDot π σ γ := computedDotDown_le b π σ γ
  have h2 : computedMass π σ γ ≤ computedMassUp b π σ γ := computedMassUp_le b π σ γ
  have hsq : computedDotDown b π σ γ ^ 2 ≤ computedDot π σ γ ^ 2 := by nlinarith
  have hmul : p * computedMass π σ γ ≤ p * computedMassUp b π σ γ :=
    mul_le_mul_of_nonneg_left h2 hp
  linarith

/-- For nonnegative data, target, and level, the upper interval gap bounds the exact fidelity
comparison gap from above. -/
theorem intervalBand_upper {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p) :
    computedDot π σ γ ^ 2 - p * computedMass π σ γ
      ≤ computedDotUp b π σ γ ^ 2 - p * computedMassDown b π σ γ := by
  have hU0 : 0 ≤ computedDotUp b π σ γ := computedDotUp_nonneg b π σ hπ hσ hγ
  have hdot0 : 0 ≤ computedDot π σ γ := computedDot_nonneg π σ hπ hσ hγ
  have h1 : computedDot π σ γ ≤ computedDotUp b π σ γ := computedDotUp_le b π σ γ
  have h2 : computedMassDown b π σ γ ≤ computedMass π σ γ := computedMassDown_le b π σ γ
  have hsq : computedDot π σ γ ^ 2 ≤ computedDotUp b π σ γ ^ 2 := by nlinarith
  have hmul : p * computedMassDown b π σ γ ≤ p * computedMass π σ γ :=
    mul_le_mul_of_nonneg_left h2 hp
  linarith

/-- For nonnegative data, target, and level, an ambiguous decision bounds the absolute fidelity
comparison gap by `intervalBandWidth`. -/
theorem intervalDecision_ambiguous_band {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : intervalDecision b π σ p γ = .ambiguous) :
    |computedDot π σ γ ^ 2 - p * computedMass π σ γ| ≤ intervalBandWidth b π σ p γ := by
  have hspec := intervalDecision_spec π σ b p γ
  have hamb := hspec.2.2.mp h
  have hnP : ¬ (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) := hamb.1
  have hnQ : ¬ (computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ) := hamb.2
  have hP : computedDotDown b π σ γ ^ 2 < p * computedMassUp b π σ γ := lt_of_not_ge hnP
  have hQ : p * computedMassDown b π σ γ ≤ computedDotUp b π σ γ ^ 2 := le_of_not_gt hnQ
  have hlo := intervalBand_lower π σ b p γ hπ hσ hγ hp
  have hhi := intervalBand_upper π σ b p γ hπ hσ hγ hp
  have hband : 0 ≤ intervalBandWidth b π σ p γ := by
    unfold intervalBandWidth
    have hVL : computedMassDown b π σ γ ≤ computedMassUp b π σ γ := by
      have h1 := computedMassDown_le b π σ γ
      have h2 := computedMassUp_le b π σ γ
      linarith
    have hpm : 0 ≤ p * (computedMassUp b π σ γ - computedMassDown b π σ γ) := by
      have h1 := mul_nonneg hp (sub_nonneg.mpr hVL)
      linarith
    have h1 : 0 ≤ computedDotUp b π σ γ ^ 2 - computedDotDown b π σ γ ^ 2 := by
      have h2 : computedDotDown b π σ γ ≤ computedDotUp b π σ γ := by
        have h3 := computedDotDown_le b π σ γ
        have h4 := computedDotUp_le b π σ γ
        linarith
      have h3 : 0 ≤ computedDotUp b π σ γ - computedDotDown b π σ γ := by linarith
      have h4 : 0 ≤ computedDotUp b π σ γ + computedDotDown b π σ γ := by
        have h5 := computedDotDown_nonneg b π σ hπ hσ hγ
        have h6 := computedDotUp_nonneg b π σ hπ hσ hγ
        linarith
      have hkey : computedDotUp b π σ γ ^ 2 - computedDotDown b π σ γ ^ 2
          = (computedDotUp b π σ γ - computedDotDown b π σ γ)
              * (computedDotUp b π σ γ + computedDotDown b π σ γ) := by ring
      rw [hkey]
      exact mul_nonneg h3 h4
    linarith
  rw [abs_le]
  constructor
  · have h2 : p * computedMassUp b π σ γ - computedDotDown b π σ γ ^ 2
        ≤ intervalBandWidth b π σ p γ := by
      unfold intervalBandWidth
      linarith
    linarith [hlo, h2]
  · have h2 : computedDotUp b π σ γ ^ 2 - p * computedMassDown b π σ γ
        ≤ intervalBandWidth b π σ p γ := by
      unfold intervalBandWidth
      linarith
    linarith [hhi, h2]

/-- Bounds the interval band width by twice the table size times the grid spacing times the sum
of the dot estimates and target. -/
theorem intervalBandWidth_le {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p) :
    intervalBandWidth b π σ p γ
      ≤ 2 * (m : ℚ) * (gridStep b)
          * (computedDotUp b π σ γ + computedDotDown b π σ γ + p) := by
  have hU0 : 0 ≤ computedDotUp b π σ γ := computedDotUp_nonneg b π σ hπ hσ hγ
  have hD0 : 0 ≤ computedDotDown b π σ γ := computedDotDown_nonneg b π σ hπ hσ hγ
  have hUD : computedDotUp b π σ γ - computedDotDown b π σ γ
      ≤ 2 * (m : ℚ) * (gridStep b) := by
    have h1 := computedDotUp_error b π σ γ
    have h2 := (computedDotDown_error b π σ γ).2
    linarith
  have hVL : computedMassUp b π σ γ - computedMassDown b π σ γ
      ≤ 2 * (m : ℚ) * (gridStep b) := by
    have h1 := computedMassUp_error b π σ γ
    have h2 := (computedMassDown_error b π σ γ).2
    linarith
  have hsq : computedDotUp b π σ γ ^ 2 - computedDotDown b π σ γ ^ 2
      ≤ (2 * (m : ℚ) * (gridStep b))
          * (computedDotUp b π σ γ + computedDotDown b π σ γ) := by
    have hkey : computedDotUp b π σ γ ^ 2 - computedDotDown b π σ γ ^ 2
        = (computedDotUp b π σ γ - computedDotDown b π σ γ)
            * (computedDotUp b π σ γ + computedDotDown b π σ γ) := by ring
    rw [hkey]
    have hsum0 : 0 ≤ computedDotUp b π σ γ + computedDotDown b π σ γ := by linarith
    exact mul_le_mul_of_nonneg_right hUD hsum0
  have hmul : p * (computedMassUp b π σ γ - computedMassDown b π σ γ)
      ≤ p * (2 * (m : ℚ) * (gridStep b)) := mul_le_mul_of_nonneg_left hVL hp
  unfold intervalBandWidth
  linarith

/-- For nonnegative target entries, the water-filled dot product is at most the full
source-target dot product. -/
theorem computedDot_le_sum {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ j, 0 ≤ σ j) {γ : ℚ} :
    computedDot π σ γ ≤ ∑ j, π j * σ j := by
  unfold computedDot
  refine Finset.sum_le_sum fun j _ => ?_
  have hw : waterFill π σ γ j ≤ π j := by
    rw [waterFill]
    exact min_le_left _ _
  calc σ j * waterFill π σ γ j ≤ σ j * π j := mul_le_mul_of_nonneg_left hw (hσ j)
    _ = π j * σ j := by ring

/-- Bounds the interval band width using only table size, grid spacing, the full source-target
dot product, and target fidelity. -/
theorem intervalBandWidth_le_resolution {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p) :
    intervalBandWidth b π σ p γ
      ≤ 2 * (m : ℚ) * (gridStep b)
          * (2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p) := by
  have h1 := intervalBandWidth_le π σ b p γ hπ hσ hγ hp
  have hU : computedDotUp b π σ γ ≤ (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) := by
    have h2 := computedDotUp_error b π σ γ
    have h3 := computedDot_le_sum (γ := γ) π σ hσ
    linarith
  have hD : computedDotDown b π σ γ ≤ computedDot π σ γ := computedDotDown_le b π σ γ
  have h3 := computedDot_le_sum (γ := γ) π σ hσ
  have hnonneg : 0 ≤ 2 * (m : ℚ) * (gridStep b) := by
    have h1 : (0 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
    have h2 : 0 ≤ gridStep b := (gridStep_pos b).le
    exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
  have hsum : computedDotUp b π σ γ + computedDotDown b π σ γ + p
      ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_left hsum hnonneg)

/-- At positive filled mass, an ambiguous interval decision bounds the fidelity error by the
interval band width divided by that mass. -/
theorem intervalAmbiguity_fidelity_close {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (hmass : 0 < computedMass π σ γ)
    (h : intervalDecision b π σ p γ = .ambiguous) :
    |computedFidelity π σ γ - p| ≤ intervalBandWidth b π σ p γ / computedMass π σ γ := by
  have hband := intervalDecision_ambiguous_band π σ b p γ hπ hσ hγ hp h
  have hfid : computedFidelity π σ γ = computedDot π σ γ ^ 2 / computedMass π σ γ := by
    unfold computedFidelity
    rw [if_neg (ne_of_gt hmass)]
  have hsub : computedFidelity π σ γ - p
      = (computedDot π σ γ ^ 2 - p * computedMass π σ γ) / computedMass π σ γ := by
    rw [hfid]
    field_simp
  rw [hsub, abs_div, abs_of_pos hmass]
  rw [div_le_div_iff₀ hmass hmass]
  nlinarith [hband]

/-- Nearest-grid rounding is monotone. -/
theorem gridRound_mono (b : ℕ) {x y : ℚ} (h : x ≤ y) : gridRound b x ≤ gridRound b y := by
  unfold gridRound
  have hpow : 0 < (2 : ℚ) ^ b := by positivity
  have h1 : x * (2 : ℚ) ^ b + 1 / 2 ≤ y * (2 : ℚ) ^ b + 1 / 2 := by
    have h2 : x * (2 : ℚ) ^ b ≤ y * (2 : ℚ) ^ b :=
      mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  have hf : ⌊x * (2 : ℚ) ^ b + 1 / 2⌋ ≤ ⌊y * (2 : ℚ) ^ b + 1 / 2⌋ := Int.floor_le_floor h1
  have hc : ((⌊x * (2 : ℚ) ^ b + 1 / 2⌋ : ℤ) : ℚ) ≤ ((⌊y * (2 : ℚ) ^ b + 1 / 2⌋ : ℤ) : ℚ) := by
    exact_mod_cast hf
  exact div_le_div_of_nonneg_right hc hpow.le

/-- For nonnegative source and target entries, the nearest-rounded mass is monotone in
nonnegative levels. -/
theorem computedMassRounded_mono (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ γ' : ℚ} (hγ : 0 ≤ γ) (h : γ ≤ γ') :
    computedMassRounded b π σ γ ≤ computedMassRounded b π σ γ' := by
  unfold computedMassRounded
  refine Finset.sum_le_sum fun j _ => ?_
  have hfill : waterFill π σ γ j ≤ waterFill π σ γ' j :=
    min_le_min (le_refl _) (mul_le_mul_of_nonneg_right h (hσ j))
  have hnonneg : 0 ≤ waterFill π σ γ j := by
    rw [waterFill]
    exact le_min (hπ j) (mul_nonneg hγ (hσ j))
  have hsq : (waterFill π σ γ j) ^ 2 ≤ (waterFill π σ γ' j) ^ 2 := by
    nlinarith [sq_nonneg (waterFill π σ γ' j - waterFill π σ γ j)]
  exact gridRound_mono b hsq

/-- For nonnegative source and target entries, the upper mass estimate is monotone in
nonnegative levels. -/
theorem computedMassUp_mono (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ γ' : ℚ} (hγ : 0 ≤ γ) (h : γ ≤ γ') :
    computedMassUp b π σ γ ≤ computedMassUp b π σ γ' := by
  have h1 := computedMassRounded_mono b π σ hπ hσ hγ h
  have hc : (0 : ℚ) ≤ (m : ℚ) * (gridStep b / 2) := by
    have h2 : (0 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
    have h3 : 0 ≤ gridStep b / 2 := div_nonneg (gridStep_pos b).le (by norm_num)
    exact mul_nonneg h2 h3
  unfold computedMassUp
  linarith

/-- The stated dot-loss and mass-loss margin preserves an interval reach test when the level
decreases, and the downward dot estimate also decreases. -/
theorem intervalReaches_downward_of_margin {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hσ : ∀ j, 0 ≤ σ j) (hγ'γ : γ' ≤ γ)
    (hmargin : 2 * computedDotDown b π σ γ * (computedDotDown b π σ γ - computedDotDown b π σ γ')
               ≤ p * (computedMassUp b π σ γ - computedMassUp b π σ γ'))
    (h : intervalReaches b π σ p γ = true) :
    computedDotDown b π σ γ' ≤ computedDotDown b π σ γ ∧
      intervalReaches b π σ p γ' = true := by
  have hcert : computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ := by
    rw [intervalReaches_eq_true] at h
    exact h
  have hsq : computedDotDown b π σ γ' ^ 2
      ≥ computedDotDown b π σ γ ^ 2
        - 2 * computedDotDown b π σ γ * (computedDotDown b π σ γ - computedDotDown b π σ γ') := by
    have hkey : computedDotDown b π σ γ' ^ 2
        = (computedDotDown b π σ γ
            - (computedDotDown b π σ γ - computedDotDown b π σ γ')) ^ 2 := by ring
    rw [hkey]
    nlinarith [sq_nonneg (computedDotDown b π σ γ - computedDotDown b π σ γ')]
  have hfinal : computedDotDown b π σ γ' ^ 2 ≥ p * computedMassUp b π σ γ' := by
    have h4 : p * computedMassUp b π σ γ'
        = p * computedMassUp b π σ γ
            - p * (computedMassUp b π σ γ - computedMassUp b π σ γ') := by ring
    rw [h4]
    nlinarith [hsq, hcert, hmargin]
  refine ⟨computedDotDown_mono b π σ hσ hγ'γ, ?_⟩
  rw [intervalReaches_eq_true]
  exact hfinal

/-- For nonnegative target entries, the dot-product increase is at most the target squared norm
times the level increase. -/
theorem computedDot_gap_le {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ j, 0 ≤ σ j)
    {γ γ' : ℚ} (h : γ' ≤ γ) :
    computedDot π σ γ - computedDot π σ γ' ≤ (∑ j, (σ j) ^ 2) * (γ - γ') := by
  have hsum : computedDot π σ γ - computedDot π σ γ'
      = ∑ j, (σ j * waterFill π σ γ j - σ j * waterFill π σ γ' j) := by
    unfold computedDot
    rw [← Finset.sum_sub_distrib]
  rw [hsum]
  have hsum2 : (∑ j, (σ j) ^ 2) * (γ - γ')
      = ∑ j, (σ j) ^ 2 * (γ - γ') := by
    rw [Finset.sum_mul]
  rw [hsum2]
  refine Finset.sum_le_sum fun j _ => ?_
  have hgap : waterFill π σ γ j - waterFill π σ γ' j ≤ (γ - γ') * σ j := by
    have hle : γ' * σ j ≤ γ * σ j := mul_le_mul_of_nonneg_right h (hσ j)
    by_cases hc : γ' * σ j ≤ π j
    · have hmin : waterFill π σ γ' j = γ' * σ j := by
        rw [waterFill, min_eq_right hc]
      have hup : waterFill π σ γ j ≤ γ * σ j := by
        rw [waterFill]
        exact min_le_right _ _
      rw [hmin]
      linarith
    · have hc' : π j ≤ γ' * σ j := le_of_not_ge hc
      have hmin : waterFill π σ γ' j = π j := by
        rw [waterFill, min_eq_left hc']
      have hmin2 : waterFill π σ γ j = π j := by
        rw [waterFill, min_eq_left (hc'.trans hle)]
      rw [hmin, hmin2]
      have hnonneg : 0 ≤ (γ - γ') * σ j := by
        have h3 := mul_nonneg (sub_nonneg.mpr h) (hσ j)
        linarith
      linarith
  calc σ j * waterFill π σ γ j - σ j * waterFill π σ γ' j
      = σ j * (waterFill π σ γ j - waterFill π σ γ' j) := by ring
    _ ≤ σ j * ((γ - γ') * σ j) := mul_le_mul_of_nonneg_left hgap (hσ j)
    _ = (σ j) ^ 2 * (γ - γ') := by ring

/-- The stated cross-multiplied ratio condition preserves an interval reach test when the level
decreases, assuming positive mass at the original level. -/
theorem intervalReaches_downward_of_ratio {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hσ : ∀ j, 0 ≤ σ j) (hγ'γ : γ' ≤ γ)
    (hmass : 0 < computedMass π σ γ)
    (hratio : computedDotDown b π σ γ' ^ 2 * computedMassUp b π σ γ
              ≥ computedDotDown b π σ γ ^ 2 * computedMassUp b π σ γ')
    (h : intervalReaches b π σ p γ = true) :
    computedDotDown b π σ γ' ≤ computedDotDown b π σ γ ∧
      intervalReaches b π σ p γ' = true := by
  have hV0 : 0 < computedMassUp b π σ γ := by
    have h1 := computedMassUp_le b π σ γ
    linarith
  have hcert : computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ := by
    rw [intervalReaches_eq_true] at h
    exact h
  have hfinal : computedDotDown b π σ γ' ^ 2 ≥ p * computedMassUp b π σ γ' := by
    have h1 : p * computedMassUp b π σ γ' * computedMassUp b π σ γ
        ≤ computedDotDown b π σ γ ^ 2 * computedMassUp b π σ γ' := by
      have h2 : p * computedMassUp b π σ γ ≤ computedDotDown b π σ γ ^ 2 := hcert
      have h3 : 0 ≤ computedMassUp b π σ γ' := by
        have h4 := computedMassUp_le b π σ γ'
        have h5 := computedMass_nonneg π σ γ'
        linarith
      calc p * computedMassUp b π σ γ' * computedMassUp b π σ γ
          = (p * computedMassUp b π σ γ) * computedMassUp b π σ γ' := by ring
        _ ≤ computedDotDown b π σ γ ^ 2 * computedMassUp b π σ γ' :=
            mul_le_mul_of_nonneg_right h2 h3
    have h3 : p * computedMassUp b π σ γ' * computedMassUp b π σ γ
        ≤ computedDotDown b π σ γ' ^ 2 * computedMassUp b π σ γ := by
      calc p * computedMassUp b π σ γ' * computedMassUp b π σ γ
          ≤ computedDotDown b π σ γ ^ 2 * computedMassUp b π σ γ' := h1
        _ ≤ computedDotDown b π σ γ' ^ 2 * computedMassUp b π σ γ := hratio
    have h4 : p * computedMassUp b π σ γ'
        ≤ computedDotDown b π σ γ' ^ 2 * computedMassUp b π σ γ
            / computedMassUp b π σ γ := (le_div_iff₀ hV0).2 h3
    calc p * computedMassUp b π σ γ'
        ≤ computedDotDown b π σ γ' ^ 2 * computedMassUp b π σ γ
            / computedMassUp b π σ γ := h4
      _ = computedDotDown b π σ γ' ^ 2 := by field_simp
  refine ⟨computedDotDown_mono b π σ hσ hγ'γ, ?_⟩
  rw [intervalReaches_eq_true]
  exact hfinal

/-- A search ledger recording refinement steps, interval reads, exact reads, and ambiguous
decisions. -/
structure IntervalSearchLedger where
  steps : ℕ
  intervalReads : ℕ
  exactReads : ℕ
  ambiguities : ℕ
  deriving DecidableEq, Repr

/-- Refines a bracket using interval tests at its midpoint, falling back to an exact comparison
on ambiguity and recording the read costs. -/
def intervalFidelityStep {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (br : ℚ × ℚ) :
    (ℚ × ℚ) × IntervalSearchLedger :=
  match intervalDecision b π σ p ((br.1 + br.2) / 2) with
  | .reaches => (((br.1 + br.2) / 2, br.2), ⟨1, 4 * m, 0, 0⟩)
  | .fails => ((br.1, (br.1 + br.2) / 2), ⟨1, 4 * m, 0, 0⟩)
  | .ambiguous =>
      if computedDot π σ ((br.1 + br.2) / 2) ^ 2 ≥ p * computedMass π σ ((br.1 + br.2) / 2) then
        (((br.1 + br.2) / 2, br.2), ⟨1, 4 * m, 2 * m, 1⟩)
      else ((br.1, (br.1 + br.2) / 2), ⟨1, 4 * m, 2 * m, 1⟩)

/-- Iterates interval-based bracket refinement from zero and `computedWaterHigh`, accumulating
the search ledger. -/
def intervalFidelitySearch {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) :
    ℕ → (ℚ × ℚ) × IntervalSearchLedger
  | 0 => ((0, computedWaterHigh π σ), ⟨0, 0, 0, 0⟩)
  | k + 1 =>
      let r := intervalFidelitySearch b π σ p k
      let s := intervalFidelityStep b π σ p r.1
      (s.1, ⟨r.2.steps + s.2.steps, r.2.intervalReads + s.2.intervalReads,
        r.2.exactReads + s.2.exactReads, r.2.ambiguities + s.2.ambiguities⟩)

/-- One interval refinement uses exactly `2 * m` exact reads per ambiguous decision. -/
theorem intervalFidelityStep_ledger {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (br : ℚ × ℚ) :
    (intervalFidelityStep b π σ p br).2.exactReads
      = 2 * m * (intervalFidelityStep b π σ p br).2.ambiguities := by
  simp only [intervalFidelityStep]
  split
  · simp
  · simp
  · split <;> simp

/-- One interval refinement records one step and `4 * m` interval reads. -/
theorem intervalFidelityStep_reads {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (br : ℚ × ℚ) :
    (intervalFidelityStep b π σ p br).2.steps = 1 ∧
      (intervalFidelityStep b π σ p br).2.intervalReads = 4 * m := by
  simp only [intervalFidelityStep]
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- One interval refinement records one ambiguity exactly when both midpoint interval
certification inequalities fail. -/
theorem intervalFidelityStep_ambiguity {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (br : ℚ × ℚ) :
    (intervalFidelityStep b π σ p br).2.ambiguities
      = (if ¬ (computedDotDown b π σ ((br.1 + br.2) / 2)) ^ 2
                ≥ p * computedMassUp b π σ ((br.1 + br.2) / 2) ∧
             ¬ (computedDotUp b π σ ((br.1 + br.2) / 2)) ^ 2
                < p * computedMassDown b π σ ((br.1 + br.2) / 2)
           then 1 else 0) := by
  cases hdec : intervalDecision b π σ p ((br.1 + br.2) / 2) with
  | reaches =>
      simp only [intervalFidelityStep, hdec]
      rw [if_neg (not_ambiguous_of_decision π σ b p _ (by simp [hdec]))]
  | fails =>
      simp only [intervalFidelityStep, hdec]
      rw [if_neg (not_ambiguous_of_decision π σ b p _ (by simp [hdec]))]
  | ambiguous =>
      simp only [intervalFidelityStep, hdec]
      rw [if_pos ((intervalDecision_ambiguous_iff π σ b p _).mp hdec)]
      split <;> rfl

/-- For nonnegative data and target, applying the interval refinement to the exact depth-`k`
bracket gives the exact depth-`k + 1` bracket. -/
theorem intervalFidelityStep_eq {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) (k : ℕ) :
    (intervalFidelityStep b π σ p (fidelityBracket π σ p k)).1 = fidelityBracket π σ p (k+1) := by
  have hbb := fidelityBracket_bounds π σ p k hπ hσ
  have hmid0 : 0 ≤ ((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2 := by
    have h1 : 0 ≤ (fidelityBracket π σ p k).1 := hbb.1
    have h2 : 0 ≤ (fidelityBracket π σ p k).2 := hbb.2.le
    linarith
  cases hdec : intervalDecision b π σ p
      (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2) with
  | reaches =>
      have h1 : computedDot π σ
            (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2) ^ 2
          ≥ p * computedMass π σ
            (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2) :=
        intervalDecision_sound_reaches π σ b p _ hπ hσ hmid0 hp hdec
      simp only [intervalFidelityStep, hdec]
      simp only [fidelityBracket]
      rw [if_pos h1]
  | fails =>
      have h1 : ¬ (computedDot π σ
            (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2) ^ 2
          ≥ p * computedMass π σ
            (((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2)) :=
        intervalDecision_sound_fails π σ b p _ hπ hσ hmid0 hp hdec
      simp only [intervalFidelityStep, hdec]
      simp only [fidelityBracket]
      rw [if_neg h1]
  | ambiguous =>
      simp only [intervalFidelityStep, hdec]
      simp only [fidelityBracket]
      split <;> rfl

/-- For nonnegative data and target, the interval search returns the same bracket as the exact
fidelity search. -/
theorem intervalFidelitySearch_eq {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) :
    (intervalFidelitySearch b π σ p k).1 = fidelityBracket π σ p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hstep := intervalFidelityStep_eq b π σ p hπ hσ hp k
      simp only [intervalFidelitySearch]
      rw [ih, hstep]

/-- After `k` refinements, the ledger records `k` steps, `4 * m * k` interval reads, and `2 * m`
exact reads per ambiguity. -/
theorem intervalFidelitySearch_ledger {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) :
    (intervalFidelitySearch b π σ p k).2.steps = k ∧
    (intervalFidelitySearch b π σ p k).2.intervalReads = 4 * m * k ∧
    (intervalFidelitySearch b π σ p k).2.exactReads
      = 2 * m * (intervalFidelitySearch b π σ p k).2.ambiguities := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hstep := intervalFidelityStep_ledger b π σ p (intervalFidelitySearch b π σ p k).1
      have hreads := intervalFidelityStep_reads b π σ p (intervalFidelitySearch b π σ p k).1
      simp only [intervalFidelitySearch]
      constructor
      · rw [h1, hreads.1]
      · constructor
        · rw [h2, hreads.2]
          ring
        · rw [h3, hstep]
          ring

/-- For nonnegative data and target, the ambiguity count equals the sum of the ambiguity
indicators at the exact search midpoints. -/
theorem intervalFidelitySearch_ambiguities {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) :
    (intervalFidelitySearch b π σ p k).2.ambiguities
      = ∑ j ∈ Finset.range k,
          (if ¬ (computedDotDown b π σ
                    (((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2)) ^ 2
                  ≥ p * computedMassUp b π σ
                    (((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2) ∧
               ¬ (computedDotUp b π σ
                    (((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2)) ^ 2
                  < p * computedMassDown b π σ
                    (((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2)
             then 1 else 0) := by
  induction k with
  | zero =>
      simp only [intervalFidelitySearch, Finset.sum_range_zero]
  | succ k ih =>
      have hsearch := intervalFidelitySearch_eq b π σ p k hπ hσ hp
      have hstep := intervalFidelityStep_ambiguity b π σ p (intervalFidelitySearch b π σ p k).1
      simp only [intervalFidelitySearch]
      rw [ih, hstep, hsearch, Finset.sum_range_succ]

/-- A successful interval reach test within the specified bracket window and above the witness
ratio certifies fidelity error at most `ε`. -/
theorem intervalAmbiguity_certificate {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m)
    (k b : ℕ) (γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hγ0 : 0 ≤ γ)
    (hγhi : γ ≤ (fidelityBracket π σ p k).2)
    (hγlo : (fidelityBracket π σ p k).2 - computedWaterHigh π σ / (2 : ℚ) ^ k ≤ γ)
    (hγgc : π i / σ i ≤ γ)
    (hreach : intervalReaches b π σ p γ = true) :
    |computedFidelity π σ γ - p| ≤ ε := by
  have h1 : fidelityReaches π σ p γ :=
    intervalReaches_sound π σ b p γ hπ (fun j => (hσ j).le) hγ0 hp.le hreach
  exact certifiedFidelity_error_ambiguous π σ p ε i k γ hπ hσ hp hε hpi hrange hsteps
    hγhi hγlo hγgc h1

/-- A successful interval reach test one grid spacing below the upper bracket endpoint certifies
fidelity error at most `ε` under the stated depth and location bounds. -/
theorem intervalAmbiguity_reported_certificate {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ)
    (i : Fin m) (k b : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hcell : gridStep b ≤ (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1)
    (hgc : π i / σ i ≤ (fidelityBracket π σ p k).2 - gridStep b)
    (hreach : intervalReaches b π σ p ((fidelityBracket π σ p k).2 - gridStep b) = true) :
    |computedFidelity π σ ((fidelityBracket π σ p k).2 - gridStep b) - p| ≤ ε := by
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  have hwidth : (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1
      = computedWaterHigh π σ / (2 : ℚ) ^ k := hbr.2.2.2.1
  have hγ0 : 0 ≤ (fidelityBracket π σ p k).2 - gridStep b := by
    have h1 : 0 ≤ (fidelityBracket π σ p k).1 := hbr.1
    have h2 : (fidelityBracket π σ p k).1 ≤ (fidelityBracket π σ p k).2 := hbr.2.1
    linarith [hcell]
  have hγhi : (fidelityBracket π σ p k).2 - gridStep b ≤ (fidelityBracket π σ p k).2 := by
    have h1 : 0 ≤ gridStep b := (gridStep_pos b).le
    linarith
  have hγlo : (fidelityBracket π σ p k).2 - computedWaterHigh π σ / (2 : ℚ) ^ k
      ≤ (fidelityBracket π σ p k).2 - gridStep b := by
    have h1 : gridStep b ≤ computedWaterHigh π σ / (2 : ℚ) ^ k := by
      rw [← hwidth]
      exact hcell
    linarith
  exact intervalAmbiguity_certificate π σ p ε i k b _ hπ hσ hp hε hpi hrange hsteps
    hγ0 hγhi hγlo hgc hreach

/-- Combines an ambiguity-band bound at the upper endpoint with a nearby fidelity certificate
and downward propagation of its interval reach test under a margin condition. -/
theorem frontier12 {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k b : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k)
    (hcell : gridStep b ≤ (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1)
    (hgc : π i / σ i ≤ (fidelityBracket π σ p k).2 - gridStep b)
    (hreach : intervalReaches b π σ p ((fidelityBracket π σ p k).2 - gridStep b) = true)
    (hamb : intervalDecision b π σ p (fidelityBracket π σ p k).2 = .ambiguous) :
    |computedDot π σ (fidelityBracket π σ p k).2 ^ 2
        - p * computedMass π σ (fidelityBracket π σ p k).2|
      ≤ intervalBandWidth b π σ p (fidelityBracket π σ p k).2 ∧
    intervalBandWidth b π σ p (fidelityBracket π σ p k).2
      ≤ 2 * (m : ℚ) * (gridStep b)
          * (2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p) ∧
    |computedFidelity π σ ((fidelityBracket π σ p k).2 - gridStep b) - p| ≤ ε ∧
    (∀ γ'' : ℚ,
      γ'' ≤ (fidelityBracket π σ p k).2 - gridStep b →
      2 * computedDotDown b π σ ((fidelityBracket π σ p k).2 - gridStep b)
          * (computedDotDown b π σ ((fidelityBracket π σ p k).2 - gridStep b)
              - computedDotDown b π σ γ'')
        ≤ p * (computedMassUp b π σ ((fidelityBracket π σ p k).2 - gridStep b)
            - computedMassUp b π σ γ'') →
      intervalReaches b π σ p γ'' = true) := by
  have hhi0 : 0 ≤ (fidelityBracket π σ p k).2 := by
    have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
    (try dsimp only at hbr)
    exact hbr.1.trans hbr.2.1
  have hband := intervalDecision_ambiguous_band π σ b p (fidelityBracket π σ p k).2
    hπ (fun j => (hσ j).le) hhi0 hp.le hamb
  have hwidth := intervalBandWidth_le_resolution π σ b p (fidelityBracket π σ p k).2
    hπ (fun j => (hσ j).le) hhi0 hp.le
  have hcert := intervalAmbiguity_reported_certificate π σ p ε i k b hπ hσ hp hε hpi
    hrange hsteps hcell hgc hreach
  refine ⟨hband, hwidth, hcert, ?_⟩
  intro γ'' hγ'' hmargin
  exact (intervalReaches_downward_of_margin π σ b p (fun j => (hσ j).le) hγ'' hmargin
    hreach).2

/-- For nonnegative target entries, the nearest-rounded dot product is monotone in the water
level. -/
theorem computedDotRounded_mono (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hσ : ∀ j, 0 ≤ σ j) {γ γ' : ℚ} (h : γ ≤ γ') :
    computedDotRounded b π σ γ ≤ computedDotRounded b π σ γ' := by
  unfold computedDotRounded
  refine Finset.sum_le_sum fun j _ => ?_
  have hfill : waterFill π σ γ j ≤ waterFill π σ γ' j :=
    min_le_min (le_refl _) (mul_le_mul_of_nonneg_right h (hσ j))
  have hprod : σ j * waterFill π σ γ j ≤ σ j * waterFill π σ γ' j :=
    mul_le_mul_of_nonneg_left hfill (hσ j)
  exact gridRound_mono b hprod

/-- For nonnegative target entries, the upper dot-product estimate is monotone in the water
level. -/
theorem computedDotUp_mono (b : ℕ) {m : ℕ} (π σ : Fin m → ℚ)
    (hσ : ∀ j, 0 ≤ σ j) {γ γ' : ℚ} (h : γ ≤ γ') :
    computedDotUp b π σ γ ≤ computedDotUp b π σ γ' := by
  have h1 := computedDotRounded_mono b π σ hσ h
  have hc : (0 : ℚ) ≤ (m : ℚ) * (gridStep b / 2) := by
    have h2 : (0 : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.zero_le m
    have h3 : 0 ≤ gridStep b / 2 := div_nonneg (gridStep_pos b).le (by norm_num)
    exact mul_nonneg h2 h3
  unfold computedDotUp
  linarith

/-- The stated squared-dot and mass increment margin preserves an interval failure test when the
level increases and gives monotonicity of the downward mass. -/
theorem intervalFails_upward_of_margin {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (_hp : 0 ≤ p)
    (hγγ' : γ ≤ γ')
    (hmargin : computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2
               ≤ p * (computedMassDown b π σ γ' - computedMassDown b π σ γ))
    (h : intervalFails b π σ p γ = true) :
    computedMassDown b π σ γ ≤ computedMassDown b π σ γ' ∧
      intervalFails b π σ p γ' = true := by
  have hcert : computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ := by
    rw [intervalFails_eq_true] at h
    exact h
  have hsplit : computedDotUp b π σ γ' ^ 2
      = computedDotUp b π σ γ ^ 2
          + (computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2) := by ring
  have hstep : computedDotUp b π σ γ ^ 2
        + (computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2)
      ≤ computedDotUp b π σ γ ^ 2
          + p * (computedMassDown b π σ γ' - computedMassDown b π σ γ) :=
    add_le_add_right hmargin _
  have hcombine : computedDotUp b π σ γ ^ 2
        + p * (computedMassDown b π σ γ' - computedMassDown b π σ γ)
      < p * computedMassDown b π σ γ' := by
    have hkey : p * computedMassDown b π σ γ
        + p * (computedMassDown b π σ γ' - computedMassDown b π σ γ)
        = p * computedMassDown b π σ γ' := by ring
    linarith
  refine ⟨computedMassDown_mono b π σ hπ hσ hγ hγγ', ?_⟩
  rw [intervalFails_eq_true]
  rw [hsplit]
  linarith

/-- With positive downward mass, the stated cross-multiplied ratio condition preserves an
interval failure test when the level increases. -/
theorem intervalFails_upward_of_ratio {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ)
    (hγγ' : γ ≤ γ')
    (hmass : 0 < computedMassDown b π σ γ)
    (hratio : computedDotUp b π σ γ' ^ 2 * computedMassDown b π σ γ
              ≤ computedDotUp b π σ γ ^ 2 * computedMassDown b π σ γ')
    (h : intervalFails b π σ p γ = true) :
    intervalFails b π σ p γ' = true := by
  have hcert : computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ := by
    rw [intervalFails_eq_true] at h
    exact h
  have hmono : computedMassDown b π σ γ ≤ computedMassDown b π σ γ' :=
    computedMassDown_mono b π σ hπ hσ hγ hγγ'
  have hpos : 0 < computedMassDown b π σ γ' := lt_of_lt_of_le hmass hmono
  have h1 : computedDotUp b π σ γ' ^ 2
      ≤ (computedDotUp b π σ γ ^ 2 * computedMassDown b π σ γ')
          / computedMassDown b π σ γ := by
    rw [le_div_iff₀ hmass]
    exact hratio
  have h2 : (computedDotUp b π σ γ ^ 2 * computedMassDown b π σ γ')
          / computedMassDown b π σ γ
      < p * computedMassDown b π σ γ' := by
    have h3 : computedDotUp b π σ γ ^ 2 / computedMassDown b π σ γ < p :=
      (div_lt_iff₀ hmass).2 hcert
    have h4 : (computedDotUp b π σ γ ^ 2 * computedMassDown b π σ γ')
          / computedMassDown b π σ γ
        = (computedDotUp b π σ γ ^ 2 / computedMassDown b π σ γ)
            * computedMassDown b π σ γ' := by
      field_simp [ne_of_gt hmass]
    rw [h4]
    exact mul_lt_mul_of_pos_right h3 hpos
  rw [intervalFails_eq_true]
  linarith

/-- The stated downward margin condition preserves a `reaches` interval decision when the level
decreases. -/
theorem intervalDecision_reaches_downward_of_margin {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hσ : ∀ j, 0 ≤ σ j)
    (hγ'γ : γ' ≤ γ)
    (hmargin : 2 * computedDotDown b π σ γ * (computedDotDown b π σ γ - computedDotDown b π σ γ')
               ≤ p * (computedMassUp b π σ γ - computedMassUp b π σ γ'))
    (h : intervalDecision b π σ p γ = .reaches) :
    intervalDecision b π σ p γ' = .reaches := by
  have hh : intervalReaches b π σ p γ = true :=
    (intervalDecision_eq_reaches π σ b p γ).mp h
  have h2 := intervalReaches_downward_of_margin π σ b p hσ hγ'γ hmargin hh
  exact (intervalDecision_eq_reaches π σ b p γ').mpr h2.2

/-- The stated upward margin condition preserves a `fails` interval decision when the level
increases. -/
theorem intervalDecision_fails_upward_of_margin {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (hγγ' : γ ≤ γ')
    (hmargin : computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2
               ≤ p * (computedMassDown b π σ γ' - computedMassDown b π σ γ))
    (h : intervalDecision b π σ p γ = .fails) :
    intervalDecision b π σ p γ' = .fails := by
  have hγ'0 : 0 ≤ γ' := hγ.trans hγγ'
  have hh : intervalFails b π σ p γ = true :=
    (intervalDecision_eq_fails π σ b p γ hπ hσ hγ hp).mp h
  have h2 := intervalFails_upward_of_margin π σ b p hπ hσ hγ hp hγγ' hmargin hh
  exact (intervalDecision_eq_fails π σ b p γ' hπ hσ hγ'0 hp).mpr h2.2

/-- Under the upward failure-propagation margin, an ambiguous decision at the larger level
prevents a failure decision at the smaller level. -/
theorem intervalDecision_ambiguous_not_fails_below {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (hγγ' : γ ≤ γ')
    (hmargin : computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2
               ≤ p * (computedMassDown b π σ γ' - computedMassDown b π σ γ))
    (h : intervalDecision b π σ p γ' = .ambiguous) :
    intervalDecision b π σ p γ ≠ .fails := by
  intro hfail
  have h2 := intervalDecision_fails_upward_of_margin π σ b p hπ hσ hγ hp hγγ' hmargin hfail
  have hB : computedDotUp b π σ γ' ^ 2 < p * computedMassDown b π σ γ' :=
    (intervalDecision_spec π σ b p γ').2.1.mp h2 |>.2
  have hnB : ¬ (computedDotUp b π σ γ' ^ 2 < p * computedMassDown b π σ γ') :=
    (intervalDecision_ambiguous_iff π σ b p γ').mp h |>.2
  exact hnB hB

/-- Under the downward reach-propagation margin, an ambiguous decision at the smaller level
prevents a reach decision at the larger level. -/
theorem intervalDecision_ambiguous_not_reaches_above {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ γ' : ℚ} (hσ : ∀ j, 0 ≤ σ j)
    (hγγ' : γ ≤ γ')
    (hmargin : 2 * computedDotDown b π σ γ' * (computedDotDown b π σ γ' - computedDotDown b π σ γ)
               ≤ p * (computedMassUp b π σ γ' - computedMassUp b π σ γ))
    (h : intervalDecision b π σ p γ = .ambiguous) :
    intervalDecision b π σ p γ' ≠ .reaches := by
  intro hreach
  have hh : intervalReaches b π σ p γ' = true :=
    (intervalDecision_eq_reaches π σ b p γ').mp hreach
  have h2 := intervalReaches_downward_of_margin π σ b p hσ hγγ' hmargin hh
  have h3 : computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ :=
    (intervalReaches_eq_true π σ b p γ).mp h2.2
  have hnA : ¬ (computedDotDown b π σ γ ^ 2 ≥ p * computedMassUp b π σ γ) :=
    (intervalDecision_ambiguous_iff π σ b p γ).mp h |>.1
  exact hnA h3

/-- A level between two ambiguous levels is ambiguous when the stated reach and failure
propagation margins hold on the two subintervals. -/
theorem intervalDecision_ambiguous_between {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ₁ γ₂ γ₃ : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ₁) (hp : 0 ≤ p)
    (h₁₂ : γ₁ ≤ γ₂) (h₂₃ : γ₂ ≤ γ₃)
    (hm₁₂ : 2 * computedDotDown b π σ γ₂ * (computedDotDown b π σ γ₂ - computedDotDown b π σ γ₁)
             ≤ p * (computedMassUp b π σ γ₂ - computedMassUp b π σ γ₁))
    (hm₂₃ : computedDotUp b π σ γ₃ ^ 2 - computedDotUp b π σ γ₂ ^ 2
             ≤ p * (computedMassDown b π σ γ₃ - computedMassDown b π σ γ₂))
    (hamb₁ : intervalDecision b π σ p γ₁ = .ambiguous)
    (hamb₃ : intervalDecision b π σ p γ₃ = .ambiguous) :
    intervalDecision b π σ p γ₂ = .ambiguous := by
  have hγ₂0 : 0 ≤ γ₂ := hγ.trans h₁₂
  have hγ₃0 : 0 ≤ γ₃ := hγ₂0.trans h₂₃
  have hnf : intervalDecision b π σ p γ₂ ≠ .fails :=
    intervalDecision_ambiguous_not_fails_below π σ b p hπ hσ hγ₂0 hp h₂₃ hm₂₃ hamb₃
  have hnr : intervalDecision b π σ p γ₂ ≠ .reaches :=
    intervalDecision_ambiguous_not_reaches_above π σ b p hσ h₁₂ hm₁₂ hamb₁
  have hspec := intervalDecision_spec π σ b p γ₂
  have hnA : ¬ (computedDotDown b π σ γ₂ ^ 2 ≥ p * computedMassUp b π σ γ₂) := by
    intro hA
    exact hnr (hspec.1.mpr hA)
  have hnB : ¬ (computedDotUp b π σ γ₂ ^ 2 < p * computedMassDown b π σ γ₂) := by
    intro hB
    exact hnf (hspec.2.1.mpr ⟨hnA, hB⟩)
  exact (intervalDecision_ambiguous_iff π σ b p γ₂).mpr ⟨hnA, hnB⟩

/-- The exact fidelity comparison gap, equal to the squared computed dot product minus the
target times computed mass. -/
def fidelityGap {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : ℚ :=
  computedDot π σ γ ^ 2 - p * computedMass π σ γ

/-- For nonnegative target entries, the exact computed dot product is monotone in the water
level. -/
theorem computedDot_mono {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ j, 0 ≤ σ j)
    {γ γ' : ℚ} (h : γ ≤ γ') : computedDot π σ γ ≤ computedDot π σ γ' := by
  unfold computedDot
  refine Finset.sum_le_sum fun j _ => ?_
  have hfill : waterFill π σ γ j ≤ waterFill π σ γ' j :=
    min_le_min (le_refl _) (mul_le_mul_of_nonneg_right h (hσ j))
  exact mul_le_mul_of_nonneg_left hfill (hσ j)

/-- For nonnegative source and target entries, the mass increase is at most twice the full
source-target dot product times the level increase. -/
theorem computedMass_gap_le {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ j, 0 ≤ π j)
    (hσ : ∀ j, 0 ≤ σ j)
    {γ γ' : ℚ} (h : γ' ≤ γ) :
    computedMass π σ γ - computedMass π σ γ' ≤ 2 * (∑ j, π j * σ j) * (γ - γ') := by
  have hsum : computedMass π σ γ - computedMass π σ γ'
      = ∑ j, ((waterFill π σ γ j) ^ 2 - (waterFill π σ γ' j) ^ 2) := by
    unfold computedMass computedWaterEnergy
    rw [← Finset.sum_sub_distrib]
  rw [hsum]
  have hcoord : ∀ j : Fin m,
      (waterFill π σ γ j) ^ 2 - (waterFill π σ γ' j) ^ 2
        ≤ 2 * (π j * σ j) * (γ - γ') := by
    intro j
    have hgap : waterFill π σ γ j - waterFill π σ γ' j ≤ (γ - γ') * σ j := by
      by_cases hc : γ' * σ j ≤ π j
      · have hmin : waterFill π σ γ' j = γ' * σ j := by rw [waterFill, min_eq_right hc]
        have hup : waterFill π σ γ j ≤ γ * σ j := by
          rw [waterFill]
          exact min_le_right _ _
        rw [hmin]
        linarith
      · have hc' : π j ≤ γ' * σ j := le_of_not_ge hc
        have hmin : waterFill π σ γ' j = π j := by rw [waterFill, min_eq_left hc']
        have hmin2 : waterFill π σ γ j = π j := by
          rw [waterFill, min_eq_left (hc'.trans (mul_le_mul_of_nonneg_right h (hσ j)))]
        rw [hmin, hmin2]
        have hnonneg : 0 ≤ (γ - γ') * σ j := mul_nonneg (sub_nonneg.mpr h) (hσ j)
        linarith
    have hmono : waterFill π σ γ' j ≤ waterFill π σ γ j := by
      rw [waterFill, waterFill]
      exact min_le_min (le_refl _) (mul_le_mul_of_nonneg_right h (hσ j))
    have hnonneg1 : 0 ≤ waterFill π σ γ j - waterFill π σ γ' j := sub_nonneg.mpr hmono
    have hbound : waterFill π σ γ j + waterFill π σ γ' j ≤ 2 * π j := by
      have h1 : waterFill π σ γ j ≤ π j := by rw [waterFill]; exact min_le_left _ _
      have h2 : waterFill π σ γ' j ≤ π j := by rw [waterFill]; exact min_le_left _ _
      linarith
    have hkey : (waterFill π σ γ j) ^ 2 - (waterFill π σ γ' j) ^ 2
        = (waterFill π σ γ j - waterFill π σ γ' j)
            * (waterFill π σ γ j + waterFill π σ γ' j) := by ring
    rw [hkey]
    have hA : 0 ≤ ((γ - γ') * σ j) * (2 * π j) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr h) (hσ j)) (mul_nonneg (by norm_num) (hπ j))
    by_cases hxy : 0 ≤ waterFill π σ γ j + waterFill π σ γ' j
    · have h1 : (waterFill π σ γ j - waterFill π σ γ' j)
            * (waterFill π σ γ j + waterFill π σ γ' j)
        ≤ ((γ - γ') * σ j) * (waterFill π σ γ j + waterFill π σ γ' j) :=
        mul_le_mul_of_nonneg_right hgap hxy
      have h2 : ((γ - γ') * σ j) * (waterFill π σ γ j + waterFill π σ γ' j)
          ≤ ((γ - γ') * σ j) * (2 * π j) :=
        mul_le_mul_of_nonneg_left hbound (mul_nonneg (sub_nonneg.mpr h) (hσ j))
      have h3 : ((γ - γ') * σ j) * (2 * π j) = 2 * (π j * σ j) * (γ - γ') := by ring
      linarith
    · have hneg : (waterFill π σ γ j - waterFill π σ γ' j)
            * (waterFill π σ γ j + waterFill π σ γ' j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnonneg1 (le_of_not_ge hxy)
      have h3 : 2 * (π j * σ j) * (γ - γ') = ((γ - γ') * σ j) * (2 * π j) := by ring
      linarith
  have hsum2 : ∑ j, 2 * (π j * σ j) * (γ - γ')
      = 2 * (∑ j, π j * σ j) * (γ - γ') := by
    calc ∑ j, 2 * (π j * σ j) * (γ - γ')
        = ∑ j, (γ - γ') * (2 * (π j * σ j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = (γ - γ') * ∑ j, 2 * (π j * σ j) := by rw [Finset.mul_sum]
      _ = (γ - γ') * (2 * ∑ j, π j * σ j) := by
        have h1 : (γ - γ') * (2 * ∑ j, π j * σ j)
            = (γ - γ') * ∑ j, 2 * (π j * σ j) := by rw [Finset.mul_sum]
        rw [h1]
      _ = 2 * (∑ j, π j * σ j) * (γ - γ') := by ring
  calc (∑ j, ((waterFill π σ γ j) ^ 2 - (waterFill π σ γ' j) ^ 2))
      ≤ ∑ j, 2 * (π j * σ j) * (γ - γ') := Finset.sum_le_sum fun j _ => hcoord j
    _ = 2 * (∑ j, π j * σ j) * (γ - γ') := hsum2

/-- The rational constant `2 * (∑ j, π j * σ j) * (p + ∑ j, (σ j) ^ 2)` used to bound variation
of the fidelity gap. -/
def fidelityGapLipschitz {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) : ℚ :=
  2 * (∑ j, π j * σ j) * (p + ∑ j, (σ j) ^ 2)

/-- For nonnegative data and target, the fidelity gap is Lipschitz on nonnegative levels with
constant `fidelityGapLipschitz`. -/
theorem fidelityGap_lipschitz {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    {γ γ' : ℚ} (hγ : 0 ≤ γ) (hγ' : 0 ≤ γ') :
    |fidelityGap π σ p γ - fidelityGap π σ p γ'|
      ≤ fidelityGapLipschitz π σ p * |γ - γ'| := by
  have hL0 : 0 ≤ fidelityGapLipschitz π σ p := by
    unfold fidelityGapLipschitz
    have h1 : 0 ≤ (∑ j, π j * σ j) := Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
    have h2 : 0 ≤ ∑ j, (σ j) ^ 2 := Finset.sum_nonneg fun j _ => by positivity
    have h3 : 0 ≤ p + ∑ j, (σ j) ^ 2 := by linarith
    positivity
  have hdotsum : ∀ {a b : ℚ}, 0 ≤ a → 0 ≤ b →
      computedDot π σ a + computedDot π σ b ≤ 2 * (∑ j, π j * σ j) := by
    intro a b ha hb
    have h1 := computedDot_le_sum (γ := a) π σ hσ
    have h2 := computedDot_le_sum (γ := b) π σ hσ
    linarith
  have hcore : ∀ {a b : ℚ}, 0 ≤ a → 0 ≤ b → a ≤ b →
      -(fidelityGapLipschitz π σ p * (b - a))
        ≤ fidelityGap π σ p b - fidelityGap π σ p a ∧
      fidelityGap π σ p b - fidelityGap π σ p a
        ≤ fidelityGapLipschitz π σ p * (b - a) := by
    intro a b ha hb hab
    have hdotmono : computedDot π σ a ≤ computedDot π σ b := computedDot_mono π σ hσ hab
    have hdotgap : computedDot π σ b - computedDot π σ a
        ≤ (∑ j, (σ j) ^ 2) * (b - a) :=
      computedDot_gap_le π σ hσ (γ := b) (γ' := a) hab
    have hdotbound : computedDot π σ b + computedDot π σ a ≤ 2 * (∑ j, π j * σ j) :=
      hdotsum (by linarith) ha
    have hdotnonneg : 0 ≤ computedDot π σ b + computedDot π σ a := by
      have h1 := computedDot_nonneg π σ hπ hσ hb
      have h2 := computedDot_nonneg π σ hπ hσ ha
      linarith
    have hsq : computedDot π σ b ^ 2 - computedDot π σ a ^ 2
        ≤ 2 * (∑ j, (σ j) ^ 2) * (∑ j, π j * σ j) * (b - a) := by
      have hkey : computedDot π σ b ^ 2 - computedDot π σ a ^ 2
          = (computedDot π σ b - computedDot π σ a)
              * (computedDot π σ b + computedDot π σ a) := by ring
      rw [hkey]
      have h1 : (computedDot π σ b - computedDot π σ a)
              * (computedDot π σ b + computedDot π σ a)
          ≤ (∑ j, (σ j) ^ 2) * (b - a) * (computedDot π σ b + computedDot π σ a) :=
        mul_le_mul_of_nonneg_right hdotgap hdotnonneg
      have h2 : (∑ j, (σ j) ^ 2) * (b - a) * (computedDot π σ b + computedDot π σ a)
          ≤ (∑ j, (σ j) ^ 2) * (b - a) * (2 * (∑ j, π j * σ j)) :=
        mul_le_mul_of_nonneg_left hdotbound
          (mul_nonneg (Finset.sum_nonneg fun j _ => by positivity) (sub_nonneg.mpr hab))
      have h3 : (∑ j, (σ j) ^ 2) * (b - a) * (2 * (∑ j, π j * σ j))
          = 2 * (∑ j, (σ j) ^ 2) * (∑ j, π j * σ j) * (b - a) := by ring
      linarith
    have hmassmono : computedMass π σ a ≤ computedMass π σ b :=
      computedMass_mono π σ hπ hσ ha hab
    have hmassgap : computedMass π σ b - computedMass π σ a
        ≤ 2 * (∑ j, π j * σ j) * (b - a) :=
      computedMass_gap_le π σ hπ hσ (γ := b) (γ' := a) hab
    constructor
    · have hnonneg : 0 ≤ p * (computedMass π σ b - computedMass π σ a) :=
        mul_nonneg hp (sub_nonneg.mpr hmassmono)
      have h1 : 0 ≤ computedDot π σ b ^ 2 - computedDot π σ a ^ 2 := by
        have hkey : computedDot π σ b ^ 2 - computedDot π σ a ^ 2
            = (computedDot π σ b - computedDot π σ a)
                * (computedDot π σ b + computedDot π σ a) := by ring
        rw [hkey]
        exact mul_nonneg (sub_nonneg.mpr hdotmono) hdotnonneg
      unfold fidelityGap
      have h2 : -(fidelityGapLipschitz π σ p * (b - a))
          ≤ -2 * p * (∑ j, π j * σ j) * (b - a) := by
        unfold fidelityGapLipschitz
        have h3 : 0 ≤ (∑ j, (σ j) ^ 2) * (b - a) :=
          mul_nonneg (Finset.sum_nonneg fun j _ => by positivity) (sub_nonneg.mpr hab)
        nlinarith
      have h4 : -2 * p * (∑ j, π j * σ j) * (b - a)
          ≤ computedDot π σ b ^ 2 - computedDot π σ a ^ 2
              - p * (computedMass π σ b - computedMass π σ a) := by
        nlinarith
      linarith
    · unfold fidelityGap
      have h1 : computedDot π σ b ^ 2 - computedDot π σ a ^ 2
          ≤ 2 * (∑ j, (σ j) ^ 2) * (∑ j, π j * σ j) * (b - a) := hsq
      have h2 : 0 ≤ p * (computedMass π σ b - computedMass π σ a) :=
        mul_nonneg hp (sub_nonneg.mpr hmassmono)
      have h3 : fidelityGapLipschitz π σ p * (b - a)
          = 2 * (∑ j, π j * σ j) * (p + ∑ j, (σ j) ^ 2) * (b - a) := by
        unfold fidelityGapLipschitz
        ring
      have h4 : 2 * (∑ j, (σ j) ^ 2) * (∑ j, π j * σ j) * (b - a)
          ≤ 2 * (∑ j, π j * σ j) * (p + ∑ j, (σ j) ^ 2) * (b - a) := by
        have h5 : 0 ≤ 2 * (∑ j, π j * σ j) * (b - a) :=
          mul_nonneg (mul_nonneg (by norm_num)
            (Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j))) (sub_nonneg.mpr hab)
        have h6 : (∑ j, (σ j) ^ 2) ≤ p + ∑ j, (σ j) ^ 2 := by linarith
        nlinarith
      linarith
  by_cases h : γ ≤ γ'
  · obtain ⟨hlo, hhi⟩ := hcore (a := γ) (b := γ') hγ hγ' h
    have habs : |γ - γ'| = γ' - γ := by
      have hneg : γ - γ' = -(γ' - γ) := by ring
      rw [hneg, abs_neg, abs_of_nonneg (sub_nonneg.mpr h)]
    rw [abs_le, habs]
    constructor
    · linarith
    · linarith
  · obtain ⟨hlo, hhi⟩ := hcore (a := γ') (b := γ) hγ' hγ (le_of_not_ge h)
    have habs : |γ - γ'| = γ - γ' := abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))
    rw [abs_le, habs]
    constructor
    · linarith
    · linarith

/-- A level-independent bound on the ambiguity band in terms of grid spacing, table size,
source-target dot product, and target fidelity. -/
def ambiguityBandBound {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) : ℚ :=
  2 * (m : ℚ) * (gridStep b) * (2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p)

/-- For nonnegative data, target, and level, an ambiguous interval decision bounds the absolute
fidelity gap by `ambiguityBandBound`. -/
theorem intervalAmbiguity_gap_le {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (hamb : intervalDecision b π σ p γ = .ambiguous) :
    |fidelityGap π σ p γ| ≤ ambiguityBandBound π σ b p := by
  have hband := intervalDecision_ambiguous_band π σ b p γ hπ hσ hγ hp hamb
  have hwidth := intervalBandWidth_le_resolution π σ b p γ hπ hσ hγ hp
  unfold fidelityGap ambiguityBandBound
  linarith

/-- The fidelity gaps at two nonnegative ambiguous levels differ by at most twice the ambiguity
band bound. -/
theorem intervalAmbiguity_gap_pair {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    {γ₁ γ₂ : ℚ} (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hamb₁ : intervalDecision b π σ p γ₁ = .ambiguous)
    (hamb₂ : intervalDecision b π σ p γ₂ = .ambiguous) :
    |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂| ≤ 2 * ambiguityBandBound π σ b p := by
  have hg₁ := intervalAmbiguity_gap_le π σ b p hπ hσ hγ₁ hp hamb₁
  have hg₂ := intervalAmbiguity_gap_le π σ b p hπ hσ hγ₂ hp hamb₂
  have hsum1 : |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂|
      ≤ |fidelityGap π σ p γ₁| + |fidelityGap π σ p γ₂| := by
    have hkey : fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂
        = fidelityGap π σ p γ₁ + -(fidelityGap π σ p γ₂) := by ring
    rw [hkey]
    simpa only [abs_neg] using!
      abs_add_le (fidelityGap π σ p γ₁) (-(fidelityGap π σ p γ₂))
  linarith

/-- The interval search operation count obtained by adding interval-read overhead and
ambiguity-dependent exact-read costs to the base run count. -/
def intervalRunOperationCount (m k amb : ℕ) : ℕ :=
  runOperationCount m k + 2 * m * k + 2 * m * amb

/-- Expands the interval run operation count as a polynomial in table size, refinement depth,
and ambiguity count. -/
theorem intervalRunOperationCount_eq (m k amb : ℕ) :
    intervalRunOperationCount m k amb
      = 2 * m * m + 4 * m * k + 2 * m * amb + 2 * k + 8 * m + 2 := by
  rw [intervalRunOperationCount, runOperationCount_eq]
  ring

/-- The interval run operation count is strictly positive. -/
theorem intervalRunOperationCount_pos (m k amb : ℕ) :
    0 < intervalRunOperationCount m k amb := by
  have h : (0 : ℕ) < runOperationCount m k := runOperationCount_pos m k
  unfold intervalRunOperationCount
  omega

/-- The interval run operation count is at least the base run operation count. -/
theorem intervalRunOperationCount_ge (m k amb : ℕ) :
    runOperationCount m k ≤ intervalRunOperationCount m k amb := by
  unfold intervalRunOperationCount
  rw [Nat.add_assoc]
  exact Nat.le_add_right _ _

/-- The operation bit budget evaluated at the interval run operation count, including the
specified ambiguity count. -/
def intervalSearchOpBitBudget (ε p πi : ℚ) (m k amb : ℕ) : ℚ :=
  opBitBudget ε p πi (intervalRunOperationCount m k amb)

/-- Meeting the interval search bit budget controls the accumulated amplitude and mass error
allowances for its operation count. -/
theorem intervalSearchOpBitBudget_sufficient {ε p πi : ℚ} {m k amb : ℕ}
    (hε : 0 < ε) (hp : 0 < p) (hπi : 0 < πi) (b : ℕ)
    (hb : gridStep b ≤ intervalSearchOpBitBudget ε p πi m k amb) :
    (intervalRunOperationCount m k amb : ℚ) * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (intervalRunOperationCount m k amb : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  have hn : 0 < intervalRunOperationCount m k amb := intervalRunOperationCount_pos m k amb
  exact opBitBudget_sufficient hn hε hp hπi b hb

/-- A bit budget using the search's actual ambiguity count controls its accumulated amplitude
and mass error allowances. -/
theorem intervalSearch_budget {m : ℕ} (π σ : Fin m → ℚ) (p ε πi : ℚ) (b : ℕ)
    (hε : 0 < ε) (hp : 0 < p) (hπi : 0 < πi) (k : ℕ)
    (hb : gridStep b
        ≤ intervalSearchOpBitBudget ε p πi m k (intervalFidelitySearch b π σ p k).2.ambiguities) :
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  exact intervalSearchOpBitBudget_sufficient hε hp hπi b hb

/-- Collects conditional propagation of interval decisions, ambiguity between endpoints, gap
bounds, and accumulated precision bounds using the actual ambiguity count. -/
theorem frontier13 {m : ℕ} (π σ : Fin m → ℚ) (p ε πi : ℚ) (b k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 < p) (hε : 0 < ε) (hπi : 0 < πi)
    (γ₁ γ₂ γ₃ : ℚ)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hγ₃ : 0 ≤ γ₃)
    (h₁₂ : γ₁ ≤ γ₂) (h₂₃ : γ₂ ≤ γ₃)
    (hm₁₂ : 2 * computedDotDown b π σ γ₂ * (computedDotDown b π σ γ₂ - computedDotDown b π σ γ₁)
             ≤ p * (computedMassUp b π σ γ₂ - computedMassUp b π σ γ₁))
    (hm₂₃ : computedDotUp b π σ γ₃ ^ 2 - computedDotUp b π σ γ₂ ^ 2
             ≤ p * (computedMassDown b π σ γ₃ - computedMassDown b π σ γ₂))
    (hamb₁ : intervalDecision b π σ p γ₁ = .ambiguous)
    (hamb₃ : intervalDecision b π σ p γ₃ = .ambiguous)
    (hbudget : gridStep b ≤ intervalSearchOpBitBudget ε p πi m k
                 (intervalFidelitySearch b π σ p k).2.ambiguities) :
    (∀ γ γ' : ℚ, 0 ≤ γ' → γ' ≤ γ →
       2 * computedDotDown b π σ γ * (computedDotDown b π σ γ - computedDotDown b π σ γ')
         ≤ p * (computedMassUp b π σ γ - computedMassUp b π σ γ') →
       intervalDecision b π σ p γ = .reaches →
       intervalDecision b π σ p γ' = .reaches) ∧
    (∀ γ γ' : ℚ, 0 ≤ γ → γ ≤ γ' →
       computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2
         ≤ p * (computedMassDown b π σ γ' - computedMassDown b π σ γ) →
       intervalDecision b π σ p γ = .fails →
       intervalDecision b π σ p γ' = .fails) ∧
    intervalDecision b π σ p γ₂ = .ambiguous ∧
    (∀ γ : ℚ, 0 ≤ γ → intervalDecision b π σ p γ = .ambiguous →
       |fidelityGap π σ p γ| ≤ ambiguityBandBound π σ b p) ∧
    |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂|
      ≤ fidelityGapLipschitz π σ p * |γ₁ - γ₂| ∧
    |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₃| ≤ 2 * ambiguityBandBound π σ b p ∧
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  have hdown : ∀ γ γ' : ℚ, 0 ≤ γ' → γ' ≤ γ →
       2 * computedDotDown b π σ γ * (computedDotDown b π σ γ - computedDotDown b π σ γ')
         ≤ p * (computedMassUp b π σ γ - computedMassUp b π σ γ') →
       intervalDecision b π σ p γ = .reaches →
       intervalDecision b π σ p γ' = .reaches := by
    intro γ γ' hγ' hγ'γ hmargin h
    exact intervalDecision_reaches_downward_of_margin π σ b p hσ hγ'γ hmargin h
  have hup : ∀ γ γ' : ℚ, 0 ≤ γ → γ ≤ γ' →
       computedDotUp b π σ γ' ^ 2 - computedDotUp b π σ γ ^ 2
         ≤ p * (computedMassDown b π σ γ' - computedMassDown b π σ γ) →
       intervalDecision b π σ p γ = .fails →
       intervalDecision b π σ p γ' = .fails := by
    intro γ γ' hγ hγγ' hmargin h
    exact intervalDecision_fails_upward_of_margin π σ b p hπ hσ hγ hp.le hγγ' hmargin h
  have hamb₂ := intervalDecision_ambiguous_between π σ b p hπ hσ hγ₁ hp.le h₁₂ h₂₃
    hm₁₂ hm₂₃ hamb₁ hamb₃
  have hband : ∀ γ : ℚ, 0 ≤ γ → intervalDecision b π σ p γ = .ambiguous →
      |fidelityGap π σ p γ| ≤ ambiguityBandBound π σ b p := by
    intro γ hγ hγamb
    exact intervalAmbiguity_gap_le π σ b p hπ hσ hγ hp.le hγamb
  have hlip := fidelityGap_lipschitz π σ p hπ hσ hp.le hγ₁ hγ₂
  have hpair := intervalAmbiguity_gap_pair π σ b p hπ hσ hp.le hγ₁ hγ₃ hamb₁ hamb₃
  have hbud := intervalSearch_budget π σ p ε πi b hε hp hπi k hbudget
  exact ⟨hdown, hup, hamb₂, hband, hlip, hpair, hbud.1, hbud.2⟩

/-- The condition that the scaled target entry does not exceed the source entry at any positive
source index. -/
def onPlateau {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : Prop :=
  ∀ j, 0 < π j → γ * σ j ≤ π j

/-- For nonnegative source entries, level zero satisfies the plateau condition. -/
theorem onPlateau_zero {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ j, 0 ≤ π j) :
    onPlateau π σ 0 := by
  intro j _
  simpa using! hπ j

instance onPlateauDecidable {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    Decidable (onPlateau π σ γ) := by
  unfold onPlateau
  infer_instance

/-- For nonnegative target entries, the plateau condition persists when the level decreases. -/
theorem onPlateau_mono {m : ℕ} (π σ : Fin m → ℚ) {γ γ' : ℚ} (hσ : ∀ j, 0 ≤ σ j)
    (h : γ' ≤ γ) (hp : onPlateau π σ γ) : onPlateau π σ γ' := by
  intro j hj
  exact le_trans (mul_le_mul_of_nonneg_right h (hσ j)) (hp j hj)

/-- On the nonnegative plateau, the filled mass equals `γ ^ 2 * computedPmax π σ` under the
stated nonnegativity assumptions. -/
theorem computedMass_plateau {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (h : onPlateau π σ γ) :
    computedMass π σ γ = γ ^ 2 * computedPmax π σ := by
  unfold computedMass computedWaterEnergy
  have hstep : ∀ j : Fin m,
      (waterFill π σ γ j) ^ 2 = (if 0 < π j then (γ * σ j) ^ 2 else 0) := by
    intro j
    by_cases hj : 0 < π j
    · rw [if_pos hj, waterFill, min_eq_right (h j hj)]
    · rw [if_neg hj]
      have hπ0 : π j = 0 := le_antisymm (not_lt.mp hj) (hπ j)
      rw [waterFill, hπ0, min_eq_left (mul_nonneg hγ (hσ j))]
      ring
  have hstep2 : ∀ j : Fin m,
      (if 0 < π j then (γ * σ j) ^ 2 else 0)
        = γ ^ 2 * (if 0 < π j then σ j ^ 2 else 0) := by
    intro j
    by_cases hj : 0 < π j
    · rw [if_pos hj, if_pos hj]
      ring
    · rw [if_neg hj, if_neg hj]
      ring
  rw [Finset.sum_congr rfl (fun j _ => hstep j),
    Finset.sum_congr rfl (fun j _ => hstep2 j)]
  rw [← Finset.mul_sum]
  rfl

/-- On the nonnegative plateau, the filled dot product equals `γ * computedPmax π σ` under the
stated nonnegativity assumptions. -/
theorem computedDot_plateau {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (h : onPlateau π σ γ) :
    computedDot π σ γ = γ * computedPmax π σ := by
  unfold computedDot
  have hstep : ∀ j : Fin m,
      σ j * waterFill π σ γ j = (if 0 < π j then σ j * (γ * σ j) else 0) := by
    intro j
    by_cases hj : 0 < π j
    · rw [if_pos hj, waterFill, min_eq_right (h j hj)]
    · rw [if_neg hj]
      have hπ0 : π j = 0 := le_antisymm (not_lt.mp hj) (hπ j)
      rw [waterFill, hπ0, min_eq_left (mul_nonneg hγ (hσ j))]
      ring
  have hstep2 : ∀ j : Fin m,
      (if 0 < π j then σ j * (γ * σ j) else 0)
        = γ * (if 0 < π j then σ j ^ 2 else 0) := by
    intro j
    by_cases hj : 0 < π j
    · rw [if_pos hj, if_pos hj]
      ring
    · rw [if_neg hj, if_neg hj]
      ring
  rw [Finset.sum_congr rfl (fun j _ => hstep j),
    Finset.sum_congr rfl (fun j _ => hstep2 j)]
  rw [← Finset.mul_sum]
  rfl

/-- At a positive plateau level with positive `computedPmax`, the computed fidelity equals
`computedPmax`. -/
theorem computedFidelity_plateau {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 < γ) (h : onPlateau π σ γ)
    (hmax : 0 < computedPmax π σ) :
    computedFidelity π σ γ = computedPmax π σ := by
  have hmass := computedMass_plateau π σ hπ hσ hγ.le h
  have hdot := computedDot_plateau π σ hπ hσ hγ.le h
  have hpos : 0 < γ ^ 2 * computedPmax π σ := mul_pos (sq_pos_of_pos hγ) hmax
  unfold computedFidelity
  rw [hmass, if_neg (ne_of_gt hpos), hdot]
  have hne : γ ^ 2 * computedPmax π σ ≠ 0 := ne_of_gt hpos
  rw [div_eq_iff hne]
  ring

/-- On the nonnegative plateau, the fidelity gap equals `γ ^ 2 * (computedPmax π σ *
(computedPmax π σ - p))`. -/
theorem fidelityGap_plateau {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (h : onPlateau π σ γ) :
    fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by
  have hmass := computedMass_plateau π σ hπ hσ hγ h
  have hdot := computedDot_plateau π σ hπ hσ hγ h
  unfold fidelityGap
  rw [hmass, hdot]
  ring

/-- When the target equals `computedPmax`, the fidelity gap vanishes on the nonnegative plateau. -/
theorem fidelityGap_plateau_zero {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (h : onPlateau π σ γ)
    (hp : p = computedPmax π σ) : fidelityGap π σ p γ = 0 := by
  have hg := fidelityGap_plateau π σ p hπ hσ hγ h
  rw [hp] at hg
  rw [hp, hg]
  ring

/-- When the target equals `computedPmax`, the interval failure test is false on the nonnegative
plateau. -/
theorem intervalFails_plateau_false {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (h : onPlateau π σ γ)
    (hp : p = computedPmax π σ) : intervalFails b π σ p γ = false := by
  have hgap := fidelityGap_plateau_zero π σ p hπ hσ hγ h hp
  have hD0 : 0 ≤ computedDotUp b π σ γ := computedDotUp_nonneg b π σ hπ hσ hγ
  have hdot0 : 0 ≤ computedDot π σ γ := computedDot_nonneg π σ hπ hσ hγ
  have hdot : computedDot π σ γ ≤ computedDotUp b π σ γ := computedDotUp_le b π σ γ
  have hmass : computedMassDown b π σ γ ≤ computedMass π σ γ :=
    computedMassDown_le b π σ γ
  have hp0 : 0 ≤ p := by rw [hp]; unfold computedPmax; positivity
  have hsq : computedDot π σ γ ^ 2 ≤ computedDotUp b π σ γ ^ 2 := by nlinarith
  have hmul : p * computedMassDown b π σ γ ≤ p * computedMass π σ γ :=
    mul_le_mul_of_nonneg_left hmass hp0
  have hnot : ¬ (computedDotUp b π σ γ ^ 2 < p * computedMassDown b π σ γ) := by
    unfold fidelityGap at hgap
    nlinarith
  unfold intervalFails
  exact decide_eq_false hnot

/-- Every nonnegative plateau level satisfies `fidelityReaches` when the target is at most
`computedPmax`, under the stated nonnegativity assumptions. -/
theorem fidelityReaches_plateau {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (h : onPlateau π σ γ)
    (hp : p ≤ computedPmax π σ) : fidelityReaches π σ p γ := by
  have hg := fidelityGap_plateau π σ p hπ hσ hγ h
  have hP0 : 0 ≤ computedPmax π σ := by unfold computedPmax; positivity
  have hgap0 : 0 ≤ computedDot π σ γ ^ 2 - p * computedMass π σ γ := by
    have h1 : 0 ≤ γ ^ 2 := sq_nonneg γ
    have h3 : 0 ≤ computedPmax π σ - p := sub_nonneg.mpr hp
    have h4 : 0 ≤ γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) :=
      mul_nonneg h1 (mul_nonneg hP0 h3)
    unfold fidelityGap at hg
    rw [hg]
    exact h4
  unfold fidelityReaches
  linarith

/-- The minimum of the high water endpoint and all source-target ratios on the positive source
support. -/
def firstBreakpoint {m : ℕ} (π σ : Fin m → ℚ) : ℚ :=
  (sourceSupport π).fold min (computedWaterHigh π σ) (fun j => π j / σ j)

/-- A finite minimum fold is at most the value at each member of its indexing set. -/
private theorem fold_min_le {α : Type} [DecidableEq α] (init : ℚ) (f : α → ℚ) :
    ∀ (s : Finset α) (a : α), a ∈ s → s.fold min init f ≤ f a := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro a ha; simp at ha
  | @insert a s ha ih =>
      intro b hb
      rw [Finset.fold_insert ha]
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih b hb)

/-- A common lower bound for the initial value and all indexed values bounds their finite
minimum fold from below. -/
private theorem le_fold_min {α : Type} [DecidableEq α] (init : ℚ) (f : α → ℚ) :
    ∀ (s : Finset α) (x : ℚ), x ≤ init → (∀ a ∈ s, x ≤ f a) → x ≤ s.fold min init f := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro x hinit hx
      simpa using! hinit
  | @insert a s ha ih =>
      intro x hinit hx
      rw [Finset.fold_insert ha, le_min_iff]
      exact ⟨hx a (Finset.mem_insert_self a s),
        ih x hinit fun b hb => hx b (Finset.mem_insert_of_mem hb)⟩

/-- Membership in `sourceSupport` implies strict positivity of the corresponding source entry. -/
theorem sourceSupport_pos {m : ℕ} (π : Fin m → ℚ) {j : Fin m} (hj : j ∈ sourceSupport π) :
    0 < π j := by
  classical
  exact (Finset.mem_filter.mp hj).2

/-- The first breakpoint is at most every source-target ratio with a positive source entry. -/
theorem firstBreakpoint_le {m : ℕ} (π σ : Fin m → ℚ) {j : Fin m} (hj : 0 < π j) :
    firstBreakpoint π σ ≤ π j / σ j := by
  unfold firstBreakpoint
  exact fold_min_le _ _ _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

/-- For nonnegative source entries, positive target entries, and nonempty source support, the
plateau condition holds exactly below the first breakpoint. -/
theorem onPlateau_iff_le {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ j, 0 ≤ π j)
    (hσ : ∀ j, 0 < σ j) (hsupp : (sourceSupport π).Nonempty) (γ : ℚ) :
    onPlateau π σ γ ↔ γ ≤ firstBreakpoint π σ := by
  classical
  constructor
  · intro hγ
    have hhigh : γ ≤ computedWaterHigh π σ := by
      obtain ⟨j, hj⟩ := hsupp
      have hjσ : 0 < σ j := hσ j
      have h1 : γ * σ j ≤ π j := hγ j (sourceSupport_pos π hj)
      have h2 : γ ≤ π j / σ j := (le_div_iff₀ hjσ).2 h1
      have h3 : π j / σ j ≤ ∑ i, π i / σ i :=
        Finset.single_le_sum (fun i _ => div_nonneg (hπ i) (hσ i).le)
          (Finset.mem_univ j)
      unfold computedWaterHigh
      linarith
    refine le_fold_min _ _ _ γ hhigh ?_
    intro a ha
    have hjσ : 0 < σ a := hσ a
    have h1 : γ * σ a ≤ π a := hγ a (sourceSupport_pos π ha)
    exact (le_div_iff₀ hjσ).2 h1
  · intro hγ j hj
    have hjσ : 0 < σ j := hσ j
    have h1 : firstBreakpoint π σ ≤ π j / σ j := firstBreakpoint_le π σ hj
    have h2 : γ ≤ firstBreakpoint π σ := hγ
    have h3 : γ ≤ π j / σ j := le_trans h2 h1
    exact (le_div_iff₀ hjσ).1 h3

/-- The midpoint of the fidelity bracket at a given refinement depth. -/
def bracketMidpoint {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : ℚ :=
  ((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2

/-- One refinement increases the lower endpoint and decreases the upper endpoint of an ordered
fidelity bracket. -/
theorem fidelityBracket_sub {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (j : ℕ)
    (hle : (fidelityBracket π σ p j).1 ≤ (fidelityBracket π σ p j).2) :
    (fidelityBracket π σ p (j + 1)).1 ≥ (fidelityBracket π σ p j).1 ∧
    (fidelityBracket π σ p (j + 1)).2 ≤ (fidelityBracket π σ p j).2 := by
  dsimp only [fidelityBracket]
  split_ifs with h
  · constructor <;> linarith
  · constructor <;> linarith

/-- For nonnegative source and target entries, every fidelity bracket is ordered. -/
theorem fidelityBracket_ordered {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (j : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) :
    (fidelityBracket π σ p j).1 ≤ (fidelityBracket π σ p j).2 := by
  induction j with
  | zero =>
      have h := computedWaterHigh_pos π σ hπ hσ
      simp only [fidelityBracket]
      linarith
  | succ j ih =>
      dsimp only [fidelityBracket]
      split_ifs with h
      · linarith
      · linarith

/-- For nonnegative source and target entries, later fidelity brackets are contained in earlier
ones. -/
theorem fidelityBracket_nested {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {i j : ℕ} (hij : i ≤ j)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) :
    (fidelityBracket π σ p j).1 ≥ (fidelityBracket π σ p i).1 ∧
    (fidelityBracket π σ p j).2 ≤ (fidelityBracket π σ p i).2 := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ j hj ih =>
      have hsub := fidelityBracket_sub π σ p j (fidelityBracket_ordered π σ p j hπ hσ)
      exact ⟨le_trans ih.1 hsub.1, le_trans hsub.2 ih.2⟩

/-- The fidelity bracket at depth `j` has width `computedWaterHigh π σ / 2 ^ j`. -/
theorem fidelityBracket_width {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (j : ℕ) :
    (fidelityBracket π σ p j).2 - (fidelityBracket π σ p j).1
      = computedWaterHigh π σ / (2 : ℚ) ^ j := by
  induction j with
  | zero => simp [fidelityBracket]
  | succ j ih =>
      dsimp only [fidelityBracket]
      split_ifs with h
      · have hkey : (fidelityBracket π σ p j).2 -
              ((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2
            = ((fidelityBracket π σ p j).2 - (fidelityBracket π σ p j).1) / 2 := by ring
        rw [hkey, ih, pow_succ]
        ring
      · have hkey : ((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2
              - (fidelityBracket π σ p j).1
            = ((fidelityBracket π σ p j).2 - (fidelityBracket π σ p j).1) / 2 := by ring
        rw [hkey, ih, pow_succ]
        ring

/-- A bracket midpoint becomes one of the endpoints of the next bracket. -/
theorem bracketMidpoint_endpoint {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (j : ℕ) :
    bracketMidpoint π σ p j = (fidelityBracket π σ p (j + 1)).1 ∨
      bracketMidpoint π σ p j = (fidelityBracket π σ p (j + 1)).2 := by
  dsimp only [fidelityBracket, bracketMidpoint]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Midpoints at depths `i < j` are separated by at least `computedWaterHigh π σ / 2 ^ (j + 1)`
for nonnegative data. -/
theorem bracketMidpoint_separation {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (i j : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hij : i < j) :
    |bracketMidpoint π σ p i - bracketMidpoint π σ p j|
      ≥ computedWaterHigh π σ / (2 : ℚ) ^ (j + 1) := by
  have hnest := fidelityBracket_nested π σ p (show i + 1 ≤ j by omega) hπ hσ
  have hwidth := fidelityBracket_width π σ p j
  have hordj := fidelityBracket_ordered π σ p j hπ hσ
  have hmid : bracketMidpoint π σ p j
      = ((fidelityBracket π σ p j).1 + (fidelityBracket π σ p j).2) / 2 := rfl
  have hhalf : ((fidelityBracket π σ p j).2 - (fidelityBracket π σ p j).1) / 2
      = computedWaterHigh π σ / (2 : ℚ) ^ (j + 1) := by
    rw [hwidth, pow_succ]
    ring
  rcases bracketMidpoint_endpoint π σ p i with hlo | hhi
  · have hC : (fidelityBracket π σ p j).1 ≥ bracketMidpoint π σ p i := by
      rw [hlo]
      exact hnest.1
    have h1 : 0 ≤ bracketMidpoint π σ p j - bracketMidpoint π σ p i := by
      rw [hmid]
      linarith
    have h1' : bracketMidpoint π σ p i - bracketMidpoint π σ p j ≤ 0 := by linarith
    rw [abs_of_nonpos h1', neg_sub]
    have h2 : bracketMidpoint π σ p j - bracketMidpoint π σ p i
        = ((fidelityBracket π σ p j).2 - (fidelityBracket π σ p j).1) / 2
          + ((fidelityBracket π σ p j).1 - bracketMidpoint π σ p i) := by
      rw [hmid]
      ring
    rw [h2, hhalf]
    have h3 : 0 ≤ (fidelityBracket π σ p j).1 - bracketMidpoint π σ p i := by linarith
    linarith
  · have hD : (fidelityBracket π σ p j).2 ≤ bracketMidpoint π σ p i := by
      rw [hhi]
      exact hnest.2
    have h1 : 0 ≤ bracketMidpoint π σ p i - bracketMidpoint π σ p j := by
      rw [hmid]
      linarith
    rw [abs_of_nonneg h1]
    have h2 : bracketMidpoint π σ p i - bracketMidpoint π σ p j
        = ((fidelityBracket π σ p j).2 - (fidelityBracket π σ p j).1) / 2
          + (bracketMidpoint π σ p i - (fidelityBracket π σ p j).2) := by
      rw [hmid]
      ring
    rw [h2, hhalf]
    have h3 : 0 ≤ bracketMidpoint π σ p i - (fidelityBracket π σ p j).2 := by linarith
    linarith

/-- A finite rational set with pairwise separation at least `s > 0` and diameter at most `W` has
cardinality at most `Nat.floor (W / s) + 1`. -/
theorem Finset.card_le_of_separated_diam (S : Finset ℚ) (s W : ℚ) (hs : 0 < s)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → s ≤ |x - y|)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ W) :
    S.card ≤ Nat.floor (W / s) + 1 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨m, hmS, hmin⟩ : ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
      refine ⟨S.min' hS, Finset.min'_mem S hS, fun x hx => Finset.min'_le S x hx⟩
    have hwin : ∀ x ∈ S, m ≤ x ∧ x ≤ m + W := by
      intro x hx
      refine ⟨hmin x hx, ?_⟩
      have hd : |m - x| ≤ W := hdiam m hmS x hx
      rw [abs_of_nonpos (sub_nonpos.mpr (hmin x hx))] at hd
      linarith
    set g : ℚ → ℕ := fun x => Nat.floor ((x - m) / s) with hg
    have hbucket : ∀ x ∈ S, g x ≤ Nat.floor (W / s) := by
      intro x hx
      have h0 : 0 ≤ (x - m) / s := div_nonneg (sub_nonneg.mpr (hmin x hx)) hs.le
      have h1 : x - m ≤ W := by linarith [hwin x hx]
      have h2 : (x - m) / s ≤ W / s := div_le_div_of_nonneg_right h1 hs.le
      exact Nat.floor_mono h2
    have hinj : Set.InjOn g S := by
      intro x hx y hy hxy
      by_contra hne
      have hltx : (x - m) / s < (g x : ℚ) + 1 := by
        have h := Nat.lt_floor_add_one ((x - m) / s)
        simpa [hg] using! h
      have hlty : (y - m) / s < (g y : ℚ) + 1 := by
        have h := Nat.lt_floor_add_one ((y - m) / s)
        simpa [hg] using! h
      have hgcast : (g x : ℚ) = (g y : ℚ) := by exact_mod_cast hxy
      have hfloory : (g y : ℚ) ≤ (y - m) / s := by
        have h0 : 0 ≤ (y - m) / s := div_nonneg (sub_nonneg.mpr (hmin y hy)) hs.le
        exact Nat.floor_le h0
      have hfloorx : (g x : ℚ) ≤ (x - m) / s := by
        have h0 : 0 ≤ (x - m) / s := div_nonneg (sub_nonneg.mpr (hmin x hx)) hs.le
        exact Nat.floor_le h0
      rw [← hgcast] at hlty
      have hdiff : |x - y| < s := by
        rw [abs_lt]
        constructor
        · have h1 : (y - m) / s - (x - m) / s < 1 := by linarith
          have h2 : (y - m) / s - (x - m) / s = (y - x) / s := by ring
          rw [h2] at h1
          have h3 : y - x < s := by simpa using! (div_lt_iff₀ hs).1 h1
          linarith
        · have h1 : (x - m) / s - (y - m) / s < 1 := by linarith
          have h2 : (x - m) / s - (y - m) / s = (x - y) / s := by ring
          rw [h2] at h1
          have h3 : x - y < s := by simpa using! (div_lt_iff₀ hs).1 h1
          exact h3
      exact absurd (hsep x hx y hy hne) (not_le_of_gt hdiff)
    have hmaps : Set.MapsTo g S (Finset.range (Nat.floor (W / s) + 1)) := by
      intro x hx
      have hmem : g x ∈ Finset.range (Nat.floor (W / s) + 1) := by
        simp only [Finset.mem_range]
        have := hbucket x hx
        omega
      exact hmem
    have hcard := Finset.card_le_card_of_injOn g hmaps hinj
    rw [Finset.card_range] at hcard
    exact hcard
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hempty]

/-- The refinement depths below `k` whose exact bracket midpoints receive ambiguous interval
decisions. -/
def ambiguousDepths {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (fun j => intervalDecision b π σ p (bracketMidpoint π σ p j) = .ambiguous)

/-- The finite set of bracket midpoint levels corresponding to ambiguous depths below `k`. -/
def ambiguousLevels {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : Finset ℚ :=
  (ambiguousDepths b π σ p k).image (bracketMidpoint π σ p)

/-- A lower rate bound relating level separation to gap separation for distinct search midpoints
whose gaps lie in the ambiguity band. -/
def bandRate {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ) : Prop :=
  ∀ j j' : ℕ, j < k → j' < k → j ≠ j' →
    |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
    |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
    c * |bracketMidpoint π σ p j - bracketMidpoint π σ p j'|
      ≤ |fidelityGap π σ p (bracketMidpoint π σ p j)
          - fidelityGap π σ p (bracketMidpoint π σ p j')|

/-- A positive band rate bounds the distance between ambiguous search levels by twice the
ambiguity band bound divided by that rate. -/
theorem ambiguousRegionWidth_le {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) (hc : 0 < c)
    (hrate : bandRate π σ b p c k)
    {γ₁ γ₂ : ℚ} (hamb₁ : intervalDecision b π σ p γ₁ = .ambiguous)
    (hamb₂ : intervalDecision b π σ p γ₂ = .ambiguous)
    (h₁ : γ₁ ∈ ambiguousLevels b π σ p k) (h₂ : γ₂ ∈ ambiguousLevels b π σ p k) :
    |γ₁ - γ₂| ≤ 2 * ambiguityBandBound π σ b p / c := by
  have hB : 0 ≤ ambiguityBandBound π σ b p := by
    unfold ambiguityBandBound
    have hgrid : 0 ≤ gridStep b := by unfold gridStep; positivity
    have hsum : 0 ≤ ∑ j, π j * σ j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
    have h1 : 0 ≤ 2 * (m : ℚ) * gridStep b := by positivity
    have h2 : 0 ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) * gridStep b + p := by linarith
    exact mul_nonneg h1 h2
  by_cases heq : γ₁ = γ₂
  · rw [heq, sub_self, abs_zero]
    rw [le_div_iff₀ hc]
    linarith
  · obtain ⟨j₁, hj₁, hj₁'⟩ := Finset.mem_image.mp h₁
    obtain ⟨j₂, hj₂, hj₂'⟩ := Finset.mem_image.mp h₂
    have hne : j₁ ≠ j₂ := by
      intro h
      apply heq
      rw [← hj₁', ← hj₂', h]
    have hγ₁ : 0 ≤ γ₁ := by
      have hb := fidelityBracket_bounds π σ p j₁ hπ hσ
      dsimp only [bracketMidpoint] at hj₁' ⊢
      rw [← hj₁']
      linarith
    have hγ₂ : 0 ≤ γ₂ := by
      have hb := fidelityBracket_bounds π σ p j₂ hπ hσ
      dsimp only [bracketMidpoint] at hj₂' ⊢
      rw [← hj₂']
      linarith
    have hband₁ := intervalAmbiguity_gap_le π σ b p hπ hσ hγ₁ hp hamb₁
    have hband₂ := intervalAmbiguity_gap_le π σ b p hπ hσ hγ₂ hp hamb₂
    have hrate' := hrate j₁ j₂
      (Finset.mem_range.mp ((Finset.mem_filter.mp hj₁).1))
      (Finset.mem_range.mp ((Finset.mem_filter.mp hj₂).1)) hne
    have hband₁' := hband₁
    have hband₂' := hband₂
    rw [← hj₁'] at hband₁
    rw [← hj₂'] at hband₂
    rw [hj₁', hj₂'] at hrate'
    have hdiff : |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂|
        ≤ 2 * ambiguityBandBound π σ b p := by
      have hsum : |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂|
          ≤ |fidelityGap π σ p γ₁| + |fidelityGap π σ p γ₂| := by
        have hkey : fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂
            = fidelityGap π σ p γ₁ + -(fidelityGap π σ p γ₂) := by ring
        rw [hkey]
        simpa only [abs_neg] using!
          abs_add_le (fidelityGap π σ p γ₁) (-(fidelityGap π σ p γ₂))
      linarith
    have hrate'' := hrate' hband₁' hband₂'
    rw [le_div_iff₀ hc]
    nlinarith [hrate'', hdiff]

/-- For nonnegative data and target, the search ambiguity count equals the cardinality of
`ambiguousDepths`. -/
theorem intervalFidelitySearch_ambiguities_depths {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ)
    (p : ℚ) (k : ℕ) (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) :
    (intervalFidelitySearch b π σ p k).2.ambiguities
      = (ambiguousDepths b π σ p k).card := by
  have hsum := intervalFidelitySearch_ambiguities b π σ p k hπ hσ hp
  rw [hsum]
  classical
  rw [Finset.sum_boole]
  have hfilter : (Finset.range k).filter
        (fun j => ¬ (computedDotDown b π σ (bracketMidpoint π σ p j)) ^ 2
              ≥ p * computedMassUp b π σ (bracketMidpoint π σ p j) ∧
            ¬ (computedDotUp b π σ (bracketMidpoint π σ p j)) ^ 2
              < p * computedMassDown b π σ (bracketMidpoint π σ p j))
      = (Finset.range k).filter
        (fun j => intervalDecision b π σ p (bracketMidpoint π σ p j) = .ambiguous) := by
    apply Finset.filter_congr
    intro j _
    exact (intervalDecision_ambiguous_iff π σ b p (bracketMidpoint π σ p j)).symm
  simp only [bracketMidpoint] at hfilter
  rw [hfilter]
  unfold ambiguousDepths
  rfl

/-- For nonnegative source and target entries, bracket midpoints at distinct refinement depths
are distinct. -/
theorem bracketMidpoint_ne {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {i j : ℕ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hij : i ≠ j) :
    bracketMidpoint π σ p i ≠ bracketMidpoint π σ p j := by
  by_contra hne
  have hpos' : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  rcases lt_or_gt_of_ne hij with h | h
  · have hsep := bracketMidpoint_separation π σ p i j hπ hσ h
    have hq : 0 < computedWaterHigh π σ / (2 : ℚ) ^ (j + 1) :=
      div_pos hpos' (by positivity)
    rw [hne, sub_self, abs_zero] at hsep
    linarith
  · have hsep := bracketMidpoint_separation π σ p j i hπ hσ h
    have hq : 0 < computedWaterHigh π σ / (2 : ℚ) ^ (i + 1) :=
      div_pos hpos' (by positivity)
    rw [hne, sub_self, abs_zero] at hsep
    linarith

/-- For nonnegative source and target entries, the number of ambiguous levels equals the number
of ambiguous depths. -/
theorem ambiguousLevels_card {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) :
    (ambiguousLevels b π σ p k).card = (ambiguousDepths b π σ p k).card := by
  unfold ambiguousLevels
  refine Finset.card_image_of_injOn ?_
  intro i hi j hj hij
  by_contra hne
  exact absurd hij (bracketMidpoint_ne π σ p hπ hσ hne)

/-- Natural powers of rational two are monotone in their exponent. -/
private theorem two_pow_le {a b : ℕ} (h : a ≤ b) : (2 : ℚ) ^ a ≤ (2 : ℚ) ^ b := by
  have h1 : (2 : ℕ) ^ a ≤ (2 : ℕ) ^ b := Nat.pow_le_pow_right (by omega) h
  calc (2 : ℚ) ^ a = ((2 : ℕ) ^ a : ℚ) := by simp
    _ ≤ ((2 : ℕ) ^ b : ℚ) := by exact_mod_cast h1
    _ = (2 : ℚ) ^ b := by simp

/-- For positive `H`, division by `H / 2 ^ k` equals multiplication by `2 ^ k` followed by
division by `H`. -/
private theorem div_grid {W H : ℚ} (hH : 0 < H) (k : ℕ) :
    W / (H / (2 : ℚ) ^ k) = W * (2 : ℚ) ^ k / H := by
  have h2k : (2 : ℚ) ^ k ≠ 0 := by positivity
  have hb : H / (2 : ℚ) ^ k ≠ 0 := by positivity
  rw [div_eq_div_iff hb (ne_of_gt hH)]
  field_simp [h2k]

/-- Distinct ambiguous levels from the first `k` refinements are separated by at least
`computedWaterHigh π σ / 2 ^ k`. -/
theorem ambiguousLevels_separation {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {x y : ℚ}
    (hx : x ∈ ambiguousLevels b π σ p k) (hy : y ∈ ambiguousLevels b π σ p k)
    (hne : x ≠ y) :
    computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| := by
  obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hyj⟩ := Finset.mem_image.mp hy
  have hxi' : x = bracketMidpoint π σ p i := hxi.symm
  have hyj' : y = bracketMidpoint π σ p j := hyj.symm
  have hiR : i ∈ Finset.range k := (Finset.mem_filter.mp hi).1
  have hjR : j ∈ Finset.range k := (Finset.mem_filter.mp hj).1
  have hij : i ≠ j := by
    intro h
    apply hne
    exact hxi'.trans ((congrArg (bracketMidpoint π σ p) h).trans hyj'.symm)
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hsep := bracketMidpoint_separation π σ p i j hπ hσ hlt
    have hjk : j + 1 ≤ k := by
      have := Finset.mem_range.mp hjR
      omega
    have hpow : (2 : ℚ) ^ (j + 1) ≤ (2 : ℚ) ^ k := two_pow_le hjk
    have hdiv : computedWaterHigh π σ / (2 : ℚ) ^ k
        ≤ computedWaterHigh π σ / (2 : ℚ) ^ (j + 1) :=
      div_le_div_of_nonneg_left (le_of_lt hH) (by positivity) hpow
    rw [hxi', hyj']
    exact le_trans hdiv hsep
  · have hsep' : computedWaterHigh π σ / (2 : ℚ) ^ (i + 1)
        ≤ |bracketMidpoint π σ p i - bracketMidpoint π σ p j| := by
      rw [abs_sub_comm]
      exact bracketMidpoint_separation π σ p j i hπ hσ hlt
    have hik : i + 1 ≤ k := by
      have := Finset.mem_range.mp hiR
      omega
    have hpow : (2 : ℚ) ^ (i + 1) ≤ (2 : ℚ) ^ k := two_pow_le hik
    have hdiv : computedWaterHigh π σ / (2 : ℚ) ^ k
        ≤ computedWaterHigh π σ / (2 : ℚ) ^ (i + 1) :=
      div_le_div_of_nonneg_left (le_of_lt hH) (by positivity) hpow
    rw [hxi', hyj']
    exact le_trans hdiv hsep'

/-- A positive band rate bounds the diameter of the ambiguous level set by `2 *
ambiguityBandBound π σ b p / c`. -/
theorem ambiguousLevels_diam {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (c : ℚ) (hc : 0 < c) (hrate : bandRate π σ b p c k)
    {x y : ℚ} (hx : x ∈ ambiguousLevels b π σ p k) (hy : y ∈ ambiguousLevels b π σ p k) :
    |x - y| ≤ 2 * ambiguityBandBound π σ b p / c := by
  have hxamb : intervalDecision b π σ p x = .ambiguous := by
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp hx
    rw [← hj']
    exact (Finset.mem_filter.mp hj).2
  have hyamb : intervalDecision b π σ p y = .ambiguous := by
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp hy
    rw [← hj']
    exact (Finset.mem_filter.mp hj).2
  exact ambiguousRegionWidth_le π σ b p c k hπ hσ hp hc hrate hxamb hyamb hx hy

/-- A positive band rate bounds the search ambiguity count by the floor of ambiguity-region
width divided by grid separation, plus one. -/
theorem ambiguityCount_le {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (c : ℚ) (hc : 0 < c) (hrate : bandRate π σ b p c k) :
    (intervalFidelitySearch b π σ p k).2.ambiguities
      ≤ Nat.floor (2 * ambiguityBandBound π σ b p / c * (2 : ℚ) ^ k
          / computedWaterHigh π σ) + 1 := by
  have hcard : (intervalFidelitySearch b π σ p k).2.ambiguities
      = (ambiguousLevels b π σ p k).card :=
    (intervalFidelitySearch_ambiguities_depths b π σ p k hπ hσ hp).trans
      (ambiguousLevels_card b π σ p k hπ hσ).symm
  rw [hcard]
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  have hsp : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k :=
    div_pos hH (by positivity)
  have hsep : ∀ x ∈ ambiguousLevels b π σ p k, ∀ y ∈ ambiguousLevels b π σ p k,
      x ≠ y → computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| :=
    fun x hx y hy hne => ambiguousLevels_separation b π σ p k hπ hσ hx hy hne
  have hdiam : ∀ x ∈ ambiguousLevels b π σ p k, ∀ y ∈ ambiguousLevels b π σ p k,
      |x - y| ≤ 2 * ambiguityBandBound π σ b p / c :=
    fun x hx y hy => ambiguousLevels_diam b π σ p k hπ hσ hp c hc hrate hx hy
  have hbound := Finset.card_le_of_separated_diam (ambiguousLevels b π σ p k)
    (computedWaterHigh π σ / (2 : ℚ) ^ k) (2 * ambiguityBandBound π σ b p / c) hsp hsep hdiam
  have hconv : (2 * ambiguityBandBound π σ b p / c) / (computedWaterHigh π σ / (2 : ℚ) ^ k)
      = 2 * ambiguityBandBound π σ b p / c * (2 : ℚ) ^ k / computedWaterHigh π σ :=
    div_grid hH k
  rw [hconv] at hbound
  exact hbound

/-- The interval search bit budget using the ambiguity count bound obtained from a region width
`W`, high endpoint `H`, and refinement depth. -/
def intervalWidthOpBitBudget {ε p πi : ℚ} (m k : ℕ) (W H : ℚ) : ℚ :=
  intervalSearchOpBitBudget ε p πi m k (Nat.floor (W * (2 : ℚ) ^ k / H) + 1)

/-- For positive parameters and operation counts, the operation bit budget is antitone in the
operation count. -/
theorem opBitBudget_mono {ε p πi : ℚ} {n n' : ℕ} (hn : 0 < n)
    (hε : 0 < ε) (hp : 0 < p) (hπi : 0 < πi) (h : n ≤ n') :
    opBitBudget ε p πi n' ≤ opBitBudget ε p πi n := by
  have hA : 2 * ε * πi ^ 2 / ((n' : ℚ) * p) ≤ 2 * ε * πi ^ 2 / ((n : ℚ) * p) := by
    have hX : 0 ≤ 2 * ε * πi ^ 2 := by positivity
    have hc : 0 < ((n : ℚ) * p) := mul_pos (by exact_mod_cast hn) hp
    have h1 : ((n : ℚ) * p) ≤ ((n' : ℚ) * p) := by
      have h2 : (n : ℚ) ≤ (n' : ℚ) := by exact_mod_cast h
      exact mul_le_mul_of_nonneg_right h2 hp.le
    exact div_le_div_of_nonneg_left hX hc h1
  have hB : πi ^ 2 / (n' : ℚ) ≤ πi ^ 2 / (n : ℚ) := by
    have hX : 0 ≤ πi ^ 2 := sq_nonneg πi
    have hc : 0 < (n : ℚ) := by exact_mod_cast hn
    have h1 : (n : ℚ) ≤ (n' : ℚ) := by exact_mod_cast h
    exact div_le_div_of_nonneg_left hX hc h1
  unfold opBitBudget
  exact min_le_min hA hB

/-- The interval run operation count is monotone in its ambiguity count. -/
theorem intervalRunOperationCount_mono (m k : ℕ) {a a' : ℕ} (h : a ≤ a') :
    intervalRunOperationCount m k a ≤ intervalRunOperationCount m k a' := by
  have hmul : 2 * m * a ≤ 2 * m * a' := Nat.mul_le_mul_left (2 * m) h
  unfold intervalRunOperationCount
  linarith

/-- A width-based interval bit budget and positive band rate bound the accumulated error
allowances using the actual search ambiguity count. -/
theorem intervalSearch_budget_of_width {m : ℕ} (π σ : Fin m → ℚ) (p ε πi : ℚ) (b k : ℕ)
    (hε : 0 < ε) (hp : 0 < p) (hπi : 0 < πi)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (c : ℚ) (hc : 0 < c) (hrate : bandRate π σ b p c k)
    (hb : gridStep b ≤ intervalWidthOpBitBudget (ε := ε) (p := p) (πi := πi) m k
            (2 * ambiguityBandBound π σ b p / c) (computedWaterHigh π σ)) :
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  have hcount := ambiguityCount_le b π σ p k hπ hσ hp.le c hc hrate
  have hop := intervalRunOperationCount_mono m k hcount
  have hn : 0 < intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities :=
    intervalRunOperationCount_pos m k _
  have hbud : opBitBudget ε p πi
        (intervalRunOperationCount m k (Nat.floor (2 * ambiguityBandBound π σ b p / c
          * (2 : ℚ) ^ k / computedWaterHigh π σ) + 1))
      ≤ opBitBudget ε p πi
        (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities) :=
    opBitBudget_mono hn hε hp hπi hop
  have hb' : gridStep b ≤ intervalSearchOpBitBudget ε p πi m k
      (intervalFidelitySearch b π σ p k).2.ambiguities := by
    calc gridStep b ≤ intervalWidthOpBitBudget (ε := ε) (p := p) (πi := πi) m k
            (2 * ambiguityBandBound π σ b p / c) (computedWaterHigh π σ) := hb
      _ = intervalSearchOpBitBudget ε p πi m k
            (Nat.floor (2 * ambiguityBandBound π σ b p / c * (2 : ℚ) ^ k
              / computedWaterHigh π σ) + 1) := rfl
      _ ≤ intervalSearchOpBitBudget ε p πi m k
            ((intervalFidelitySearch b π σ p k).2.ambiguities) := by
          unfold intervalSearchOpBitBudget
          exact hbud
  exact intervalSearchOpBitBudget_sufficient hε hp hπi b hb'

/-- The finite set of positive source indices whose scaled target entries strictly exceed their
source entries. -/
def satSet {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => 0 < π j ∧ π j < γ * σ j)

/-- The source-target dot product restricted to an index set. -/
def satDot {m : ℕ} (π σ : Fin m → ℚ) (S : Finset (Fin m)) : ℚ :=
  ∑ j : Fin m, if j ∈ S then σ j * π j else 0

/-- The sum of squared source entries restricted to an index set. -/
def satMass {m : ℕ} (π : Fin m → ℚ) (S : Finset (Fin m)) : ℚ :=
  ∑ j : Fin m, if j ∈ S then π j ^ 2 else 0

/-- The sum of squared target entries over positive source indices outside the given index set. -/
def freeSq {m : ℕ} (π σ : Fin m → ℚ) (S : Finset (Fin m)) : ℚ :=
  ∑ j : Fin m, if j ∈ S then 0 else (if 0 < π j then σ j ^ 2 else 0)

/-- At an index in `satSet`, the water-filled entry equals the source entry. -/
theorem waterFill_sat {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} {j : Fin m}
    (hj : j ∈ satSet π σ γ) : waterFill π σ γ j = π j := by
  have hj' := (Finset.mem_filter.mp hj).2
  have h1 : π j < γ * σ j := hj'.2
  rw [waterFill, min_eq_left (le_of_lt h1)]

/-- At a positive source index outside `satSet`, the water-filled entry equals the level times
the target entry. -/
theorem waterFill_free {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} {j : Fin m}
    (hπ : 0 < π j) (hj : j ∉ satSet π σ γ) :
    waterFill π σ γ j = γ * σ j := by
  have hj' : ¬ (0 < π j ∧ π j < γ * σ j) := by
    simpa [satSet, Finset.mem_filter, Finset.mem_univ, true_and] using! hj
  have h1 : γ * σ j ≤ π j := by
    by_contra hc
    exact hj' ⟨hπ, lt_of_not_ge hc⟩
  rw [waterFill, min_eq_right h1]

/-- A zero source entry has zero water fill when the level and corresponding target entry are
nonnegative. -/
theorem waterFill_zero {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} {j : Fin m}
    (hπ : π j = 0) (hγ : 0 ≤ γ) (hσ : 0 ≤ σ j) : waterFill π σ γ j = 0 := by
  rw [waterFill, hπ, min_eq_left (mul_nonneg hγ hσ)]

/-- For a fixed saturation pattern, the computed dot product equals the saturated dot
contribution plus the level times `freeSq`. -/
theorem computedDot_piece {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} (S : Finset (Fin m))
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ)
    (hpat : satSet π σ γ = S) :
    computedDot π σ γ = satDot π σ S + γ * freeSq π σ S := by
  have hmem : ∀ j : Fin m, j ∈ S ↔ j ∈ satSet π σ γ := fun j => by rw [hpat]
  have hstep : ∀ j : Fin m, σ j * waterFill π σ γ j
      = (if j ∈ S then σ j * π j else (if 0 < π j then σ j * (γ * σ j) else 0)) := by
    intro j
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, waterFill_sat π σ ((hmem j).mp hjS)]
    · rw [if_neg hjS]
      have hnot : j ∉ satSet π σ γ := fun h => hjS ((hmem j).mpr h)
      by_cases hjπ : 0 < π j
      · rw [if_pos hjπ, waterFill_free π σ hjπ hnot]
      · rw [if_neg hjπ]
        have hπ0 : π j = 0 := le_antisymm (not_lt.mp hjπ) (hπ j)
        rw [waterFill_zero π σ hπ0 hγ (hσ j)]
        ring
  have hstep2 : ∀ j : Fin m,
      (if j ∈ S then σ j * π j else (if 0 < π j then σ j * (γ * σ j) else 0))
      = (if j ∈ S then σ j * π j else 0)
        + γ * (if j ∈ S then 0 else (if 0 < π j then σ j ^ 2 else 0)) := by
    intro j
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos hjS, if_pos hjS]
      ring
    · rw [if_neg hjS, if_neg hjS]
      by_cases hjπ : 0 < π j
      · rw [if_pos hjπ, if_neg hjS, if_pos hjπ]
        ring
      · rw [if_neg hjπ, if_neg hjS, if_neg hjπ]
        ring
  unfold computedDot
  rw [Finset.sum_congr rfl (fun j _ => hstep j),
    Finset.sum_congr rfl (fun j _ => hstep2 j),
    Finset.sum_add_distrib]
  simp only [satDot, freeSq]
  rw [Finset.mul_sum]

/-- For a fixed saturation pattern, the computed mass equals the saturated mass plus the squared
level times `freeSq`. -/
theorem computedMass_piece {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} (S : Finset (Fin m))
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ)
    (hpat : satSet π σ γ = S) :
    computedMass π σ γ = satMass π S + γ ^ 2 * freeSq π σ S := by
  have hmem : ∀ j : Fin m, j ∈ S ↔ j ∈ satSet π σ γ := fun j => by rw [hpat]
  have hstep : ∀ j : Fin m, (waterFill π σ γ j) ^ 2
      = (if j ∈ S then π j ^ 2 else (if 0 < π j then (γ * σ j) ^ 2 else 0)) := by
    intro j
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, waterFill_sat π σ ((hmem j).mp hjS)]
    · rw [if_neg hjS]
      have hnot : j ∉ satSet π σ γ := fun h => hjS ((hmem j).mpr h)
      by_cases hjπ : 0 < π j
      · rw [if_pos hjπ, waterFill_free π σ hjπ hnot]
      · rw [if_neg hjπ]
        have hπ0 : π j = 0 := le_antisymm (not_lt.mp hjπ) (hπ j)
        rw [waterFill_zero π σ hπ0 hγ (hσ j)]
        ring
  have hstep2 : ∀ j : Fin m,
      (if j ∈ S then π j ^ 2 else (if 0 < π j then (γ * σ j) ^ 2 else 0))
      = (if j ∈ S then π j ^ 2 else 0)
        + γ ^ 2 * (if j ∈ S then 0 else (if 0 < π j then σ j ^ 2 else 0)) := by
    intro j
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos hjS, if_pos hjS]
      ring
    · rw [if_neg hjS, if_neg hjS]
      by_cases hjπ : 0 < π j
      · rw [if_pos hjπ, if_neg hjS, if_pos hjπ]
        ring
      · rw [if_neg hjπ, if_neg hjS, if_neg hjπ]
        ring
  unfold computedMass computedWaterEnergy
  rw [Finset.sum_congr rfl (fun j _ => hstep j),
    Finset.sum_congr rfl (fun j _ => hstep2 j),
    Finset.sum_add_distrib]
  simp only [satMass, freeSq]
  rw [Finset.mul_sum]

/-- For a fixed saturation pattern, the fidelity gap is the stated quadratic polynomial in the
level. -/
theorem fidelityGap_piece {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (γ : ℚ) (S : Finset (Fin m))
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ)
    (hpat : satSet π σ γ = S) :
    fidelityGap π σ p γ
      = freeSq π σ S * (freeSq π σ S - p) * γ ^ 2
        + 2 * satDot π σ S * freeSq π σ S * γ
        + (satDot π σ S ^ 2 - p * satMass π S) := by
  have hD := computedDot_piece π σ S hπ hσ hγ hpat
  have hM := computedMass_piece π σ S hπ hσ hγ hpat
  unfold fidelityGap
  rw [hD, hM]
  ring

/-- The derivative expression of the fidelity-gap quadratic associated with a fixed saturation
set. -/
def pieceSlopeAt {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S : Finset (Fin m)) (γ : ℚ) : ℚ :=
  2 * freeSq π σ S * ((freeSq π σ S - p) * γ + satDot π σ S)

/-- At two nonnegative levels with the same saturation set, the gap difference factors as the
level difference times the quadratic's secant slope. -/
theorem fidelityGap_diff_piece {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (γ₁ γ₂ : ℚ)
    (S : Finset (Fin m))
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S) (hpat₂ : satSet π σ γ₂ = S) :
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γ₂ - γ₁) * (freeSq π σ S * (freeSq π σ S - p) * (γ₁ + γ₂)
          + 2 * satDot π σ S * freeSq π σ S) := by
  rw [fidelityGap_piece π σ p γ₂ S hπ hσ hγ₂ hpat₂,
    fidelityGap_piece π σ p γ₁ S hπ hσ hγ₁ hpat₁]
  ring

/-- At two nonnegative levels with the same saturation set, the gap difference equals the level
difference times `pieceSlopeAt` at their midpoint. -/
theorem fidelityGap_diff_piece_slope {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (γ₁ γ₂ : ℚ)
    (S : Finset (Fin m))
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S) (hpat₂ : satSet π σ γ₂ = S) :
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γ₂ - γ₁) * pieceSlopeAt π σ p S ((γ₁ + γ₂) / 2) := by
  rw [fidelityGap_diff_piece π σ p γ₁ γ₂ S hπ hσ hγ₁ hγ₂ hpat₁ hpat₂]
  unfold pieceSlopeAt
  ring

/-- The absolute difference of two rationals is unchanged by swapping their order. -/
private theorem abs_sub_swap (a b : ℚ) : |a - b| = |b - a| := by
  have h : a - b = -(b - a) := by ring
  rw [h, abs_neg]

/-- A lower bound on the absolute midpoint slope for a common saturation pattern gives a lower
bound on gap separation. -/
theorem fidelityGap_rate_of_piece {m : ℕ} (π σ : Fin m → ℚ) (p c : ℚ)
    (S : Finset (Fin m)) (γ₁ γ₂ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S) (hpat₂ : satSet π σ γ₂ = S)
    (hslope : c ≤ |pieceSlopeAt π σ p S ((γ₁ + γ₂) / 2)|) :
    c * |γ₁ - γ₂| ≤ |fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁| := by
  rw [fidelityGap_diff_piece_slope π σ p γ₁ γ₂ S hπ hσ hγ₁ hγ₂ hpat₁ hpat₂]
  calc c * |γ₁ - γ₂| = |γ₂ - γ₁| * c := by rw [abs_sub_swap]; ring
    _ ≤ |γ₂ - γ₁| * |pieceSlopeAt π σ p S ((γ₁ + γ₂) / 2)| :=
      mul_le_mul_of_nonneg_left hslope (abs_nonneg _)
    _ = |(γ₂ - γ₁) * pieceSlopeAt π σ p S ((γ₁ + γ₂) / 2)| := (abs_mul _ _).symm

/-- A common saturation pattern and a uniform absolute slope bound on an interval containing the
relevant search midpoints imply `bandRate`. -/
theorem bandRate_of_piece_interval {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ)
    (S : Finset (Fin m)) (lo hi : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hpat : ∀ j j' : ℕ, j < k → j' < k → j ≠ j' →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
      satSet π σ (bracketMidpoint π σ p j) = S ∧
        satSet π σ (bracketMidpoint π σ p j') = S)
    (hrange : ∀ j : ℕ, j < k →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      lo ≤ bracketMidpoint π σ p j ∧ bracketMidpoint π σ p j ≤ hi)
    (hslope : ∀ γ : ℚ, lo ≤ γ → γ ≤ hi → c ≤ |pieceSlopeAt π σ p S γ|) :
    bandRate π σ b p c k := by
  intro j j' hj hj' hne hb1 hb2
  obtain ⟨hS1, hS2⟩ := hpat j j' hj hj' hne hb1 hb2
  obtain ⟨hl1, hh1⟩ := hrange j hj hb1
  obtain ⟨hl2, hh2⟩ := hrange j' hj' hb2
  have hmid_lo : lo ≤ (bracketMidpoint π σ p j + bracketMidpoint π σ p j') / 2 := by linarith
  have hmid_hi : (bracketMidpoint π σ p j + bracketMidpoint π σ p j') / 2 ≤ hi := by linarith
  have hγ₁ : 0 ≤ bracketMidpoint π σ p j := by
    have hb := fidelityBracket_bounds π σ p j hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  have hγ₂ : 0 ≤ bracketMidpoint π σ p j' := by
    have hb := fidelityBracket_bounds π σ p j' hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  calc c * |bracketMidpoint π σ p j - bracketMidpoint π σ p j'|
      = c * |bracketMidpoint π σ p j' - bracketMidpoint π σ p j| := by rw [abs_sub_swap]
    _ ≤ |fidelityGap π σ p (bracketMidpoint π σ p j')
          - fidelityGap π σ p (bracketMidpoint π σ p j)| := by
        have h := fidelityGap_rate_of_piece π σ p c S (bracketMidpoint π σ p j)
          (bracketMidpoint π σ p j') hπ hσ hγ₁ hγ₂ hS1 hS2
          (hslope _ hmid_lo hmid_hi)
        rw [abs_sub_swap] at h
        exact h
    _ = |fidelityGap π σ p (bracketMidpoint π σ p j)
          - fidelityGap π σ p (bracketMidpoint π σ p j')| := by rw [abs_sub_swap]

/-- Cancels a strictly positive common left factor from a rational inequality. -/
private theorem le_of_mul_le_mul_pos {a b c : ℚ} (hc : 0 < c) (h : c * a ≤ c * b) :
    a ≤ b := by
  have hd : 0 < c⁻¹ := by positivity
  have hdc : c⁻¹ * c = 1 := by field_simp
  have h1 : c⁻¹ * (c * a) ≤ c⁻¹ * (c * b) :=
    mul_le_mul_of_nonneg_left h (le_of_lt hd)
  nlinarith [hdc, h1]

/-- A positive lower bound on the absolute piece slope at same-sign endpoints also bounds its
absolute value throughout the interval. -/
theorem pieceSlope_bound_of_endpoints {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S : Finset (Fin m)) {lo hi γ : ℚ} (rate : ℚ) (hrate : 0 < rate)
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi) (hγ : lo ≤ γ) (hγ' : γ ≤ hi)
    (hend_lo : rate ≤ |pieceSlopeAt π σ p S lo|)
    (hend_hi : rate ≤ |pieceSlopeAt π σ p S hi|)
    (hsign : 0 < pieceSlopeAt π σ p S lo * pieceSlopeAt π σ p S hi) :
    rate ≤ |pieceSlopeAt π σ p S γ| := by
  have hkey : (hi - lo) * pieceSlopeAt π σ p S γ
      = (hi - γ) * pieceSlopeAt π σ p S lo
        + (γ - lo) * pieceSlopeAt π σ p S hi := by
    unfold pieceSlopeAt
    ring
  have hrate : rate ≤ min |pieceSlopeAt π σ p S lo| |pieceSlopeAt π σ p S hi| :=
    le_min hend_lo hend_hi
  have hne_lo : pieceSlopeAt π σ p S lo ≠ 0 := by
    intro h
    have : pieceSlopeAt π σ p S lo * pieceSlopeAt π σ p S hi = 0 := by rw [h]; ring
    linarith [hsign]
  by_cases hlohi : lo = hi
  · have hγeq : γ = lo := by linarith
    subst hγeq
    exact hend_lo
  · have hgt : 0 < hi - lo := by
      have hlt : lo < hi := lt_of_le_of_ne hhi hlohi
      exact sub_pos.mpr hlt
    have hmin : min (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi)
        ≤ pieceSlopeAt π σ p S γ := by
      by_cases hle : pieceSlopeAt π σ p S lo ≤ pieceSlopeAt π σ p S hi
      · rw [min_eq_left hle]
        have h2 : (γ - lo) * (pieceSlopeAt π σ p S hi - pieceSlopeAt π σ p S lo) ≥ 0 :=
          mul_nonneg (sub_nonneg.mpr hγ) (sub_nonneg.mpr hle)
        have h1 : (hi - lo) * pieceSlopeAt π σ p S lo
            ≤ (hi - γ) * pieceSlopeAt π σ p S lo
              + (γ - lo) * pieceSlopeAt π σ p S hi := by linarith
        rw [← hkey] at h1
        exact le_of_mul_le_mul_pos hgt h1
      · rw [min_eq_right (le_of_not_ge hle)]
        have h2 : (hi - γ) * (pieceSlopeAt π σ p S lo - pieceSlopeAt π σ p S hi) ≥ 0 :=
          mul_nonneg (sub_nonneg.mpr hγ') (sub_nonneg.mpr (le_of_not_ge hle))
        have h1 : (hi - lo) * pieceSlopeAt π σ p S hi
            ≤ (hi - γ) * pieceSlopeAt π σ p S lo
              + (γ - lo) * pieceSlopeAt π σ p S hi := by linarith
        rw [← hkey] at h1
        exact le_of_mul_le_mul_pos hgt h1
    have hmax : pieceSlopeAt π σ p S γ
        ≤ max (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi) := by
      by_cases hle : pieceSlopeAt π σ p S lo ≤ pieceSlopeAt π σ p S hi
      · rw [max_eq_right hle]
        have h2 : (hi - γ) * (pieceSlopeAt π σ p S hi - pieceSlopeAt π σ p S lo) ≥ 0 :=
          mul_nonneg (sub_nonneg.mpr hγ') (sub_nonneg.mpr hle)
        have h1 : (hi - γ) * pieceSlopeAt π σ p S lo
            + (γ - lo) * pieceSlopeAt π σ p S hi
            ≤ (hi - lo) * pieceSlopeAt π σ p S hi := by linarith
        rw [← hkey] at h1
        exact le_of_mul_le_mul_pos hgt h1
      · rw [max_eq_left (le_of_not_ge hle)]
        have h2 : (γ - lo) * (pieceSlopeAt π σ p S lo - pieceSlopeAt π σ p S hi) ≥ 0 :=
          mul_nonneg (sub_nonneg.mpr hγ) (sub_nonneg.mpr (le_of_not_ge hle))
        have h1 : (hi - γ) * pieceSlopeAt π σ p S lo
            + (γ - lo) * pieceSlopeAt π σ p S hi
            ≤ (hi - lo) * pieceSlopeAt π σ p S lo := by linarith
        rw [← hkey] at h1
        exact le_of_mul_le_mul_pos hgt h1
    by_cases hpos : 0 < pieceSlopeAt π σ p S lo
    · have hpos' : 0 < pieceSlopeAt π σ p S hi := by
        by_contra hc'
        have hnonpos : pieceSlopeAt π σ p S hi ≤ 0 := le_of_not_gt hc'
        have hprod : pieceSlopeAt π σ p S lo * pieceSlopeAt π σ p S hi ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hpos.le hnonpos
        linarith [hsign]
      have hminabs : min |pieceSlopeAt π σ p S lo| |pieceSlopeAt π σ p S hi|
          = min (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi) := by
        rw [abs_of_pos hpos, abs_of_pos hpos']
      have hfg : 0 < pieceSlopeAt π σ p S γ := by
        have h1 : 0 < min (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi) :=
          lt_min hpos hpos'
        linarith [hmin]
      rw [abs_of_pos hfg]
      calc rate ≤ min |pieceSlopeAt π σ p S lo| |pieceSlopeAt π σ p S hi| := hrate
        _ = min (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi) := hminabs
        _ ≤ pieceSlopeAt π σ p S γ := hmin
    · have hneg : pieceSlopeAt π σ p S lo < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hne_lo
      have hneg' : pieceSlopeAt π σ p S hi < 0 := by
        by_contra hc'
        have hnonneg : 0 ≤ pieceSlopeAt π σ p S hi := le_of_not_gt hc'
        have hprod : pieceSlopeAt π σ p S lo * pieceSlopeAt π σ p S hi ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hneg.le hnonneg
        linarith [hsign]
      have hminabs : min |pieceSlopeAt π σ p S lo| |pieceSlopeAt π σ p S hi|
          = -(max (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi)) := by
        rw [abs_of_neg hneg, abs_of_neg hneg']
        by_cases hle : pieceSlopeAt π σ p S lo ≤ pieceSlopeAt π σ p S hi
        · rw [min_eq_right (neg_le_neg hle), max_eq_right hle]
        · rw [min_eq_left (neg_le_neg (le_of_not_ge hle)), max_eq_left (le_of_not_ge hle)]
      have hfg : pieceSlopeAt π σ p S γ < 0 := by
        have h1 : max (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi) < 0 :=
          max_lt hneg hneg'
        linarith [hmax]
      calc rate ≤ min |pieceSlopeAt π σ p S lo| |pieceSlopeAt π σ p S hi| := hrate
        _ = -(max (pieceSlopeAt π σ p S lo) (pieceSlopeAt π σ p S hi)) := hminabs
        _ ≤ -(pieceSlopeAt π σ p S γ) := neg_le_neg hmax
        _ = |pieceSlopeAt π σ p S γ| := (abs_of_neg hfg).symm

/-- The smaller of the absolute piece slopes at the two endpoints of an interval. -/
def pieceSlopeLower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S : Finset (Fin m))
    (lo hi : ℚ) : ℚ :=
  min |pieceSlopeAt π σ p S lo| |pieceSlopeAt π σ p S hi|

/-- Positive same-sign endpoint slopes in absolute value, a common saturation pattern, and
midpoint location bounds give a band rate via `pieceSlopeLower`. -/
theorem bandRate_of_piece_lower {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ)
    (S : Finset (Fin m)) (lo hi : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi)
    (hc : 0 < c)
    (hlower : c ≤ pieceSlopeLower π σ p S lo hi)
    (hsign : 0 < pieceSlopeAt π σ p S lo * pieceSlopeAt π σ p S hi)
    (hpat : ∀ j j' : ℕ, j < k → j' < k → j ≠ j' →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
      satSet π σ (bracketMidpoint π σ p j) = S ∧
        satSet π σ (bracketMidpoint π σ p j') = S)
    (hrange : ∀ j : ℕ, j < k →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      lo ≤ bracketMidpoint π σ p j ∧ bracketMidpoint π σ p j ≤ hi) :
    bandRate π σ b p c k := by
  refine bandRate_of_piece_interval π σ b p c k S lo hi hπ hσ hpat hrange ?_
  intro γ hγ hγ'
  exact pieceSlope_bound_of_endpoints π σ p S c hc hlo hhi hγ hγ'
    (le_trans hlower (min_le_left _ _)) (le_trans hlower (min_le_right _ _)) hsign

/-- The plateau condition holds exactly when the strict saturation set is empty. -/
theorem onPlateau_iff_satSet_empty {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    onPlateau π σ γ ↔ satSet π σ γ = ∅ := by
  constructor
  · intro hγ
    refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj => ?_
    have hj' := (Finset.mem_filter.mp hj).2
    exact absurd hj'.2 (not_lt_of_ge (hγ j hj'.1))
  · intro hγ j hj
    by_contra hc
    have hlt : π j < γ * σ j := lt_of_not_ge hc
    have hmem : j ∈ satSet π σ γ := by
      simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and, hj, hlt]
    rw [hγ] at hmem
    exact (Finset.notMem_empty j) hmem

/-- For two nonnegative plateau levels, the fidelity gap difference factors using their sum,
difference, and `computedPmax π σ * (computedPmax π σ - p)`. -/
theorem plateau_gap_rate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {γ₁ γ₂ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hplate₁ : onPlateau π σ γ₁) (hplate₂ : onPlateau π σ γ₂) :
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (computedPmax π σ * (computedPmax π σ - p)) * (γ₂ - γ₁) * (γ₁ + γ₂) := by
  rw [fidelityGap_plateau π σ p hπ hσ hγ₂ hplate₂,
    fidelityGap_plateau π σ p hπ hσ hγ₁ hplate₁]
  ring

/-- For plateau levels at least `γ₀ > 0` and target at most `computedPmax`, the gap separation
has rate at least `2 * computedPmax π σ * (computedPmax π σ - p) * γ₀`. -/
theorem plateau_gap_rate_lower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {γ₁ γ₂ γ₀ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ₀ : 0 < γ₀)
    (hγ₁ : γ₀ ≤ γ₁) (hγ₂ : γ₀ ≤ γ₂)
    (hplate₁ : onPlateau π σ γ₁) (hplate₂ : onPlateau π σ γ₂)
    (hp : p ≤ computedPmax π σ) :
    2 * computedPmax π σ * (computedPmax π σ - p) * γ₀ * |γ₁ - γ₂|
      ≤ |fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁| := by
  have hP0 : 0 ≤ computedPmax π σ := by unfold computedPmax; positivity
  have hQ0 : 0 ≤ computedPmax π σ * (computedPmax π σ - p) :=
    mul_nonneg hP0 (sub_nonneg.mpr hp)
  have hsum0 : 0 < γ₁ + γ₂ := by linarith
  rw [plateau_gap_rate π σ p hπ hσ (hγ₀.le.trans hγ₁) (hγ₀.le.trans hγ₂) hplate₁ hplate₂]
  rw [abs_mul, abs_mul, abs_of_nonneg hQ0, abs_of_nonneg hsum0.le]
  have hnonneg : 0 ≤ (computedPmax π σ * (computedPmax π σ - p)) * |γ₂ - γ₁| :=
    mul_nonneg hQ0 (abs_nonneg _)
  have hsum : 2 * γ₀ ≤ γ₁ + γ₂ := by linarith
  have habs : |γ₁ - γ₂| = |γ₂ - γ₁| := abs_sub_swap γ₁ γ₂
  rw [habs]
  have hmul : (computedPmax π σ * (computedPmax π σ - p)) * |γ₂ - γ₁| * (2 * γ₀)
      ≤ (computedPmax π σ * (computedPmax π σ - p)) * |γ₂ - γ₁| * (γ₁ + γ₂) :=
    mul_le_mul_of_nonneg_left hsum hnonneg
  calc 2 * computedPmax π σ * (computedPmax π σ - p) * γ₀ * |γ₂ - γ₁|
      = (computedPmax π σ * (computedPmax π σ - p)) * |γ₂ - γ₁| * (2 * γ₀) := by ring
    _ ≤ (computedPmax π σ * (computedPmax π σ - p)) * |γ₂ - γ₁| * (γ₁ + γ₂) := hmul

/-- A finite minimum fold is positive when its initial value and all indexed values are
positive. -/
private theorem fold_min_pos {α : Type} [DecidableEq α] (init : ℚ) (f : α → ℚ)
    (hinit : 0 < init) : ∀ (s : Finset α), (∀ a ∈ s, 0 < f a) → 0 < s.fold min init f := by
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using! hinit
  | @insert a s ha ih =>
      intro hpos
      rw [Finset.fold_insert ha]
      have h1 : 0 < s.fold min init f := ih (fun b hb => hpos b (Finset.mem_insert_of_mem hb))
      have h2 : 0 < f a := hpos a (Finset.mem_insert_self a s)
      exact lt_min h2 h1

/-- For nonnegative source entries and positive target entries, the first breakpoint is strictly
positive. -/
theorem firstBreakpoint_pos {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ j, 0 ≤ π j)
    (hσ : ∀ j, 0 < σ j) :
    0 < firstBreakpoint π σ := by
  have hH : 0 < computedWaterHigh π σ := by
    have h := computedWaterHigh_pos π σ hπ (fun j => (hσ j).le)
    linarith
  unfold firstBreakpoint
  refine fold_min_pos _ _ hH _ ?_
  intro a ha
  have ha' := (Finset.mem_filter.mp ha).2
  exact div_pos ha' (hσ a)

/-- A candidate plateau level given by the minimum of the first breakpoint and a rate-dependent
rational bound. -/
def plateauRateWitness {m : ℕ} (π σ : Fin m → ℚ) (p c : ℚ) : ℚ :=
  min (firstBreakpoint π σ)
      (c / (16 * (computedPmax π σ * (computedPmax π σ - p))))

/-- For a target below `computedPmax`, every positive proposed rate fails to bound gap growth
uniformly from zero along the plateau, under the stated support and positivity assumptions. -/
theorem plateau_no_uniform_rate {m : ℕ} (π σ : Fin m → ℚ) (p c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hsupp : (sourceSupport π).Nonempty)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) (hc : 0 < c) :
    ∃ γ : ℚ, 0 < γ ∧ onPlateau π σ γ ∧
      |fidelityGap π σ p γ - fidelityGap π σ p 0| < c * γ := by
  have hfb : 0 < firstBreakpoint π σ := firstBreakpoint_pos π σ hπ hσ
  have hQ : 0 < computedPmax π σ * (computedPmax π σ - p) :=
    mul_pos hP (sub_pos.mpr hpp)
  have hsmall : 0 < c / (16 * (computedPmax π σ * (computedPmax π σ - p))) := by
    positivity
  have hγ0 : 0 < plateauRateWitness π σ p c := by
    unfold plateauRateWitness
    by_cases h : firstBreakpoint π σ
        ≤ c / (16 * (computedPmax π σ * (computedPmax π σ - p)))
    · rw [min_eq_left h]
      exact hfb
    · rw [min_eq_right (le_of_not_ge h)]
      exact hsmall
  have hγfb : plateauRateWitness π σ p c ≤ firstBreakpoint π σ := by
    unfold plateauRateWitness
    exact min_le_left _ _
  have hγB : plateauRateWitness π σ p c
      ≤ c / (16 * (computedPmax π σ * (computedPmax π σ - p))) := by
    unfold plateauRateWitness
    exact min_le_right _ _
  have hplate : onPlateau π σ (plateauRateWitness π σ p c) :=
    (onPlateau_iff_le π σ hπ hσ hsupp (plateauRateWitness π σ p c)).mpr hγfb
  refine ⟨plateauRateWitness π σ p c, hγ0, hplate, ?_⟩
  have hgap := fidelityGap_plateau π σ p hπ (fun j => (hσ j).le) hγ0.le hplate
  have hgap0 := fidelityGap_plateau π σ p hπ (fun j => (hσ j).le) (le_refl 0)
    (onPlateau_zero π σ hπ)
  have hnonneg : 0 ≤ plateauRateWitness π σ p c ^ 2
      * (computedPmax π σ * (computedPmax π σ - p)) := by positivity
  rw [hgap, hgap0]
  have hzero : (0 : ℚ) ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) = 0 := by ring
  rw [hzero, sub_zero, abs_of_nonneg hnonneg]
  have hQ16 : 0 < 16 * (computedPmax π σ * (computedPmax π σ - p)) :=
    mul_pos (by norm_num) hQ
  have hmul : plateauRateWitness π σ p c * (16 * (computedPmax π σ * (computedPmax π σ - p)))
      ≤ c := (le_div_iff₀ hQ16).mp hγB
  have hmul2 : plateauRateWitness π σ p c
      * (computedPmax π σ * (computedPmax π σ - p)) * 16 ≤ c := by
    have hkey : plateauRateWitness π σ p c * (16 * (computedPmax π σ * (computedPmax π σ - p)))
        = plateauRateWitness π σ p c
          * (computedPmax π σ * (computedPmax π σ - p)) * 16 := by ring
    linarith
  have hlt : plateauRateWitness π σ p c
      * (computedPmax π σ * (computedPmax π σ - p)) ≤ c / 16 :=
    (le_div_iff₀ (by norm_num : (0 : ℚ) < 16)).2 hmul2
  have hlt' : plateauRateWitness π σ p c
      * (computedPmax π σ * (computedPmax π σ - p)) < c := by linarith
  calc plateauRateWitness π σ p c ^ 2 * (computedPmax π σ * (computedPmax π σ - p))
      = plateauRateWitness π σ p c
        * (plateauRateWitness π σ p c * (computedPmax π σ * (computedPmax π σ - p))) := by ring
    _ < plateauRateWitness π σ p c * c :=
        mul_lt_mul_of_pos_left hlt' hγ0
    _ = c * plateauRateWitness π σ p c := by ring

/-- For nonnegative data, target, and level, a fidelity gap strictly larger than the ambiguity
band bound forces a `reaches` interval decision. -/
theorem intervalDecision_reaches_of_gap {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p γ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (hgap : computedDot π σ γ ^ 2 - p * computedMass π σ γ
      > ambiguityBandBound π σ b p) :
    intervalDecision b π σ p γ = .reaches := by
  have hbw := intervalBandWidth_le_resolution π σ b p γ hπ hσ hγ hp
  have hbw' : intervalBandWidth b π σ p γ ≤ ambiguityBandBound π σ b p := by
    simpa [ambiguityBandBound] using! hbw
  have hhi := intervalBand_upper π σ b p γ hπ hσ hγ hp
  have hkey : intervalBandWidth b π σ p γ
      = (computedDotUp b π σ γ ^ 2 - p * computedMassDown b π σ γ)
        - (computedDotDown b π σ γ ^ 2 - p * computedMassUp b π σ γ) := by
    unfold intervalBandWidth
    ring
  have hdown : 0 ≤ computedDotDown b π σ γ ^ 2 - p * computedMassUp b π σ γ := by
    have h1 : intervalBandWidth b π σ p γ
        < computedDot π σ γ ^ 2 - p * computedMass π σ γ := by linarith [hbw', hgap]
    have h2 : computedDotDown b π σ γ ^ 2 - p * computedMassUp b π σ γ
        = (computedDotUp b π σ γ ^ 2 - p * computedMassDown b π σ γ)
          - intervalBandWidth b π σ p γ := by rw [hkey]; ring
    linarith [hhi, h2]
  exact (intervalDecision_spec π σ b p γ).1.mpr (sub_nonneg.mp hdown)

/-- The ambiguity band bound divided by the plateau gap coefficient, used as a bound on squared
ambiguous plateau levels. -/
def plateauAmbiguityLevel {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) : ℚ :=
  ambiguityBandBound π σ b p / (computedPmax π σ * (computedPmax π σ - p))

/-- For a target below positive `computedPmax`, an ambiguous nonnegative plateau level has
square at most `plateauAmbiguityLevel`. -/
theorem plateau_ambiguity_confined {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) {γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hg : 0 ≤ γ) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ)
    (hplate : onPlateau π σ γ)
    (hamb : intervalDecision b π σ p γ = .ambiguous) :
    γ ^ 2 ≤ plateauAmbiguityLevel π σ b p := by
  have hgap := intervalAmbiguity_gap_le π σ b p hπ hσ hg hp hamb
  have hplateau := fidelityGap_plateau π σ p hπ hσ hg hplate
  have hPP : 0 < computedPmax π σ * (computedPmax π σ - p) :=
    mul_pos hP (sub_pos.mpr hpp)
  have hkey : fidelityGap π σ p γ
      = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := hplateau
  rw [hkey] at hgap
  have habs : 0 ≤ γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by positivity
  rw [abs_of_nonneg habs] at hgap
  unfold plateauAmbiguityLevel
  rw [le_div_iff₀ hPP]
  linarith

/-- If the plateau ambiguity bound is below `γ₀ ^ 2`, every plateau level strictly above `γ₀ >
0` receives a `reaches` decision. -/
theorem plateau_resolved_above {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) {γ₀ γ : ℚ}
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ)
    (hγ₀ : 0 < γ₀) (hγ : γ₀ < γ) (hplate : onPlateau π σ γ)
    (hres : plateauAmbiguityLevel π σ b p < γ₀ ^ 2) :
    intervalDecision b π σ p γ = .reaches := by
  have hPP : 0 < computedPmax π σ * (computedPmax π σ - p) :=
    mul_pos hP (sub_pos.mpr hpp)
  have hgap : computedDot π σ γ ^ 2 - p * computedMass π σ γ
      > ambiguityBandBound π σ b p := by
    have hplateau := fidelityGap_plateau π σ p hπ hσ (hγ₀.le.trans hγ.le) hplate
    have hkey : computedDot π σ γ ^ 2 - p * computedMass π σ γ
        = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by
      unfold fidelityGap at hplateau
      exact hplateau
    have hsq : γ₀ ^ 2 < γ ^ 2 := by
      have hlt : 0 < γ - γ₀ := by linarith
      have hpos : 0 < γ + γ₀ := by linarith
      nlinarith [mul_pos hlt hpos]
    have hB : ambiguityBandBound π σ b p
        < γ₀ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by
      unfold plateauAmbiguityLevel at hres
      rw [div_lt_iff₀ hPP] at hres
      linarith
    rw [hkey]
    nlinarith [hB, hsq]
  exact intervalDecision_reaches_of_gap π σ b p γ hπ hσ (hγ₀.le.trans hγ.le) hp hgap

/-- An ambiguous nonnegative plateau level is at most `max γ₀ (plateauAmbiguityLevel π σ b p /
γ₀)` for any positive `γ₀`, under the stated target assumptions. -/
theorem plateau_ambiguity_level_bound {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    {γ₀ γ : ℚ} (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hg : 0 ≤ γ)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) (hγ₀ : 0 < γ₀)
    (hplate : onPlateau π σ γ)
    (hamb : intervalDecision b π σ p γ = .ambiguous) :
    γ ≤ max γ₀ (plateauAmbiguityLevel π σ b p / γ₀) := by
  have hconf := plateau_ambiguity_confined π σ b p hπ hσ hg hp hP hpp hplate hamb
  by_cases h : γ < γ₀
  · exact le_max_of_le_left (le_of_lt h)
  · have hγpos : 0 < γ := lt_of_lt_of_le hγ₀ (le_of_not_gt h)
    have hmul : γ * γ₀ ≤ plateauAmbiguityLevel π σ b p := by
      have : γ * γ₀ ≤ γ ^ 2 := by
        have : γ₀ ≤ γ := le_of_not_gt h
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hγpos)) (le_of_lt hγpos)]
      linarith
    have hdiv : γ ≤ plateauAmbiguityLevel π σ b p / γ₀ :=
      (le_div_iff₀ hγ₀).2 hmul
    exact le_max_of_le_right hdiv

/-- The dyadic grid spacing is antitone in precision. -/
theorem gridStep_mono {b b' : ℕ} (h : b ≤ b') : gridStep b' ≤ gridStep b := by
  have h1 : (2 : ℚ) ^ b ≤ (2 : ℚ) ^ b' := two_pow_le h
  have hp : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  unfold gridStep
  exact div_le_div_of_nonneg_left (by norm_num) hp h1

/-- For nonnegative data and target, the ambiguity band bound is antitone in grid precision. -/
theorem ambiguityBandBound_mono {m : ℕ} (π σ : Fin m → ℚ) (b b' : ℕ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) (h : b ≤ b') :
    ambiguityBandBound π σ b' p ≤ ambiguityBandBound π σ b p := by
  have hstep : gridStep b' ≤ gridStep b := gridStep_mono h
  have hsum : 0 ≤ ∑ j, π j * σ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
  have hM0 : 0 ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
  have hM : (m : ℚ) * (gridStep b') ≤ (m : ℚ) * (gridStep b) :=
    mul_le_mul_of_nonneg_left hstep hM0
  have hA : 2 * (m : ℚ) * (gridStep b') ≤ 2 * (m : ℚ) * (gridStep b) := by nlinarith
  have hbracket : 2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b') + p
      ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p := by linarith
  have hbracket0 : 0 ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b') + p := by
    have h1 : 0 ≤ (m : ℚ) * (gridStep b') :=
      mul_nonneg hM0 (gridStep_pos b').le
    linarith
  unfold ambiguityBandBound
  calc 2 * (m : ℚ) * (gridStep b') * (2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b') + p)
      ≤ 2 * (m : ℚ) * (gridStep b) * (2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b') + p) :=
        mul_le_mul_of_nonneg_right hA hbracket0
    _ ≤ 2 * (m : ℚ) * (gridStep b) * (2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p) :=
        mul_le_mul_of_nonneg_left hbracket
          (mul_nonneg (mul_nonneg (by norm_num) hM0) (gridStep_pos b).le)

/-- When the grid spacing is at most one, bounds the ambiguity band by a linear expression in
that spacing. -/
theorem ambiguityBandBound_le_of_step {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    (hu : gridStep b ≤ 1) :
    ambiguityBandBound π σ b p
      ≤ 2 * (m : ℚ) * (gridStep b) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) := by
  unfold ambiguityBandBound
  have hbracket : 2 * (∑ j, π j * σ j) + (m : ℚ) * (gridStep b) + p
      ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) + p := by
    have hM0 : 0 ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : (m : ℚ) * (gridStep b) ≤ (m : ℚ) * 1 :=
      mul_le_mul_of_nonneg_left hu hM0
    linarith
  have hnonneg : 0 ≤ 2 * (m : ℚ) * (gridStep b) :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le m)))
      (gridStep_pos b).le
  exact mul_le_mul_of_nonneg_left hbracket hnonneg

/-- The condition that the ambiguity band bound is at most the plateau gap coefficient times `γ₀
^ 2`. -/
def plateauResolutionSufficient {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (γ₀ : ℚ) : Prop :=
  ambiguityBandBound π σ b p ≤ computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2

/-- For nonnegative data and target, increasing grid precision preserves
`plateauResolutionSufficient`. -/
theorem plateauResolution_mono {m : ℕ} (π σ : Fin m → ℚ) (b b' : ℕ) (p : ℚ) (γ₀ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (h : b ≤ b') (hs : plateauResolutionSufficient π σ b p γ₀) :
    plateauResolutionSufficient π σ b' p γ₀ := by
  unfold plateauResolutionSufficient at *
  exact le_trans (ambiguityBandBound_mono π σ b b' p hπ hσ hp h) hs

/-- For a target below positive `computedPmax` and `γ₀ > 0`, some precision at least the given
precision satisfies `plateauResolutionSufficient`. -/
theorem exists_plateauResolution {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (γ₀ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) (hγ₀ : 0 < γ₀) :
    ∃ b' : ℕ, b' ≥ b ∧ plateauResolutionSufficient π σ b' p γ₀ := by
  have hT : 0 < computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2 := by
    have h1 : 0 < computedPmax π σ * (computedPmax π σ - p) :=
      mul_pos hP (sub_pos.mpr hpp)
    nlinarith [sq_pos_of_pos hγ₀]
  have hsum : 0 ≤ ∑ j, π j * σ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
  have hM0 : 0 ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
  have hC : 0 ≤ 2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) := by
    have h1 : 0 ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) + p := by linarith
    nlinarith
  have hC1 : 0 < 2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1 := by linarith
  have hu : 0 < min 1 (computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2
      / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1)) := by
    have hdiv : 0 < computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2
        / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1) :=
      div_pos hT hC1
    exact lt_min one_pos hdiv
  obtain ⟨b'', hb''⟩ := exists_bitBudget hu
  refine ⟨max b b'', le_max_left _ _, ?_⟩
  have hgs : gridStep (max b b'') ≤ gridStep b'' := gridStep_mono (le_max_right _ _)
  have hgs1 : gridStep (max b b'') ≤ 1 := le_trans hgs (le_trans hb'' (min_le_left _ _))
  have hgsT : gridStep (max b b'')
      ≤ computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2
        / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1) :=
    le_trans hgs (le_trans hb'' (min_le_right _ _))
  have hband := ambiguityBandBound_le_of_step π σ (max b b'') p hgs1
  have hCu : (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
      * (gridStep (max b b''))
      ≤ (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
        * (computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2
          / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1)) :=
    mul_le_mul_of_nonneg_left hgsT hC
  have hCT : (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
      * (computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2
        / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1))
      ≤ computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2 := by
    have hfrac : (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
        / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1) ≤ 1 := by
      exact (div_le_iff₀ hC1).2 (by linarith)
    have hnonneg : 0 ≤ computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2 := hT.le
    calc (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
        * (computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2
          / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1))
        = ((2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
          / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) + 1))
            * (computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2) := by ring
      _ ≤ 1 * (computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2) :=
          mul_le_mul_of_nonneg_right hfrac hT.le
      _ = computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2 := by ring
  have hshape : 2 * (m : ℚ) * (gridStep (max b b''))
        * (2 * (∑ j, π j * σ j) + (m : ℚ) + p)
      = (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p)) * (gridStep (max b b'')) := by
    ring
  have hfinal : 2 * (m : ℚ) * (gridStep (max b b''))
        * (2 * (∑ j, π j * σ j) + (m : ℚ) + p)
      ≤ computedPmax π σ * (computedPmax π σ - p) * γ₀ ^ 2 := by
    rw [hshape]
    exact le_trans hCu hCT
  unfold plateauResolutionSufficient
  exact le_trans hband hfinal

/-- The ambiguous search levels that also satisfy the plateau condition. -/
def ambiguousPlateauLevels {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : Finset ℚ :=
  (ambiguousLevels b π σ p k).filter (fun γ => onPlateau π σ γ)

/-- The ambiguous plateau search levels at least a specified threshold `γ₀`. -/
def ambiguousPlateauLevelsAbove {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (γ₀ : ℚ) : Finset ℚ :=
  (ambiguousPlateauLevels b π σ p k).filter (fun γ => γ₀ ≤ γ)

/-- There are no more ambiguous plateau levels than ambiguous search levels. -/
theorem ambiguousPlateauLevels_card_le {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) :
    (ambiguousPlateauLevels b π σ p k).card ≤ (ambiguousLevels b π σ p k).card := by
  unfold ambiguousPlateauLevels
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Distinct ambiguous plateau levels from the first `k` refinements are separated by at least
`computedWaterHigh π σ / 2 ^ k`. -/
theorem ambiguousPlateauLevels_separation {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {x y : ℚ}
    (hx : x ∈ ambiguousPlateauLevels b π σ p k) (hy : y ∈ ambiguousPlateauLevels b π σ p k)
    (hne : x ≠ y) :
    computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| := by
  unfold ambiguousPlateauLevels at hx hy
  have hx' := (Finset.mem_filter.mp hx).1
  have hy' := (Finset.mem_filter.mp hy).1
  exact ambiguousLevels_separation b π σ p k hπ hσ hx' hy' hne

/-- Above `γ₀ > 0`, ambiguous plateau levels have diameter at most the ambiguity band bound
divided by the plateau gap coefficient times `γ₀`. -/
theorem ambiguousPlateauLevels_diam {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ)
    (γ₀ : ℚ) (hγ₀ : 0 < γ₀)
    {x y : ℚ} (hx : x ∈ ambiguousPlateauLevels b π σ p k)
    (hy : y ∈ ambiguousPlateauLevels b π σ p k)
    (hx₀ : γ₀ ≤ x) (hy₀ : γ₀ ≤ y) :
    |x - y| ≤ ambiguityBandBound π σ b p
        / (computedPmax π σ * (computedPmax π σ - p) * γ₀) := by
  unfold ambiguousPlateauLevels at hx hy
  have hxmem := Finset.mem_filter.mp hx
  have hymem := Finset.mem_filter.mp hy
  have hxamb : intervalDecision b π σ p x = .ambiguous := by
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp hxmem.1
    rw [← hj']
    exact (Finset.mem_filter.mp hj).2
  have hyamb : intervalDecision b π σ p y = .ambiguous := by
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp hymem.1
    rw [← hj']
    exact (Finset.mem_filter.mp hj).2
  have hrate := plateau_gap_rate_lower π σ p hπ hσ hγ₀ hx₀ hy₀ hxmem.2 hymem.2 hpp.le
  have hxnonneg : 0 ≤ x := hγ₀.le.trans hx₀
  have hynonneg : 0 ≤ y := hγ₀.le.trans hy₀
  have hpair := intervalAmbiguity_gap_pair π σ b p hπ hσ hp hxnonneg hynonneg hxamb hyamb
  have hpair' : |fidelityGap π σ p y - fidelityGap π σ p x|
      ≤ 2 * ambiguityBandBound π σ b p := by
    rw [abs_sub_comm]
    exact hpair
  have hQ : 0 < computedPmax π σ * (computedPmax π σ - p) :=
    mul_pos hP (sub_pos.mpr hpp)
  have hQ0 : 0 < computedPmax π σ * (computedPmax π σ - p) * γ₀ := mul_pos hQ hγ₀
  have h1 : 2 * computedPmax π σ * (computedPmax π σ - p) * γ₀ * |x - y|
      ≤ 2 * ambiguityBandBound π σ b p := le_trans hrate hpair'
  have h1' : |x - y| * (computedPmax π σ * (computedPmax π σ - p) * γ₀) * 2
      ≤ ambiguityBandBound π σ b p * 2 := by
    have hkey : |x - y| * (computedPmax π σ * (computedPmax π σ - p) * γ₀) * 2
        = 2 * computedPmax π σ * (computedPmax π σ - p) * γ₀ * |x - y| := by ring
    have hkey2 : ambiguityBandBound π σ b p * 2 = 2 * ambiguityBandBound π σ b p := by ring
    rw [hkey, hkey2]
    exact h1
  rw [le_div_iff₀ hQ0]
  exact le_of_mul_le_mul_right h1' (by norm_num)

/-- Bounds the number of ambiguous plateau levels above `γ₀ > 0` using their diameter and dyadic
separation. -/
theorem ambiguousPlateauLevelsAbove_count_le {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ)
    (k : ℕ) (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ)
    (γ₀ : ℚ) (hγ₀ : 0 < γ₀) :
    (ambiguousPlateauLevelsAbove b π σ p k γ₀).card
      ≤ Nat.floor (ambiguityBandBound π σ b p
          / (computedPmax π σ * (computedPmax π σ - p) * γ₀)
          * (2 : ℚ) ^ k / computedWaterHigh π σ) + 1 := by
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  have hsp : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k :=
    div_pos hH (by positivity)
  have hsep : ∀ x ∈ ambiguousPlateauLevelsAbove b π σ p k γ₀,
      ∀ y ∈ ambiguousPlateauLevelsAbove b π σ p k γ₀, x ≠ y →
        computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| := by
    intro x hx y hy hne
    unfold ambiguousPlateauLevelsAbove at hx hy
    have hx' := (Finset.mem_filter.mp hx).1
    have hy' := (Finset.mem_filter.mp hy).1
    exact ambiguousPlateauLevels_separation b π σ p k hπ hσ hx' hy' hne
  have hdiam : ∀ x ∈ ambiguousPlateauLevelsAbove b π σ p k γ₀,
      ∀ y ∈ ambiguousPlateauLevelsAbove b π σ p k γ₀,
        |x - y| ≤ ambiguityBandBound π σ b p
          / (computedPmax π σ * (computedPmax π σ - p) * γ₀) := by
    intro x hx y hy
    unfold ambiguousPlateauLevelsAbove at hx hy
    have hx' := (Finset.mem_filter.mp hx).1
    have hy' := (Finset.mem_filter.mp hy).1
    have hx0 := (Finset.mem_filter.mp hx).2
    have hy0 := (Finset.mem_filter.mp hy).2
    exact ambiguousPlateauLevels_diam b π σ p k hπ hσ hp hP hpp γ₀ hγ₀
      hx' hy' hx0 hy0
  have hbound := Finset.card_le_of_separated_diam
    (ambiguousPlateauLevelsAbove b π σ p k γ₀)
    (computedWaterHigh π σ / (2 : ℚ) ^ k)
    (ambiguityBandBound π σ b p
      / (computedPmax π σ * (computedPmax π σ - p) * γ₀))
    hsp hsep hdiam
  have hconv : (ambiguityBandBound π σ b p
      / (computedPmax π σ * (computedPmax π σ - p) * γ₀))
      / (computedWaterHigh π σ / (2 : ℚ) ^ k)
      = (ambiguityBandBound π σ b p
        / (computedPmax π σ * (computedPmax π σ - p) * γ₀))
        * (2 : ℚ) ^ k / computedWaterHigh π σ :=
    div_grid hH k
  rw [hconv] at hbound
  exact hbound

/-- A positive band rate bounds the actual interval operation count by the count obtained from
the width-based ambiguity estimate. -/
theorem intervalRunOperationCount_le_of_width {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    (k : ℕ) (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (c : ℚ) (hc : 0 < c) (hrate : bandRate π σ b p c k) :
    intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities
      ≤ intervalRunOperationCount m k (Nat.floor (2 * ambiguityBandBound π σ b p / c
          * (2 : ℚ) ^ k / computedWaterHigh π σ) + 1) := by
  have hcount := ambiguityCount_le b π σ p k hπ hσ hp c hc hrate
  exact intervalRunOperationCount_mono m k hcount

/-- The floor of the squared-level ambiguity bound divided by squared dyadic separation, plus
one. -/
def plateauAmbiguityCountBound {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (k : ℕ) : ℕ :=
  Nat.floor (plateauAmbiguityLevel π σ b p
      / (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2) + 1

/-- Every ambiguous plateau search level is nonnegative and has square at most
`plateauAmbiguityLevel`, under the stated target and positivity assumptions. -/
theorem ambiguousPlateauLevels_bound {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) :
    ∀ x ∈ ambiguousPlateauLevels b π σ p k,
      0 ≤ x ∧ x ^ 2 ≤ plateauAmbiguityLevel π σ b p := by
  intro x hx
  unfold ambiguousPlateauLevels at hx
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp hx'.1
  have hamb : intervalDecision b π σ p (bracketMidpoint π σ p j) = .ambiguous :=
    (Finset.mem_filter.mp hj).2
  have hplate : onPlateau π σ (bracketMidpoint π σ p j) := by
    rw [hj']
    exact hx'.2
  have hγ : 0 ≤ bracketMidpoint π σ p j := by
    have hb := fidelityBracket_bounds π σ p j hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  have hconf := plateau_ambiguity_confined π σ b p hπ hσ hγ hp hP hpp hplate hamb
  rw [← hj']
  exact ⟨hγ, hconf⟩

/-- If the plateau squared-level ambiguity bound is below the squared dyadic separation, at most
one plateau search level is ambiguous. -/
theorem ambiguousPlateauLevels_card_le_one {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ)
    (hlt : plateauAmbiguityLevel π σ b p < (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2) :
    (ambiguousPlateauLevels b π σ p k).card ≤ 1 := by
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  have hu : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k := div_pos hH (by positivity)
  have hbound := ambiguousPlateauLevels_bound b π σ p k hπ hσ hp hP hpp
  have hsep : ∀ x ∈ ambiguousPlateauLevels b π σ p k,
      ∀ y ∈ ambiguousPlateauLevels b π σ p k, x ≠ y →
        computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| := by
    intro x hx y hy hne
    exact ambiguousPlateauLevels_separation b π σ p k hπ hσ hx hy hne
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  by_contra hne
  have hx0 := hbound x hx
  have hy0 := hbound y hy
  have hsep' := hsep x hx y hy hne
  rcases le_total x y with hxy | hyx
  · have huy : computedWaterHigh π σ / (2 : ℚ) ^ k ≤ y := by
      have habs : |x - y| = y - x := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
      rw [habs] at hsep'
      linarith
    have hsq : (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 ≤ y ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hu.le huy
    linarith
  · have hux : computedWaterHigh π σ / (2 : ℚ) ^ k ≤ x := by
      have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hyx)
      rw [habs] at hsep'
      linarith
    have hsq : (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 ≤ x ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hu.le hux
    linarith

/-- The number of ambiguous plateau search levels is at most `plateauAmbiguityCountBound` under
the stated positivity and target assumptions. -/
theorem ambiguousPlateauLevels_count_le {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) :
    (ambiguousPlateauLevels b π σ p k).card ≤ plateauAmbiguityCountBound π σ b p k := by
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  have hu : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k := div_pos hH (by positivity)
  have hu2 : 0 < (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 := by positivity
  have hT0 : 0 ≤ plateauAmbiguityLevel π σ b p := by
    unfold plateauAmbiguityLevel
    have hB : 0 ≤ ambiguityBandBound π σ b p := by
      unfold ambiguityBandBound
      have hgrid : 0 ≤ gridStep b := by unfold gridStep; positivity
      have hsum : 0 ≤ ∑ j, π j * σ j :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
      have h1 : 0 ≤ 2 * (m : ℚ) * gridStep b := by positivity
      have h2 : 0 ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) * gridStep b + p := by linarith
      exact mul_nonneg h1 h2
    have hQ : 0 < computedPmax π σ * (computedPmax π σ - p) :=
      mul_pos hP (sub_pos.mpr hpp)
    exact div_nonneg hB hQ.le
  have hT0' : 0 ≤ plateauAmbiguityLevel π σ b p
      / (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 :=
    div_nonneg hT0 hu2.le
  by_cases hcase : plateauAmbiguityLevel π σ b p
      < (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2
  · have hone := ambiguousPlateauLevels_card_le_one b π σ p k hπ hσ hp hP hpp hcase
    have hq : plateauAmbiguityLevel π σ b p
        / (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 < 1 := by
      rw [div_lt_one hu2]
      exact hcase
    have hfloor : Nat.floor (plateauAmbiguityLevel π σ b p
        / (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2) = 0 := by
      have hnot : ¬ (1 ≤ Nat.floor (plateauAmbiguityLevel π σ b p
          / (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2)) := by
        intro hb
        have hb' := (Nat.le_floor_iff (n := 1) hT0').mp hb
        norm_num at hb'
        linarith
      omega
    unfold plateauAmbiguityCountBound
    rw [hfloor]
    omega
  · have hge : (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2
        ≤ plateauAmbiguityLevel π σ b p := not_lt.mp hcase
    have hbound := ambiguousPlateauLevels_bound b π σ p k hπ hσ hp hP hpp
    have hsep : ∀ x ∈ ambiguousPlateauLevels b π σ p k,
        ∀ y ∈ ambiguousPlateauLevels b π σ p k, x ≠ y →
          computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| := by
      intro x hx y hy hne
      exact ambiguousPlateauLevels_separation b π σ p k hπ hσ hx hy hne
    have hcap : ∀ x ∈ ambiguousPlateauLevels b π σ p k,
        x ≤ plateauAmbiguityLevel π σ b p / (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
      intro x hx
      have hx0 := hbound x hx
      by_cases hlow : x < computedWaterHigh π σ / (2 : ℚ) ^ k
      · have huu : computedWaterHigh π σ / (2 : ℚ) ^ k
            ≤ plateauAmbiguityLevel π σ b p / (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
          rw [le_div_iff₀ hu]
          nlinarith [hge]
        exact le_trans hlow.le huu
      · have hxu : computedWaterHigh π σ / (2 : ℚ) ^ k ≤ x := le_of_not_gt hlow
        have hmul : x * (computedWaterHigh π σ / (2 : ℚ) ^ k) ≤ x ^ 2 := by
          have h1 : 0 ≤ x := hx0.1
          nlinarith [mul_nonneg (sub_nonneg.mpr hxu) h1]
        have h3 : x * (computedWaterHigh π σ / (2 : ℚ) ^ k)
            ≤ plateauAmbiguityLevel π σ b p := le_trans hmul hx0.2
        exact (le_div_iff₀ hu).2 h3
    have hdiam : ∀ x ∈ ambiguousPlateauLevels b π σ p k,
        ∀ y ∈ ambiguousPlateauLevels b π σ p k,
          |x - y| ≤ plateauAmbiguityLevel π σ b p
            / (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
      intro x hx y hy
      have hx' := hcap x hx
      have hy' := hcap y hy
      have hx0 := hbound x hx
      have hy0 := hbound y hy
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hcard := Finset.card_le_of_separated_diam (ambiguousPlateauLevels b π σ p k)
      (computedWaterHigh π σ / (2 : ℚ) ^ k)
      (plateauAmbiguityLevel π σ b p / (computedWaterHigh π σ / (2 : ℚ) ^ k))
      hu hsep hdiam
    have hkey : (plateauAmbiguityLevel π σ b p / (computedWaterHigh π σ / (2 : ℚ) ^ k))
        / (computedWaterHigh π σ / (2 : ℚ) ^ k)
        = plateauAmbiguityLevel π σ b p / (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 := by
      rw [div_div, pow_two]
    rw [hkey] at hcard
    unfold plateauAmbiguityCountBound
    exact hcard

/-- The strict condition that the ambiguity band bound is below the plateau gap coefficient
times squared dyadic separation. -/
def plateauResolutionCriterion {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (k : ℕ) : Prop :=
  ambiguityBandBound π σ b p
    < computedPmax π σ * (computedPmax π σ - p) * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2

/-- The plateau resolution criterion ensures at most one ambiguous plateau search level under
the stated positivity and target assumptions. -/
theorem plateau_resolution_criterion_sufficient {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ)
    (hc : plateauResolutionCriterion π σ b p k) :
    (ambiguousPlateauLevels b π σ p k).card ≤ 1 := by
  have hQ : 0 < computedPmax π σ * (computedPmax π σ - p) :=
    mul_pos hP (sub_pos.mpr hpp)
  have hlt : plateauAmbiguityLevel π σ b p
      < (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 := by
    unfold plateauAmbiguityLevel
    rw [div_lt_iff₀ hQ]
    have hkey : (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2
        * (computedPmax π σ * (computedPmax π σ - p))
        = (computedPmax π σ * (computedPmax π σ - p))
          * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 := mul_comm _ _
    exact lt_of_lt_of_le hc (le_of_eq hkey.symm)
  exact ambiguousPlateauLevels_card_le_one b π σ p k hπ hσ hp hP hpp hlt

/-- A rational grid-spacing allowance obtained by dividing half the plateau separation threshold
by a linear ambiguity-band coefficient. -/
def plateauJointResolution {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : ℚ :=
  (computedPmax π σ * (computedPmax π σ - p)
      * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 / 2)
    / (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))

/-- For a target below positive `computedPmax` and positive table size, sufficiently increasing
precision satisfies the plateau resolution criterion. -/
theorem exists_plateauJointResolution {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) (hm : 0 < m) :
    ∃ b' : ℕ, b' ≥ b ∧ plateauResolutionCriterion π σ b' p k := by
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  have hQ : 0 < computedPmax π σ * (computedPmax π σ - p) :=
    mul_pos hP (sub_pos.mpr hpp)
  have hsum : 0 ≤ ∑ j, π j * σ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
  have hM0 : 0 ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
  have hM0' : 0 < (m : ℚ) := by exact_mod_cast hm
  have hC : 0 < 2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p) := by
    have h1 : 0 ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) + p := by linarith
    nlinarith [hM0']
  have hX : 0 < plateauJointResolution π σ p k := by
    unfold plateauJointResolution
    have h1 : 0 < computedPmax π σ * (computedPmax π σ - p)
        * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 / 2 := by
      have h2 : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k :=
        div_pos hH (by positivity)
      positivity
    exact div_pos h1 hC
  obtain ⟨b'', hb''⟩ := exists_bitBudget (lt_min one_pos hX)
  refine ⟨max b b'', le_max_left _ _, ?_⟩
  have hgs : gridStep (max b b'') ≤ gridStep b'' := gridStep_mono (le_max_right _ _)
  have hgs1 : gridStep (max b b'') ≤ 1 := le_trans hgs (le_trans hb'' (min_le_left _ _))
  have hgsX : gridStep (max b b'') ≤ plateauJointResolution π σ p k :=
    le_trans hgs (le_trans hb'' (min_le_right _ _))
  have hmul : gridStep (max b b'') * (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p))
      ≤ (computedPmax π σ * (computedPmax π σ - p)
          * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2) / 2 := by
    unfold plateauJointResolution at hgsX
    exact (le_div_iff₀ hC).1 hgsX
  have hband := ambiguityBandBound_le_of_step π σ (max b b'') p hgs1
  have hkey : 2 * (m : ℚ) * (gridStep (max b b''))
        * (2 * (∑ j, π j * σ j) + (m : ℚ) + p)
      = gridStep (max b b'')
        * (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p)) := by
    ring
  have hband' : ambiguityBandBound π σ (max b b'') p
      ≤ gridStep (max b b'')
        * (2 * (m : ℚ) * (2 * (∑ j, π j * σ j) + (m : ℚ) + p)) := by
    rw [← hkey]
    exact hband
  have hpos : 0 < computedPmax π σ * (computedPmax π σ - p)
      * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 := by
    have h1 : 0 < computedPmax π σ * (computedPmax π σ - p) := hQ
    have h2 : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k := div_pos hH (by positivity)
    positivity
  have hlt : (computedPmax π σ * (computedPmax π σ - p)
      * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2) / 2
      < computedPmax π σ * (computedPmax π σ - p)
        * (computedWaterHigh π σ / (2 : ℚ) ^ k) ^ 2 := by linarith
  unfold plateauResolutionCriterion
  exact lt_of_le_of_lt (le_trans hband' hmul) hlt

/-- The conjunction of the operation bit budget condition and the plateau resolution criterion
at fixed search depth and operation count. -/
def jointTerminationSufficient {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p ε πi : ℚ) (k n : ℕ) : Prop :=
  gridStep b ≤ opBitBudget ε p πi n ∧ plateauResolutionCriterion π σ b p k

/-- For nonnegative data and target, increasing precision preserves the plateau resolution
criterion. -/
theorem plateauResolutionCriterion_mono {m : ℕ} (π σ : Fin m → ℚ) (b b' : ℕ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) (h : b ≤ b')
    (hc : plateauResolutionCriterion π σ b p k) :
    plateauResolutionCriterion π σ b' p k := by
  unfold plateauResolutionCriterion at *
  exact lt_of_le_of_lt (ambiguityBandBound_mono π σ b b' p hπ hσ hp h) hc

/-- Under the stated positivity assumptions and a target below `computedPmax`, some precision
satisfies both the operation bit budget and plateau resolution criterion. -/
theorem exists_jointTermination {m : ℕ} (π σ : Fin m → ℚ) (p ε πi : ℚ) (k n : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 < p) (hε : 0 < ε) (hπi : 0 < πi)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) (hm : 0 < m) (hn : 0 < n) :
    ∃ b : ℕ, jointTerminationSufficient π σ b p ε πi k n := by
  obtain ⟨b1, hb1⟩ := exists_opBitBudgetSufficient hn hε hp hπi
  obtain ⟨b2, hb2⟩ := exists_plateauJointResolution 0 π σ p k hπ hσ hp.le hP hpp hm
  refine ⟨max b1 b2, ⟨?_, ?_⟩⟩
  · exact le_trans (gridStep_mono (le_max_left _ _)) hb1
  · exact plateauResolutionCriterion_mono π σ b2 (max b1 b2) p k hπ hσ hp.le
      (le_max_right _ _) hb2.2

/-- The joint termination condition bounds accumulated amplitude and mass error allowances and
ensures at most one ambiguous plateau level. -/
theorem jointTermination_certifies {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p ε πi : ℚ) (k n : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 < p) (hε : 0 < ε) (hπi : 0 < πi)
    (hP : 0 < computedPmax π σ) (hpp : p < computedPmax π σ) (hn : 0 < n)
    (hj : jointTerminationSufficient π σ b p ε πi k n) :
    (n : ℚ) * (gridStep b / 2) / πi ≤ ε * πi / p ∧
      (n : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2 ∧
      (ambiguousPlateauLevels b π σ p k).card ≤ 1 := by
  obtain ⟨hbits, hcrit⟩ := hj
  obtain ⟨h1, h2⟩ := opBitBudget_sufficient hn hε hp hπi b hbits
  exact ⟨h1, h2,
    plateau_resolution_criterion_sufficient b π σ p k hπ hσ hp.le hP hpp hcrit⟩

/-- The condition that every newly saturated index in `S₂ \ S₁` has a positive source entry
meeting its target-scaled value at the boundary level. -/
def pieceBreak {m : ℕ} (π σ : Fin m → ℚ) (γb : ℚ) (S₁ S₂ : Finset (Fin m)) : Prop :=
  ∀ j ∈ S₂ \ S₁, 0 < π j ∧ π j = γb * σ j

/-- The fidelity-gap polynomial associated with a chosen saturation set, built from its
saturated dot and mass contributions and free squared target mass. -/
def pieceGap {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S : Finset (Fin m)) (γ : ℚ) : ℚ :=
  (satDot π σ S + γ * freeSq π σ S) ^ 2 - p * (satMass π S + γ ^ 2 * freeSq π σ S)

/-- At a nonnegative level with saturation set `S`, the exact fidelity gap equals `pieceGap π σ
p S γ` for nonnegative data. -/
theorem fidelityGap_eq_pieceGap {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (γ : ℚ) (S : Finset (Fin m))
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hγ : 0 ≤ γ)
    (hpat : satSet π σ γ = S) :
    fidelityGap π σ p γ = pieceGap π σ p S γ := by
  have hD := computedDot_piece π σ S hπ hσ hγ hpat
  have hM := computedMass_piece π σ S hπ hσ hγ hpat
  unfold fidelityGap pieceGap
  rw [hD, hM]

/-- The difference of two values of a fixed piece gap factors as the level difference times its
secant slope. -/
theorem pieceGap_diff {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S : Finset (Fin m)) (γ₁ γ₂ : ℚ) :
    pieceGap π σ p S γ₂ - pieceGap π σ p S γ₁
      = (γ₂ - γ₁) * (freeSq π σ S * (freeSq π σ S - p) * (γ₁ + γ₂)
          + 2 * satDot π σ S * freeSq π σ S) := by
  unfold pieceGap
  ring

/-- Expresses the piecewise dot formula as a sum of saturated source-target products and free
target-square contributions. -/
private theorem pieceOverlap_eq_sum {m : ℕ} (π σ : Fin m → ℚ) (S : Finset (Fin m)) (γ : ℚ) :
    satDot π σ S + γ * freeSq π σ S
      = ∑ j : Fin m, (if j ∈ S then σ j * π j
          else γ * (if 0 < π j then σ j ^ 2 else 0)) := by
  unfold satDot freeSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj]

/-- Expresses the piecewise mass formula as a sum of saturated source squares and free
level-scaled target squares. -/
private theorem pieceMass_eq_sum {m : ℕ} (π σ : Fin m → ℚ) (S : Finset (Fin m)) (γ : ℚ) :
    satMass π S + γ ^ 2 * freeSq π σ S
      = ∑ j : Fin m, (if j ∈ S then π j ^ 2
          else γ ^ 2 * (if 0 < π j then σ j ^ 2 else 0)) := by
  unfold satMass freeSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj]

/-- Nested saturation sets satisfying `pieceBreak` give identical piecewise dot and mass
formulas at the boundary level. -/
theorem piece_agreement_at_boundary {m : ℕ} (π σ : Fin m → ℚ) (S₁ S₂ : Finset (Fin m)) (γb : ℚ)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂) :
    satDot π σ S₁ + γb * freeSq π σ S₁ = satDot π σ S₂ + γb * freeSq π σ S₂ ∧
    satMass π S₁ + γb ^ 2 * freeSq π σ S₁ = satMass π S₂ + γb ^ 2 * freeSq π σ S₂ := by
  have hpos : ∀ j ∈ S₂ \ S₁, 0 < π j := fun j hj => (hbrk j hj).1
  have hagree : ∀ j ∈ S₂ \ S₁, π j = γb * σ j := fun j hj => (hbrk j hj).2
  have hdotpoint : ∀ j : Fin m,
      (if j ∈ S₁ then σ j * π j else γb * (if 0 < π j then σ j ^ 2 else 0))
        = (if j ∈ S₂ then σ j * π j else γb * (if 0 < π j then σ j ^ 2 else 0)) := by
    intro j
    by_cases hj1 : j ∈ S₁
    · have hj2 : j ∈ S₂ := hsub hj1
      rw [if_pos hj1, if_pos hj2]
    · by_cases hj2 : j ∈ S₂
      · have hmem : j ∈ S₂ \ S₁ := by
          rw [Finset.mem_sdiff]
          exact ⟨hj2, hj1⟩
        have hpj : 0 < π j := hpos j hmem
        have heq : π j = γb * σ j := hagree j hmem
        rw [if_neg hj1, if_pos hj2]
        simp only [hpj, if_true]
        rw [heq]
        ring
      · rw [if_neg hj1, if_neg hj2]
  have hmasspoint : ∀ j : Fin m,
      (if j ∈ S₁ then π j ^ 2 else γb ^ 2 * (if 0 < π j then σ j ^ 2 else 0))
        = (if j ∈ S₂ then π j ^ 2 else γb ^ 2 * (if 0 < π j then σ j ^ 2 else 0)) := by
    intro j
    by_cases hj1 : j ∈ S₁
    · have hj2 : j ∈ S₂ := hsub hj1
      rw [if_pos hj1, if_pos hj2]
    · by_cases hj2 : j ∈ S₂
      · have hmem : j ∈ S₂ \ S₁ := by
          rw [Finset.mem_sdiff]
          exact ⟨hj2, hj1⟩
        have hpj : 0 < π j := hpos j hmem
        have heq : π j = γb * σ j := hagree j hmem
        rw [if_neg hj1, if_pos hj2]
        simp only [hpj, if_true]
        rw [heq]
        ring
      · rw [if_neg hj1, if_neg hj2]
  constructor
  · rw [pieceOverlap_eq_sum π σ S₁ γb, pieceOverlap_eq_sum π σ S₂ γb]
    exact Finset.sum_congr rfl (fun j _ => hdotpoint j)
  · rw [pieceMass_eq_sum π σ S₁ γb, pieceMass_eq_sum π σ S₂ γb]
    exact Finset.sum_congr rfl (fun j _ => hmasspoint j)

/-- Nested saturation sets satisfying `pieceBreak` give equal piece gaps at the boundary level. -/
theorem pieceGap_agreement {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m)) (γb : ℚ)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂) :
    pieceGap π σ p S₁ γb = pieceGap π σ p S₂ γb := by
  obtain ⟨hdot, hmass⟩ := piece_agreement_at_boundary π σ S₁ S₂ γb hsub hbrk
  unfold pieceGap
  rw [hdot, hmass]

/-- Across two saturation pieces agreeing at their boundary, the exact gap difference is the sum
of the two level increments times their piecewise secant slopes. -/
theorem fidelityGap_diff_pieces {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂) :
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb - γ₁) * (freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
            + 2 * satDot π σ S₁ * freeSq π σ S₁)
        + (γ₂ - γb) * (freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
            + 2 * satDot π σ S₂ * freeSq π σ S₂) := by
  have hg1 : fidelityGap π σ p γ₁ = pieceGap π σ p S₁ γ₁ :=
    fidelityGap_eq_pieceGap π σ p γ₁ S₁ hπ hσ hγ₁ hpat₁
  have hg2 : fidelityGap π σ p γ₂ = pieceGap π σ p S₂ γ₂ :=
    fidelityGap_eq_pieceGap π σ p γ₂ S₂ hπ hσ hγ₂ hpat₂
  have hag : pieceGap π σ p S₁ γb = pieceGap π σ p S₂ γb :=
    pieceGap_agreement π σ p S₁ S₂ γb hsub hbrk
  have hd1 : pieceGap π σ p S₁ γb - pieceGap π σ p S₁ γ₁
      = (γb - γ₁) * (freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
            + 2 * satDot π σ S₁ * freeSq π σ S₁) :=
    pieceGap_diff π σ p S₁ γ₁ γb
  have hd2 : pieceGap π σ p S₂ γ₂ - pieceGap π σ p S₂ γb
      = (γ₂ - γb) * (freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
            + 2 * satDot π σ S₂ * freeSq π σ S₂) :=
    pieceGap_diff π σ p S₂ γb γ₂
  calc
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
        = (pieceGap π σ p S₂ γ₂ - pieceGap π σ p S₂ γb)
          + (pieceGap π σ p S₁ γb - pieceGap π σ p S₁ γ₁) := by
            rw [hg2, hg1, hag]
            ring
    _ = (γb - γ₁) * (freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
            + 2 * satDot π σ S₁ * freeSq π σ S₁)
        + (γ₂ - γb) * (freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
            + 2 * satDot π σ S₂ * freeSq π σ S₂) := by
            rw [hd1, hd2]
            ring

/-- A common lower bound on the two secant slopes bounds the gap increase across an intervening
piece boundary. -/
theorem fidelityGap_rate_across_pieces {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc₁ : c ≤ freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
          + 2 * satDot π σ S₁ * freeSq π σ S₁)
    (hc₂ : c ≤ freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
          + 2 * satDot π σ S₂ * freeSq π σ S₂) :
    c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ := by
  have hdec := fidelityGap_diff_pieces π σ p S₁ S₂ γ₁ γb γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub hbrk
  have h1 : c * (γb - γ₁)
      ≤ (freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
          + 2 * satDot π σ S₁ * freeSq π σ S₁) * (γb - γ₁) :=
    mul_le_mul_of_nonneg_right hc₁ (sub_nonneg.mpr hle₁)
  have h2 : c * (γ₂ - γb)
      ≤ (freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
          + 2 * satDot π σ S₂ * freeSq π σ S₂) * (γ₂ - γb) :=
    mul_le_mul_of_nonneg_right hc₂ (sub_nonneg.mpr hle₂)
  calc
    c * (γ₂ - γ₁) = c * (γb - γ₁) + c * (γ₂ - γb) := by ring
    _ ≤ (freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
            + 2 * satDot π σ S₁ * freeSq π σ S₁) * (γb - γ₁)
          + (freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
            + 2 * satDot π σ S₂ * freeSq π σ S₂) * (γ₂ - γb) := add_le_add h1 h2
    _ = fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ := by rw [hdec]; ring

/-- A common lower bound on the negatives of the two secant slopes bounds the gap decrease
across an intervening piece boundary. -/
theorem fidelityGap_rate_across_pieces_down {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc₁ : c ≤ -(freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
          + 2 * satDot π σ S₁ * freeSq π σ S₁))
    (hc₂ : c ≤ -(freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
          + 2 * satDot π σ S₂ * freeSq π σ S₂)) :
    c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂ := by
  have hdec := fidelityGap_diff_pieces π σ p S₁ S₂ γ₁ γb γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub hbrk
  have h1 : c * (γb - γ₁)
      ≤ -(freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
          + 2 * satDot π σ S₁ * freeSq π σ S₁) * (γb - γ₁) :=
    mul_le_mul_of_nonneg_right hc₁ (sub_nonneg.mpr hle₁)
  have h2 : c * (γ₂ - γb)
      ≤ -(freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
          + 2 * satDot π σ S₂ * freeSq π σ S₂) * (γ₂ - γb) :=
    mul_le_mul_of_nonneg_right hc₂ (sub_nonneg.mpr hle₂)
  calc
    c * (γ₂ - γ₁) = c * (γb - γ₁) + c * (γ₂ - γb) := by ring
    _ ≤ -(freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
            + 2 * satDot π σ S₁ * freeSq π σ S₁) * (γb - γ₁)
          + -(freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
            + 2 * satDot π σ S₂ * freeSq π σ S₂) * (γ₂ - γb) := add_le_add h1 h2
    _ = -(fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁) := by rw [hdec]; ring
    _ = fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂ := by ring

/-- A positive rational has a nonnegative lower bound, whereas a negative rational has no
nonnegative lower bound. -/
theorem no_common_rate_of_opposite_slopes {x₁ x₂ : ℚ}
    (h₁ : 0 < x₁) (h₂ : x₂ < 0) :
    (∃ c : ℚ, 0 ≤ c ∧ c ≤ x₁) ∧ ¬ (∃ c : ℚ, 0 ≤ c ∧ c ≤ x₂) := by
  refine ⟨⟨x₁, h₁.le, le_refl x₁⟩, ?_⟩
  rintro ⟨c, hc, hc2⟩
  exact absurd (le_trans hc hc2) (not_le.mpr h₂)

/-- The secant slope expression of a fixed piece-gap quadratic between two levels. -/
def pieceSegmentSlope {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S : Finset (Fin m)) (γ₁ γ₂ : ℚ) : ℚ :=
  freeSq π σ S * (freeSq π σ S - p) * (γ₁ + γ₂) + 2 * satDot π σ S * freeSq π σ S

/-- The smaller of the secant slopes on the two sides of a piece boundary. -/
def crossPieceRateLower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ) : ℚ :=
  min (pieceSegmentSlope π σ p S₁ γ₁ γb) (pieceSegmentSlope π σ p S₂ γb γ₂)

/-- The smaller of the negated secant slopes on the two sides of a piece boundary. -/
def crossPieceRateLowerDown {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ) : ℚ :=
  min (-(pieceSegmentSlope π σ p S₁ γ₁ γb)) (-(pieceSegmentSlope π σ p S₂ γb γ₂))

/-- Across two matching saturation pieces, the exact gap difference is the sum of the two level
increments weighted by `pieceSegmentSlope`. -/
theorem fidelityGap_diff_pieces_slope {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂) :
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb
        + (γ₂ - γb) * pieceSegmentSlope π σ p S₂ γb γ₂ := by
  rw [fidelityGap_diff_pieces π σ p S₁ S₂ γ₁ γb γ₂ hπ hσ hγ₁ hγ₂ hpat₁ hpat₂ hsub hbrk]
  rfl

/-- A positive common lower bound for two nonnegative piece slopes yields the corresponding
lower bound on gap increase across their boundary. -/
theorem fidelityGap_rate_across_pieces_lower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc : 0 < c)
    (hlower : c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂)
    (hsign₁ : 0 ≤ pieceSegmentSlope π σ p S₁ γ₁ γb)
    (hsign₂ : 0 ≤ pieceSegmentSlope π σ p S₂ γb γ₂) :
    0 < c ∧ 0 ≤ pieceSegmentSlope π σ p S₁ γ₁ γb ∧ 0 ≤ pieceSegmentSlope π σ p S₂ γb γ₂ ∧
      c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ := by
  have hmin : c ≤ min (pieceSegmentSlope π σ p S₁ γ₁ γb)
      (pieceSegmentSlope π σ p S₂ γb γ₂) := by
    rw [crossPieceRateLower] at hlower
    exact hlower
  have hc₁ : c ≤ freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
        + 2 * satDot π σ S₁ * freeSq π σ S₁ := by
    have hstep := le_trans hmin (min_le_left _ _)
    rwa [pieceSegmentSlope] at hstep
  have hc₂ : c ≤ freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
        + 2 * satDot π σ S₂ * freeSq π σ S₂ := by
    have hstep := le_trans hmin (min_le_right _ _)
    rwa [pieceSegmentSlope] at hstep
  refine ⟨hc, hsign₁, hsign₂, ?_⟩
  exact fidelityGap_rate_across_pieces π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ hγ₁ hγ₂ hle₁ hle₂
    hpat₁ hpat₂ hsub hbrk hc₁ hc₂

/-- A positive common lower bound for two negated nonpositive piece slopes yields the
corresponding lower bound on gap decrease across their boundary. -/
theorem fidelityGap_rate_across_pieces_down_lower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc : 0 < c)
    (hlower : c ≤ crossPieceRateLowerDown π σ p S₁ S₂ γ₁ γb γ₂)
    (hsign₁ : pieceSegmentSlope π σ p S₁ γ₁ γb ≤ 0)
    (hsign₂ : pieceSegmentSlope π σ p S₂ γb γ₂ ≤ 0) :
    0 < c ∧ pieceSegmentSlope π σ p S₁ γ₁ γb ≤ 0 ∧
      pieceSegmentSlope π σ p S₂ γb γ₂ ≤ 0 ∧
      c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂ := by
  have hmin : c ≤ min (-(pieceSegmentSlope π σ p S₁ γ₁ γb))
      (-(pieceSegmentSlope π σ p S₂ γb γ₂)) := by
    rw [crossPieceRateLowerDown] at hlower
    exact hlower
  have hc₁ : c ≤ -(freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
        + 2 * satDot π σ S₁ * freeSq π σ S₁) := by
    have hstep := le_trans hmin (min_le_left _ _)
    rwa [pieceSegmentSlope] at hstep
  have hc₂ : c ≤ -(freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
        + 2 * satDot π σ S₂ * freeSq π σ S₂) := by
    have hstep := le_trans hmin (min_le_right _ _)
    rwa [pieceSegmentSlope] at hstep
  refine ⟨hc, hsign₁, hsign₂, ?_⟩
  exact fidelityGap_rate_across_pieces_down π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ hγ₁ hγ₂ hle₁ hle₂
    hpat₁ hpat₂ hsub hbrk hc₁ hc₂

/-- A positive common rate bound in either direction across two matching pieces gives an
absolute gap-separation bound. -/
theorem fidelityGap_rate_across_pieces_abs {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc : 0 < c)
    (hrate : c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂ ∨
      c ≤ crossPieceRateLowerDown π σ p S₁ S₂ γ₁ γb γ₂) :
    c * |γ₁ - γ₂| ≤ |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂| := by
  have horder : γ₁ ≤ γ₂ := le_trans hle₁ hle₂
  have hlen : 0 ≤ γ₂ - γ₁ := sub_nonneg.mpr horder
  have hneg₁ : γ₁ - γ₂ ≤ 0 := sub_nonpos.mpr horder
  rcases hrate with hup | hdown
  · have h1 : c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb := by
      have h' := hup
      rw [crossPieceRateLower] at h'
      exact le_trans h' (min_le_left _ _)
    have h2 : c ≤ pieceSegmentSlope π σ p S₂ γb γ₂ := by
      have h' := hup
      rw [crossPieceRateLower] at h'
      exact le_trans h' (min_le_right _ _)
    have hs1 : 0 ≤ pieceSegmentSlope π σ p S₁ γ₁ γb := le_trans hc.le h1
    have hs2 : 0 ≤ pieceSegmentSlope π σ p S₂ γb γ₂ := le_trans hc.le h2
    have hcert := fidelityGap_rate_across_pieces_lower π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ hγ₁ hγ₂
      hle₁ hle₂ hpat₁ hpat₂ hsub hbrk hc hup hs1 hs2
    have hmul : 0 ≤ c * (γ₂ - γ₁) := mul_nonneg hc.le hlen
    have hge : 0 ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ :=
      le_trans hmul hcert.2.2.2
    have hneg₂ : fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂ ≤ 0 := by linarith
    calc c * |γ₁ - γ₂| = c * -(γ₁ - γ₂) := by rw [abs_of_nonpos hneg₁]
      _ = c * (γ₂ - γ₁) := by ring
      _ ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ := hcert.2.2.2
      _ = |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂| := by
        rw [abs_of_nonpos hneg₂]
        ring
  · have h1 : c ≤ -(pieceSegmentSlope π σ p S₁ γ₁ γb) := by
      have h' := hdown
      rw [crossPieceRateLowerDown] at h'
      exact le_trans h' (min_le_left _ _)
    have h2 : c ≤ -(pieceSegmentSlope π σ p S₂ γb γ₂) := by
      have h' := hdown
      rw [crossPieceRateLowerDown] at h'
      exact le_trans h' (min_le_right _ _)
    have hs1 : pieceSegmentSlope π σ p S₁ γ₁ γb ≤ 0 := by linarith
    have hs2 : pieceSegmentSlope π σ p S₂ γb γ₂ ≤ 0 := by linarith
    have hcert := fidelityGap_rate_across_pieces_down_lower π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ
      hγ₁ hγ₂ hle₁ hle₂ hpat₁ hpat₂ hsub hbrk hc hdown hs1 hs2
    have hmul : 0 ≤ c * (γ₂ - γ₁) := mul_nonneg hc.le hlen
    have hge : 0 ≤ fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂ :=
      le_trans hmul hcert.2.2.2
    calc c * |γ₁ - γ₂| = c * -(γ₁ - γ₂) := by rw [abs_of_nonpos hneg₁]
      _ = c * (γ₂ - γ₁) := by ring
      _ ≤ fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂ := hcert.2.2.2
      _ = |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂| := by rw [abs_of_nonneg hge]

/-- The existence of two matching saturation pieces across an intervening boundary, in either
endpoint order, with a common secant rate bound in either direction. -/
def crossPieceRate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (γ₁ γ₂ : ℚ) (c : ℚ) : Prop :=
  (∃ γb S₁ S₂,
    γ₁ ≤ γb ∧ γb ≤ γ₂ ∧
    satSet π σ γ₁ = S₁ ∧ satSet π σ γ₂ = S₂ ∧ S₁ ⊆ S₂ ∧
    pieceBreak π σ γb S₁ S₂ ∧
    (c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂ ∨
      c ≤ crossPieceRateLowerDown π σ p S₁ S₂ γ₁ γb γ₂)) ∨
  (∃ γb S₁ S₂,
    γ₂ ≤ γb ∧ γb ≤ γ₁ ∧
    satSet π σ γ₂ = S₁ ∧ satSet π σ γ₁ = S₂ ∧ S₁ ⊆ S₂ ∧
    pieceBreak π σ γb S₁ S₂ ∧
    (c ≤ crossPieceRateLower π σ p S₁ S₂ γ₂ γb γ₁ ∨
      c ≤ crossPieceRateLowerDown π σ p S₁ S₂ γ₂ γb γ₁))

/-- Positive cross-piece rate bounds for all relevant pairs of search midpoints imply `bandRate`
for nonnegative source and target entries. -/
theorem bandRate_of_cross_piece_lower {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hc : 0 < c)
    (hcross : ∀ j j' : ℕ, j < k → j' < k → j ≠ j' →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
      crossPieceRate π σ p (bracketMidpoint π σ p j) (bracketMidpoint π σ p j') c) :
    bandRate π σ b p c k := by
  intro j j' hj hj' hne hb1 hb2
  have hγ₁ : 0 ≤ bracketMidpoint π σ p j := by
    have hb := fidelityBracket_bounds π σ p j hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  have hγ₂ : 0 ≤ bracketMidpoint π σ p j' := by
    have hb := fidelityBracket_bounds π σ p j' hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  rcases hcross j j' hj hj' hne hb1 hb2 with hup | hdown
  · obtain ⟨γb, S₁, S₂, hγb₁, hγb₂, hpat₁, hpat₂, hsub, hbrk, hrate⟩ := hup
    exact fidelityGap_rate_across_pieces_abs π σ p S₁ S₂
      (bracketMidpoint π σ p j) γb (bracketMidpoint π σ p j') c hπ hσ hγ₁ hγ₂
      hγb₁ hγb₂ hpat₁ hpat₂ hsub hbrk hc hrate
  · obtain ⟨γb, S₁, S₂, hγb₁, hγb₂, hpat₁, hpat₂, hsub, hbrk, hrate⟩ := hdown
    have hcert := fidelityGap_rate_across_pieces_abs π σ p S₁ S₂
      (bracketMidpoint π σ p j') γb (bracketMidpoint π σ p j) c hπ hσ hγ₂ hγ₁
      hγb₁ hγb₂ hpat₁ hpat₂ hsub hbrk hc hrate
    have hsw : |bracketMidpoint π σ p j - bracketMidpoint π σ p j'|
        = |bracketMidpoint π σ p j' - bracketMidpoint π σ p j| := abs_sub_swap _ _
    have hsw2 : |fidelityGap π σ p (bracketMidpoint π σ p j)
          - fidelityGap π σ p (bracketMidpoint π σ p j')|
        = |fidelityGap π σ p (bracketMidpoint π σ p j')
          - fidelityGap π σ p (bracketMidpoint π σ p j)| := abs_sub_swap _ _
    calc c * |bracketMidpoint π σ p j - bracketMidpoint π σ p j'|
        = c * |bracketMidpoint π σ p j' - bracketMidpoint π σ p j| :=
          congrArg (fun t => c * t) hsw
      _ ≤ |fidelityGap π σ p (bracketMidpoint π σ p j')
            - fidelityGap π σ p (bracketMidpoint π σ p j)| := hcert
      _ = |fidelityGap π σ p (bracketMidpoint π σ p j)
            - fidelityGap π σ p (bracketMidpoint π σ p j')| := hsw2.symm

/-- The minimum of the three secant slopes along a chain of three saturation pieces. -/
def chainRateLower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ S₃ : Finset (Fin m))
    (γ₁ γb₁ γb₂ γ₂ : ℚ) : ℚ :=
  min (pieceSegmentSlope π σ p S₁ γ₁ γb₁)
    (min (pieceSegmentSlope π σ p S₂ γb₁ γb₂) (pieceSegmentSlope π σ p S₃ γb₂ γ₂))

/-- Across three pieces matching at two boundaries, the exact fidelity gap difference is the sum
of the three level increments weighted by their piece slopes. -/
theorem fidelityGap_diff_pieces_chain {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ S₃ : Finset (Fin m)) (γ₁ γb₁ γb₂ γ₂ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₃)
    (hsub₁ : S₁ ⊆ S₂) (hsub₂ : S₂ ⊆ S₃)
    (hbrk₁ : pieceBreak π σ γb₁ S₁ S₂) (hbrk₂ : pieceBreak π σ γb₂ S₂ S₃) :
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb₁ - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb₁
        + (γb₂ - γb₁) * pieceSegmentSlope π σ p S₂ γb₁ γb₂
        + (γ₂ - γb₂) * pieceSegmentSlope π σ p S₃ γb₂ γ₂ := by
  have hg1 : fidelityGap π σ p γ₁ = pieceGap π σ p S₁ γ₁ :=
    fidelityGap_eq_pieceGap π σ p γ₁ S₁ hπ hσ hγ₁ hpat₁
  have hg3 : fidelityGap π σ p γ₂ = pieceGap π σ p S₃ γ₂ :=
    fidelityGap_eq_pieceGap π σ p γ₂ S₃ hπ hσ hγ₂ hpat₂
  have hag₁ : pieceGap π σ p S₁ γb₁ = pieceGap π σ p S₂ γb₁ :=
    pieceGap_agreement π σ p S₁ S₂ γb₁ hsub₁ hbrk₁
  have hag₂ : pieceGap π σ p S₂ γb₂ = pieceGap π σ p S₃ γb₂ :=
    pieceGap_agreement π σ p S₂ S₃ γb₂ hsub₂ hbrk₂
  have hd₁ : pieceGap π σ p S₁ γb₁ - pieceGap π σ p S₁ γ₁
      = (γb₁ - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb₁ := by
    rw [pieceGap_diff, pieceSegmentSlope]
  have hd₂ : pieceGap π σ p S₂ γb₂ - pieceGap π σ p S₂ γb₁
      = (γb₂ - γb₁) * pieceSegmentSlope π σ p S₂ γb₁ γb₂ := by
    rw [pieceGap_diff, pieceSegmentSlope]
  have hd₃ : pieceGap π σ p S₃ γ₂ - pieceGap π σ p S₃ γb₂
      = (γ₂ - γb₂) * pieceSegmentSlope π σ p S₃ γb₂ γ₂ := by
    rw [pieceGap_diff, pieceSegmentSlope]
  calc
    fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
        = (pieceGap π σ p S₃ γ₂ - pieceGap π σ p S₃ γb₂)
          + (pieceGap π σ p S₂ γb₂ - pieceGap π σ p S₂ γb₁)
          + (pieceGap π σ p S₁ γb₁ - pieceGap π σ p S₁ γ₁) := by
            rw [hg3, hg1, hag₁, hag₂]
            ring
    _ = (γb₁ - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb₁
        + (γb₂ - γb₁) * pieceSegmentSlope π σ p S₂ γb₁ γb₂
        + (γ₂ - γb₂) * pieceSegmentSlope π σ p S₃ γb₂ γ₂ := by
            rw [hd₁, hd₂, hd₃]
            ring

/-- A positive lower bound on all three piece slopes gives a lower bound on the fidelity gap
increase across the ordered three-piece chain. -/
theorem fidelityGap_rate_across_chain {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ S₃ : Finset (Fin m)) (γ₁ γb₁ γb₂ γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb₁) (hle₂ : γb₁ ≤ γb₂) (hle₃ : γb₂ ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₃)
    (hsub₁ : S₁ ⊆ S₂) (hsub₂ : S₂ ⊆ S₃)
    (hbrk₁ : pieceBreak π σ γb₁ S₁ S₂) (hbrk₂ : pieceBreak π σ γb₂ S₂ S₃)
    (hc : 0 < c)
    (hlower : c ≤ chainRateLower π σ p S₁ S₂ S₃ γ₁ γb₁ γb₂ γ₂) :
    0 < c ∧ c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ := by
  have hdec := fidelityGap_diff_pieces_chain π σ p S₁ S₂ S₃ γ₁ γb₁ γb₂ γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub₁ hsub₂ hbrk₁ hbrk₂
  have h1 : c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb₁ := by
    have h' := hlower
    rw [chainRateLower] at h'
    exact le_trans h' (min_le_left _ _)
  have h2 : c ≤ pieceSegmentSlope π σ p S₂ γb₁ γb₂ := by
    have h' := hlower
    rw [chainRateLower] at h'
    exact le_trans h' (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : c ≤ pieceSegmentSlope π σ p S₃ γb₂ γ₂ := by
    have h' := hlower
    rw [chainRateLower] at h'
    exact le_trans h' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hm1 : c * (γb₁ - γ₁) ≤ pieceSegmentSlope π σ p S₁ γ₁ γb₁ * (γb₁ - γ₁) :=
    mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hle₁)
  have hm2 : c * (γb₂ - γb₁) ≤ pieceSegmentSlope π σ p S₂ γb₁ γb₂ * (γb₂ - γb₁) :=
    mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hle₂)
  have hm3 : c * (γ₂ - γb₂) ≤ pieceSegmentSlope π σ p S₃ γb₂ γ₂ * (γ₂ - γb₂) :=
    mul_le_mul_of_nonneg_right h3 (sub_nonneg.mpr hle₃)
  refine ⟨hc, ?_⟩
  calc
    c * (γ₂ - γ₁) = c * (γb₁ - γ₁) + c * (γb₂ - γb₁) + c * (γ₂ - γb₂) := by ring
    _ ≤ pieceSegmentSlope π σ p S₁ γ₁ γb₁ * (γb₁ - γ₁)
        + pieceSegmentSlope π σ p S₂ γb₁ γb₂ * (γb₂ - γb₁)
        + pieceSegmentSlope π σ p S₃ γb₂ γ₂ * (γ₂ - γb₂) := by
      linarith
    _ = fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁ := by rw [hdec]; ring

/-- A segment specified by an index set and rational lower and upper levels. -/
structure ChainSegment {m : ℕ} where
  S : Finset (Fin m)
  γlo : ℚ
  γhi : ℚ

/-- The first segment of a list, with the empty-set zero-level segment as the default for an
empty list. -/
def chainFirstSeg {m : ℕ} : List (ChainSegment (m := m)) → ChainSegment (m := m)
  | [] => ⟨∅, 0, 0⟩
  | s :: _ => s

/-- The last segment of a list, with the empty-set zero-level segment as the default for an
empty list. -/
def chainLastSeg {m : ℕ} : List (ChainSegment (m := m)) → ChainSegment (m := m)
  | [] => ⟨∅, 0, 0⟩
  | [s] => s
  | _ :: t :: rest => chainLastSeg (t :: rest)

/-- Requires nonnegative ordered segment levels, matching adjacent endpoints, nested index sets,
and the `pieceBreak` condition at each shared boundary. -/
def ChainWellFormed {m : ℕ} (π σ : Fin m → ℚ) : List (ChainSegment (m := m)) → Prop
  | [] => True
  | [s] => 0 ≤ s.γlo ∧ s.γlo ≤ s.γhi
  | s₁ :: s₂ :: rest =>
      0 ≤ s₁.γlo ∧ s₁.γlo ≤ s₁.γhi ∧
      s₁.γhi = s₂.γlo ∧ s₁.S ⊆ s₂.S ∧
      pieceBreak π σ s₁.γhi s₁.S s₂.S ∧
      ChainWellFormed π σ (s₂ :: rest)

/-- The minimum of a rational function over a segment list, with value zero on an empty list. -/
def chainMin {m : ℕ} (f : ChainSegment (m := m) → ℚ) :
    List (ChainSegment (m := m)) → ℚ
  | [] => 0
  | [s] => f s
  | s :: t :: rest => min (f s) (chainMin f (t :: rest))

/-- The minimum piece secant slope over a segment chain, with value zero for an empty chain. -/
def chainSlopeLower {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (segs : List (ChainSegment (m := m))) : ℚ :=
  chainMin (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) segs

/-- The minimum negated piece secant slope over a segment chain, with value zero for an empty
chain. -/
def chainSlopeLowerDown {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (segs : List (ChainSegment (m := m))) : ℚ :=
  chainMin (fun s => -(pieceSegmentSlope π σ p s.S s.γlo s.γhi)) segs

/-- The sum of a segment function weighted by each segment's level width. -/
def chainWeightedSum {m : ℕ} (f : ChainSegment (m := m) → ℚ)
    (segs : List (ChainSegment (m := m))) : ℚ :=
  (segs.map (fun s => (s.γhi - s.γlo) * f s)).sum

/-- The sum of piece secant slopes weighted by their segment widths. -/
def chainSegmentSum {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (segs : List (ChainSegment (m := m))) : ℚ :=
  chainWeightedSum (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) segs

/-- The sum of the level widths of all segments in a list. -/
def chainWidthSum {m : ℕ} (segs : List (ChainSegment (m := m))) : ℚ :=
  (segs.map (fun s => s.γhi - s.γlo)).sum

/-- The chain minimum is at most the function value at every segment in the list. -/
theorem chainMin_le_of_mem {m : ℕ} (f : ChainSegment (m := m) → ℚ) :
    ∀ (segs : List (ChainSegment (m := m))) (s : ChainSegment (m := m)),
      s ∈ segs → chainMin f segs ≤ f s := by
  intro segs
  induction segs with
  | nil => intro s hs; simp at hs
  | cons a rest ih =>
      intro s hs
      cases rest with
      | nil =>
          simp only [chainMin]
          have hsa : s = a := by simpa using! hs
          subst hsa
          exact le_refl _
      | cons b rest' =>
          simp only [chainMin]
          rcases (by simpa using! hs : s = a ∨ s ∈ b :: rest') with rfl | hs'
          · exact min_le_left _ _
          · exact le_trans (min_le_right _ _) (ih s hs')

/-- A common lower bound on all segment values bounds the minimum of a nonempty chain from
below. -/
theorem le_chainMin {m : ℕ} (f : ChainSegment (m := m) → ℚ) (c : ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] →
      (∀ s ∈ segs, c ≤ f s) → c ≤ chainMin f segs := by
  intro segs
  induction segs with
  | nil => intro hne _; simp at hne
  | cons a rest ih =>
      intro hne hval
      cases rest with
      | nil =>
          simp only [chainMin]
          have h1 : c ≤ f a := hval a (by simp)
          exact h1
      | cons b rest' =>
          simp only [chainMin]
          have h1 : c ≤ f a := hval a (by simp)
          have h2 : c ≤ chainMin f (b :: rest') :=
            ih (by simp) (fun s hs => hval s (by simp [hs]))
          exact le_min h1 h2

/-- The minimum over a nonempty segment chain is nonpositive exactly when some segment value is
nonpositive. -/
theorem chainMin_le_zero_iff {m : ℕ} (f : ChainSegment (m := m) → ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] →
      (chainMin f segs ≤ 0 ↔ ∃ s ∈ segs, f s ≤ 0) := by
  intro segs
  induction segs with
  | nil => intro hne; simp at hne
  | cons a rest ih =>
      intro hne
      cases rest with
      | nil =>
          simp only [chainMin]
          constructor
          · intro h
            exact ⟨a, by simp, h⟩
          · rintro ⟨s, hs, h⟩
            have hsa : s = a := by simpa using! hs
            subst hsa
            exact h
      | cons b rest' =>
          simp only [chainMin]
          constructor
          · intro h
            have hmin : min (f a) (chainMin f (b :: rest')) ≤ 0 := h
            by_cases ha : f a ≤ 0
            · exact ⟨a, by simp, ha⟩
            · have hrest : chainMin f (b :: rest') ≤ 0 := by
                by_contra hc
                have hpos : 0 < chainMin f (b :: rest') := lt_of_not_ge hc
                have hposa : 0 < f a := lt_of_not_ge ha
                have hlt : 0 < min (f a) (chainMin f (b :: rest')) := lt_min hposa hpos
                linarith
              obtain ⟨s, hs, hfs⟩ := (ih (by simp)).mp hrest
              exact ⟨s, by simp [hs], hfs⟩
          · rintro ⟨s, hs, h⟩
            rcases (by simpa using! hs : s = a ∨ s ∈ b :: rest') with rfl | hs'
            · exact le_trans (min_le_left _ _) h
            · have hrest : chainMin f (b :: rest') ≤ 0 :=
                (ih (by simp)).mpr ⟨s, hs', h⟩
              exact le_trans (min_le_right _ _) hrest

/-- Every segment in a well-formed chain has a nonnegative lower level and an upper level at
least its lower level. -/
theorem chainWellFormed_width {m : ℕ} (π σ : Fin m → ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), ChainWellFormed π σ segs →
      (∀ s ∈ segs, 0 ≤ s.γlo ∧ s.γlo ≤ s.γhi) := by
  intro segs
  induction segs with
  | nil => intro _; simp
  | cons a rest ih =>
      intro hv
      cases rest with
      | nil =>
          simp only [ChainWellFormed] at hv
          intro s hs
          have hsa : s = a := by simpa using! hs
          subst hsa
          exact ⟨hv.1, hv.2⟩
      | cons b rest' =>
          simp only [ChainWellFormed] at hv
          have htail := ih hv.2.2.2.2.2
          intro s hs
          rcases (by simpa using! hs : s = a ∨ s ∈ b :: rest') with rfl | hs'
          · exact ⟨hv.1, hv.2.1⟩
          · exact htail s hs'

/-- The last segment's upper level is nonnegative for a well-formed chain, including the
empty-chain default. -/
theorem chainLastSeg_nonneg {m : ℕ} (π σ : Fin m → ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), ChainWellFormed π σ segs →
      0 ≤ (chainLastSeg segs).γhi := by
  intro segs
  induction segs with
  | nil => intro _; simp [chainLastSeg]
  | cons a rest ih =>
      intro hv
      cases rest with
      | nil =>
          simp only [ChainWellFormed] at hv
          simp only [chainLastSeg]
          exact le_trans hv.1 hv.2
      | cons b rest' =>
          simp only [ChainWellFormed] at hv
          have h := ih hv.2.2.2.2.2
          show 0 ≤ (chainLastSeg (b :: rest')).γhi
          exact h

/-- For a nonempty well-formed chain, the sum of widths equals the last upper level minus the
first lower level. -/
theorem chainWidthSum_eq {m : ℕ} (π σ : Fin m → ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] → ChainWellFormed π σ segs →
      chainWidthSum segs = (chainLastSeg segs).γhi - (chainFirstSeg segs).γlo := by
  intro segs
  induction segs with
  | nil => intro _ _; simp [chainFirstSeg, chainLastSeg, chainWidthSum]
  | cons a rest ih =>
      intro hne hv
      cases rest with
      | nil =>
          rw [chainFirstSeg, chainLastSeg, chainWidthSum, List.map_cons, List.sum_cons,
            List.map_nil, List.sum_nil]
          ring
      | cons b rest' =>
          simp only [ChainWellFormed] at hv
          have htail : ((b :: rest').map (fun s => s.γhi - s.γlo)).sum
              = (chainLastSeg (b :: rest')).γhi - b.γlo := by
            simpa only [chainWidthSum] using! ih (by simp) hv.2.2.2.2.2
          rw [chainFirstSeg, chainLastSeg, chainWidthSum, List.map_cons, List.sum_cons]
          rw [htail]
          rw [← hv.2.2.1]
          ring

/-- On a nonempty chain with nonnegative widths, a common lower bound on segment values bounds
their weighted sum by that lower bound times the total width. -/
theorem chainWeightedSum_ge {m : ℕ} (f : ChainSegment (m := m) → ℚ) (c : ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] →
      (∀ s ∈ segs, c ≤ f s) → (∀ s ∈ segs, 0 ≤ s.γhi - s.γlo) →
      c * chainWidthSum segs ≤ chainWeightedSum f segs := by
  intro segs
  induction segs with
  | nil => intro _ _ _; simp at *
  | cons a rest ih =>
      intro hne hval hwidth
      cases rest with
      | nil =>
          have h1 : c ≤ f a := hval a (by simp)
          have h2 : 0 ≤ a.γhi - a.γlo := hwidth a (by simp)
          have h3 : c * (a.γhi - a.γlo) ≤ (a.γhi - a.γlo) * f a := by
            simpa [mul_comm] using! mul_le_mul_of_nonneg_right h1 h2
          simp only [chainWidthSum, chainWeightedSum, List.map_cons, List.sum_cons,
            List.map_nil, List.sum_nil]
          simpa using! h3
      | cons b rest' =>
          have htail := ih (by simp) (fun s hs => hval s (by simp [hs]))
            (fun s hs => hwidth s (by simp [hs]))
          have h1 : c ≤ f a := hval a (by simp)
          have h2 : 0 ≤ a.γhi - a.γlo := hwidth a (by simp)
          have h3 : c * (a.γhi - a.γlo) ≤ (a.γhi - a.γlo) * f a := by
            simpa [mul_comm] using! mul_le_mul_of_nonneg_right h1 h2
          simp only [chainWidthSum, chainWeightedSum, List.map_cons, List.sum_cons] at htail ⊢
          ring_nf at htail h3 ⊢
          linarith

/-- For a nonempty well-formed chain, the last piece gap minus the first piece gap equals the
sum of width-weighted piece secant slopes. -/
theorem pieceGap_diff_chain {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] → ChainWellFormed π σ segs →
      pieceGap π σ p (chainLastSeg segs).S (chainLastSeg segs).γhi
        - pieceGap π σ p (chainFirstSeg segs).S (chainFirstSeg segs).γlo
        = chainWeightedSum (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) segs := by
  intro segs
  induction segs with
  | nil => intro _ _; simp [chainFirstSeg, chainLastSeg, chainWeightedSum]
  | cons a rest ih =>
      intro hne hv
      cases rest with
      | nil =>
          rw [chainFirstSeg, chainLastSeg, chainWeightedSum, List.map_cons, List.sum_cons,
            List.map_nil, List.sum_nil]
          rw [pieceGap_diff]
          simp only [pieceSegmentSlope]
          ring
      | cons b rest' =>
          simp only [ChainWellFormed] at hv
          have hag : pieceGap π σ p b.S b.γlo = pieceGap π σ p a.S a.γhi := by
            rw [← hv.2.2.1]
            exact (pieceGap_agreement π σ p a.S b.S a.γhi hv.2.2.2.1 hv.2.2.2.2.1).symm
          have htail : ((b :: rest').map (fun s => (s.γhi - s.γlo)
              * pieceSegmentSlope π σ p s.S s.γlo s.γhi)).sum
              = pieceGap π σ p (chainLastSeg (b :: rest')).S (chainLastSeg (b :: rest')).γhi
                - pieceGap π σ p b.S b.γlo := by
            have h := ih (by simp) hv.2.2.2.2.2
            simpa only [chainWeightedSum, chainFirstSeg] using! h.symm
          rw [chainFirstSeg, chainLastSeg, chainWeightedSum, List.map_cons, List.sum_cons]
          rw [htail, hag]
          simp only [pieceSegmentSlope]
          rw [← pieceGap_diff π σ p a.S a.γlo a.γhi]
          ring

/-- For nonnegative data and a nonempty well-formed chain matching the actual endpoint
saturation sets, the exact fidelity gap difference equals the sum of width-weighted piece
slopes. -/
theorem fidelityGap_diff_chain {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] → ChainWellFormed π σ segs →
      satSet π σ (chainFirstSeg segs).γlo = (chainFirstSeg segs).S →
      satSet π σ (chainLastSeg segs).γhi = (chainLastSeg segs).S →
      fidelityGap π σ p (chainLastSeg segs).γhi - fidelityGap π σ p (chainFirstSeg segs).γlo
        = chainWeightedSum (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) segs := by
  intro segs
  induction segs with
  | nil => intro _ _ _ _; simp [chainFirstSeg, chainLastSeg, chainWeightedSum]
  | cons a rest ih =>
      intro hne hv hfirst hlast
      cases rest with
      | nil =>
          simp only [ChainWellFormed] at hv
          simp only [chainFirstSeg, chainLastSeg] at hfirst hlast ⊢
          have hγlo : 0 ≤ a.γlo := hv.1
          have hγhi : 0 ≤ a.γhi := le_trans hv.1 hv.2
          rw [fidelityGap_eq_pieceGap π σ p a.γhi a.S hπ hσ hγhi hlast,
            fidelityGap_eq_pieceGap π σ p a.γlo a.S hπ hσ hγlo hfirst]
          simpa only [chainFirstSeg, chainLastSeg] using!
            (pieceGap_diff_chain π σ p [a] (by simp) (by simpa [ChainWellFormed] using! hv))
      | cons b rest' =>
          simp only [ChainWellFormed] at hv
          simp only [chainFirstSeg, chainLastSeg] at hfirst hlast ⊢
          have hγlo : 0 ≤ a.γlo := hv.1
          have hγhi : 0 ≤ (chainLastSeg (b :: rest')).γhi :=
            chainLastSeg_nonneg π σ (b :: rest') hv.2.2.2.2.2
          rw [fidelityGap_eq_pieceGap π σ p (chainLastSeg (b :: rest')).γhi
              (chainLastSeg (b :: rest')).S hπ hσ hγhi hlast,
            fidelityGap_eq_pieceGap π σ p a.γlo a.S hπ hσ hγlo hfirst]
          simpa only [chainFirstSeg, chainLastSeg] using!
            (pieceGap_diff_chain π σ p (a :: b :: rest') (by simp) hv)

/-- The first lower level of a nonempty well-formed chain is at most its last upper level. -/
theorem chainFirst_le_last {m : ℕ} (π σ : Fin m → ℚ) :
    ∀ (segs : List (ChainSegment (m := m))), segs ≠ [] → ChainWellFormed π σ segs →
      (chainFirstSeg segs).γlo ≤ (chainLastSeg segs).γhi := by
  intro segs
  induction segs with
  | nil => intro _ _; simp [chainFirstSeg, chainLastSeg]
  | cons a rest ih =>
      intro hne hv
      cases rest with
      | nil =>
          simp only [ChainWellFormed] at hv
          simp only [chainFirstSeg, chainLastSeg]
          exact hv.2
      | cons b rest' =>
          simp only [ChainWellFormed] at hv
          have htail := ih (by simp) hv.2.2.2.2.2
          have hstep : a.γlo ≤ a.γhi := hv.2.1
          have hjoin : a.γhi = b.γlo := hv.2.2.1
          show a.γlo ≤ (chainLastSeg (b :: rest')).γhi
          exact le_trans hstep (le_trans (le_of_eq hjoin) htail)

/-- The width-weighted sum of negated piece slopes equals the negative of `chainSegmentSum`. -/
theorem chainWeightedSum_neg {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) :
    ∀ (segs : List (ChainSegment (m := m))),
      chainWeightedSum (fun s => -(pieceSegmentSlope π σ p s.S s.γlo s.γhi)) segs
        = -(chainSegmentSum π σ p segs) := by
  intro segs
  induction segs with
  | nil => simp [chainWeightedSum, chainSegmentSum]
  | cons a rest ih =>
      have h := ih
      simp only [chainWeightedSum, chainSegmentSum, List.map_cons, List.sum_cons] at h ⊢
      rw [h]
      ring

/-- A positive common lower bound on piece slopes in a nonempty well-formed chain bounds the
exact fidelity gap increase when the endpoint saturation sets match. -/
theorem fidelityGap_rate_across_segment_chain {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (segs : List (ChainSegment (m := m))) (hne : segs ≠ [])
    (hv : ChainWellFormed π σ segs)
    (hfirst : satSet π σ (chainFirstSeg segs).γlo = (chainFirstSeg segs).S)
    (hlast : satSet π σ (chainLastSeg segs).γhi = (chainLastSeg segs).S)
    (hc : 0 < c)
    (hlower : c ≤ chainSlopeLower π σ p segs) :
    0 < c ∧ c * ((chainLastSeg segs).γhi - (chainFirstSeg segs).γlo)
      ≤ fidelityGap π σ p (chainLastSeg segs).γhi - fidelityGap π σ p (chainFirstSeg segs).γlo := by
  have hval : ∀ s ∈ segs, c ≤ pieceSegmentSlope π σ p s.S s.γlo s.γhi := by
    intro s hs
    exact le_trans hlower
      (chainMin_le_of_mem (fun t => pieceSegmentSlope π σ p t.S t.γlo t.γhi) segs s hs)
  have hwidth : ∀ s ∈ segs, 0 ≤ s.γhi - s.γlo :=
    fun s hs => sub_nonneg.mpr (chainWellFormed_width π σ segs hv s hs).2
  have hbound : c * chainWidthSum segs ≤ chainSegmentSum π σ p segs := by
    have h := chainWeightedSum_ge (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) c
      segs hne hval hwidth
    simpa only [chainWeightedSum, chainSegmentSum] using! h
  have htel : chainWidthSum segs = (chainLastSeg segs).γhi - (chainFirstSeg segs).γlo :=
    chainWidthSum_eq π σ segs hne hv
  have hdec : fidelityGap π σ p (chainLastSeg segs).γhi
      - fidelityGap π σ p (chainFirstSeg segs).γlo = chainSegmentSum π σ p segs :=
    fidelityGap_diff_chain π σ p hπ hσ segs hne hv hfirst hlast
  refine ⟨hc, ?_⟩
  rw [hdec, ← htel]
  exact hbound

/-- A positive common lower bound on negated piece slopes in a nonempty well-formed chain bounds
the exact fidelity gap decrease when the endpoint saturation sets match. -/
theorem fidelityGap_rate_across_segment_chain_down {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (segs : List (ChainSegment (m := m))) (hne : segs ≠ [])
    (hv : ChainWellFormed π σ segs)
    (hfirst : satSet π σ (chainFirstSeg segs).γlo = (chainFirstSeg segs).S)
    (hlast : satSet π σ (chainLastSeg segs).γhi = (chainLastSeg segs).S)
    (hc : 0 < c)
    (hlower : c ≤ chainSlopeLowerDown π σ p segs) :
    0 < c ∧ c * ((chainLastSeg segs).γhi - (chainFirstSeg segs).γlo)
      ≤ fidelityGap π σ p (chainFirstSeg segs).γlo - fidelityGap π σ p (chainLastSeg segs).γhi := by
  have hval : ∀ s ∈ segs, c ≤ -(pieceSegmentSlope π σ p s.S s.γlo s.γhi) := by
    intro s hs
    exact le_trans hlower
      (chainMin_le_of_mem (fun t => -(pieceSegmentSlope π σ p t.S t.γlo t.γhi)) segs s hs)
  have hwidth : ∀ s ∈ segs, 0 ≤ s.γhi - s.γlo :=
    fun s hs => sub_nonneg.mpr (chainWellFormed_width π σ segs hv s hs).2
  have hbound : c * chainWidthSum segs
      ≤ chainWeightedSum (fun s => -(pieceSegmentSlope π σ p s.S s.γlo s.γhi)) segs := by
    have h := chainWeightedSum_ge (fun s => -(pieceSegmentSlope π σ p s.S s.γlo s.γhi)) c
      segs hne hval hwidth
    simpa only [chainWeightedSum] using! h
  have hneg : chainWeightedSum (fun s => -(pieceSegmentSlope π σ p s.S s.γlo s.γhi)) segs
      = -(chainSegmentSum π σ p segs) := chainWeightedSum_neg π σ p segs
  have htel : chainWidthSum segs = (chainLastSeg segs).γhi - (chainFirstSeg segs).γlo :=
    chainWidthSum_eq π σ segs hne hv
  have hdec : fidelityGap π σ p (chainLastSeg segs).γhi
      - fidelityGap π σ p (chainFirstSeg segs).γlo = chainSegmentSum π σ p segs :=
    fidelityGap_diff_chain π σ p hπ hσ segs hne hv hfirst hlast
  have hdec' : fidelityGap π σ p (chainFirstSeg segs).γlo
      - fidelityGap π σ p (chainLastSeg segs).γhi = -(chainSegmentSum π σ p segs) := by
    linarith [hdec]
  refine ⟨hc, ?_⟩
  rw [hdec', ← htel, ← hneg]
  exact hbound

/-- A positive common chain rate in either direction bounds absolute fidelity gap separation by
that rate times endpoint separation. -/
theorem fidelityGap_rate_across_segment_chain_abs {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (segs : List (ChainSegment (m := m))) (hne : segs ≠ [])
    (hv : ChainWellFormed π σ segs)
    (hfirst : satSet π σ (chainFirstSeg segs).γlo = (chainFirstSeg segs).S)
    (hlast : satSet π σ (chainLastSeg segs).γhi = (chainLastSeg segs).S)
    (hc : 0 < c)
    (hrate : c ≤ chainSlopeLower π σ p segs ∨ c ≤ chainSlopeLowerDown π σ p segs) :
    c * |(chainFirstSeg segs).γlo - (chainLastSeg segs).γhi|
      ≤ |fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi| := by
  have horder : (chainFirstSeg segs).γlo ≤ (chainLastSeg segs).γhi :=
    chainFirst_le_last π σ segs hne hv
  have hlen : 0 ≤ (chainLastSeg segs).γhi - (chainFirstSeg segs).γlo := sub_nonneg.mpr horder
  have habs : |(chainFirstSeg segs).γlo - (chainLastSeg segs).γhi|
      = (chainLastSeg segs).γhi - (chainFirstSeg segs).γlo := by
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    ring
  rcases hrate with h | h
  · have hcert := fidelityGap_rate_across_segment_chain π σ p c hπ hσ segs hne hv hfirst
      hlast hc h
    have hge : 0 ≤ fidelityGap π σ p (chainLastSeg segs).γhi
        - fidelityGap π σ p (chainFirstSeg segs).γlo :=
      le_trans (mul_nonneg hc.le hlen) hcert.2
    have habsgap : |fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi|
        = fidelityGap π σ p (chainLastSeg segs).γhi
          - fidelityGap π σ p (chainFirstSeg segs).γlo := by
      have hkey : fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi
          = -((fidelityGap π σ p (chainLastSeg segs).γhi
            - fidelityGap π σ p (chainFirstSeg segs).γlo)) := by ring
      rw [hkey, abs_neg, abs_of_nonneg hge]
    calc c * |(chainFirstSeg segs).γlo - (chainLastSeg segs).γhi|
        = c * ((chainLastSeg segs).γhi - (chainFirstSeg segs).γlo) := by rw [habs]
      _ ≤ fidelityGap π σ p (chainLastSeg segs).γhi
          - fidelityGap π σ p (chainFirstSeg segs).γlo := hcert.2
      _ = |fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi| := by rw [habsgap]
  · have hcert := fidelityGap_rate_across_segment_chain_down π σ p c hπ hσ segs hne hv
      hfirst hlast hc h
    have hge : 0 ≤ fidelityGap π σ p (chainFirstSeg segs).γlo
        - fidelityGap π σ p (chainLastSeg segs).γhi :=
      le_trans (mul_nonneg hc.le hlen) hcert.2
    have habsgap : |fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi|
        = fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi := by
      rw [abs_of_nonneg hge]
    calc c * |(chainFirstSeg segs).γlo - (chainLastSeg segs).γhi|
        = c * ((chainLastSeg segs).γhi - (chainFirstSeg segs).γlo) := by rw [habs]
      _ ≤ fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi := hcert.2
      _ = |fidelityGap π σ p (chainFirstSeg segs).γlo
          - fidelityGap π σ p (chainLastSeg segs).γhi| := by rw [habsgap]

/-- For a nonempty chain, the minimum piece slope is nonpositive exactly when at least one
segment has a nonpositive piece slope. -/
theorem chainSlopeLower_le_zero_iff {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (segs : List (ChainSegment (m := m))) (hne : segs ≠ []) :
    (chainSlopeLower π σ p segs ≤ 0 ↔
      ∃ s ∈ segs, pieceSegmentSlope π σ p s.S s.γlo s.γhi ≤ 0) := by
  simpa only [chainSlopeLower] using!
    (chainMin_le_zero_iff (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) segs hne)

/-- The condition that the product of the two piece secant slopes across a boundary is
nonpositive. -/
def breakpointCutsRate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ) : Prop :=
  pieceSegmentSlope π σ p S₁ γ₁ γb * pieceSegmentSlope π σ p S₂ γb γ₂ ≤ 0

/-- If the two boundary slopes have nonpositive product, no positive common rate lies below both
slopes or below both negated slopes. -/
theorem breakpointCutsRate_no_common_rate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ)
    (hcut : breakpointCutsRate π σ p S₁ S₂ γ₁ γb γ₂) :
    ¬ (∃ c : ℚ, 0 < c ∧ (c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂ ∨
      c ≤ crossPieceRateLowerDown π σ p S₁ S₂ γ₁ γb γ₂)) := by
  simp only [breakpointCutsRate] at hcut
  rintro ⟨c, hc, hrate⟩
  rcases hrate with h | h
  · rw [crossPieceRateLower] at h
    have h1 : c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb := le_trans h (min_le_left _ _)
    have h2 : c ≤ pieceSegmentSlope π σ p S₂ γb γ₂ := le_trans h (min_le_right _ _)
    have hp : 0 < pieceSegmentSlope π σ p S₁ γ₁ γb
        * pieceSegmentSlope π σ p S₂ γb γ₂ :=
      mul_pos (lt_of_lt_of_le hc h1) (lt_of_lt_of_le hc h2)
    linarith [hcut]
  · rw [crossPieceRateLowerDown] at h
    have h1 : c ≤ -(pieceSegmentSlope π σ p S₁ γ₁ γb) := le_trans h (min_le_left _ _)
    have h2 : c ≤ -(pieceSegmentSlope π σ p S₂ γb γ₂) := le_trans h (min_le_right _ _)
    have hs1 : pieceSegmentSlope π σ p S₁ γ₁ γb < 0 := by linarith
    have hs2 : pieceSegmentSlope π σ p S₂ γb γ₂ < 0 := by linarith
    have hp : 0 < pieceSegmentSlope π σ p S₁ γ₁ γb
        * pieceSegmentSlope π σ p S₂ γb γ₂ := by
      have hkey : pieceSegmentSlope π σ p S₁ γ₁ γb
          * pieceSegmentSlope π σ p S₂ γb γ₂
          = -(pieceSegmentSlope π σ p S₁ γ₁ γb)
            * -(pieceSegmentSlope π σ p S₂ γb γ₂) := by ring
      rw [hkey]
      exact mul_pos (by linarith) (by linarith)
    linarith [hcut]

/-- If the two boundary slopes have positive product, there exists a positive common rate below
both slopes or below both negated slopes. -/
theorem no_breakpointCutsRate_common_rate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ)
    (hnocut : ¬ breakpointCutsRate π σ p S₁ S₂ γ₁ γb γ₂) :
    ∃ c : ℚ, 0 < c ∧ (c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂ ∨
      c ≤ crossPieceRateLowerDown π σ p S₁ S₂ γ₁ γb γ₂) := by
  simp only [breakpointCutsRate] at hnocut
  have hprod : 0 < pieceSegmentSlope π σ p S₁ γ₁ γb
      * pieceSegmentSlope π σ p S₂ γb γ₂ := lt_of_not_ge hnocut
  by_cases h1 : 0 < pieceSegmentSlope π σ p S₁ γ₁ γb
  · by_cases h2 : 0 < pieceSegmentSlope π σ p S₂ γb γ₂
    · refine ⟨min (pieceSegmentSlope π σ p S₁ γ₁ γb)
          (pieceSegmentSlope π σ p S₂ γb γ₂), lt_min h1 h2, Or.inl ?_⟩
      rw [crossPieceRateLower]
    · have hnonpos : pieceSegmentSlope π σ p S₁ γ₁ γb
          * pieceSegmentSlope π σ p S₂ γb γ₂ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h1.le (le_of_not_gt h2)
      linarith
  · have hs2 : pieceSegmentSlope π σ p S₂ γb γ₂ < 0 := by
      have hne : pieceSegmentSlope π σ p S₂ γb γ₂ ≠ 0 := by
        intro hz
        rw [hz] at hprod
        norm_num at hprod
      by_contra h
      have hnonpos : pieceSegmentSlope π σ p S₁ γ₁ γb
          * pieceSegmentSlope π σ p S₂ γb γ₂ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h1) (le_of_not_gt h)
      linarith
    have hs1 : pieceSegmentSlope π σ p S₁ γ₁ γb < 0 := by
      have hne : pieceSegmentSlope π σ p S₁ γ₁ γb ≠ 0 := by
        intro hz
        rw [hz] at hprod
        norm_num at hprod
      exact lt_of_le_of_ne (le_of_not_gt h1) hne
    refine ⟨min (-(pieceSegmentSlope π σ p S₁ γ₁ γb))
          (-(pieceSegmentSlope π σ p S₂ γb γ₂)),
      lt_min (by simpa using! neg_lt_neg hs1) (by simpa using! neg_lt_neg hs2), Or.inr ?_⟩
    rw [crossPieceRateLowerDown]

/-- Collects the exact chain gap decomposition, the segmentwise common slope bounds, and the
resulting lower bound on gap increase. -/
theorem frontier21 {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (c : ℚ)
    (segs : List (ChainSegment (m := m))) (hne : segs ≠ [])
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hv : ChainWellFormed π σ segs)
    (hfirst : satSet π σ (chainFirstSeg segs).γlo = (chainFirstSeg segs).S)
    (hlast : satSet π σ (chainLastSeg segs).γhi = (chainLastSeg segs).S)
    (hc : 0 < c)
    (hlower : c ≤ chainSlopeLower π σ p segs) :
    (fidelityGap π σ p (chainLastSeg segs).γhi
        - fidelityGap π σ p (chainFirstSeg segs).γlo
      = chainWeightedSum (fun s => pieceSegmentSlope π σ p s.S s.γlo s.γhi) segs) ∧
    (c ≤ chainSlopeLower π σ p segs ∧
      (∀ s ∈ segs, c ≤ pieceSegmentSlope π σ p s.S s.γlo s.γhi)) ∧
    (c * ((chainLastSeg segs).γhi - (chainFirstSeg segs).γlo)
      ≤ fidelityGap π σ p (chainLastSeg segs).γhi
        - fidelityGap π σ p (chainFirstSeg segs).γlo) := by
  have hdec := fidelityGap_diff_chain π σ p hπ hσ segs hne hv hfirst hlast
  have hval : ∀ s ∈ segs, c ≤ pieceSegmentSlope π σ p s.S s.γlo s.γhi := by
    intro s hs
    exact le_trans hlower
      (chainMin_le_of_mem (fun t => pieceSegmentSlope π σ p t.S t.γlo t.γhi) segs s hs)
  have hrate := fidelityGap_rate_across_segment_chain π σ p c hπ hσ segs hne hv hfirst hlast
    hc hlower
  exact ⟨hdec, ⟨hlower, hval⟩, hrate.2⟩

/-- The existence of a nonempty well-formed segment chain joining the two levels in either
order, matching endpoint saturation sets, with a common rate bound in either direction. -/
def chainPieceRate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (γ₁ γ₂ : ℚ) (c : ℚ) : Prop :=
  ∃ segs : List (ChainSegment (m := m)), segs ≠ [] ∧
    ChainWellFormed π σ segs ∧
    (c ≤ chainSlopeLower π σ p segs ∨ c ≤ chainSlopeLowerDown π σ p segs) ∧
    ((chainFirstSeg segs).γlo = γ₁ ∧ (chainLastSeg segs).γhi = γ₂ ∧
        satSet π σ γ₁ = (chainFirstSeg segs).S ∧
        satSet π σ γ₂ = (chainLastSeg segs).S ∨
      (chainFirstSeg segs).γlo = γ₂ ∧ (chainLastSeg segs).γhi = γ₁ ∧
        satSet π σ γ₂ = (chainFirstSeg segs).S ∧
        satSet π σ γ₁ = (chainLastSeg segs).S)

/-- Positive chain rate bounds for all relevant pairs of search midpoints imply `bandRate` for
nonnegative source and target entries. -/
theorem bandRate_of_chain_lower {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hc : 0 < c)
    (hchain : ∀ j j' : ℕ, j < k → j' < k → j ≠ j' →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
      chainPieceRate π σ p (bracketMidpoint π σ p j) (bracketMidpoint π σ p j') c) :
    bandRate π σ b p c k := by
  intro j j' hj hj' hne hb1 hb2
  obtain ⟨segs, hsegs, hv, hrate, hends⟩ :=
    hchain j j' hj hj' hne hb1 hb2
  rcases hends with ⟨hlo, hhi, hpat₁, hpat₂⟩ | ⟨hlo', hhi', hpat₂', hpat₁'⟩
  · rw [← hlo] at hpat₁
    rw [← hhi] at hpat₂
    have hcert := fidelityGap_rate_across_segment_chain_abs π σ p c hπ hσ segs hsegs hv
      hpat₁ hpat₂ hc hrate
    rw [hlo, hhi] at hcert
    exact hcert
  · rw [← hlo'] at hpat₂'
    rw [← hhi'] at hpat₁'
    have hcert := fidelityGap_rate_across_segment_chain_abs π σ p c hπ hσ segs hsegs hv
      hpat₂' hpat₁' hc hrate
    rw [hlo', hhi'] at hcert
    simpa only [abs_sub_comm] using! hcert

/-- Combines plateau fidelity and gap formulas, failure-test exclusion at maximal target, the
first-breakpoint characterization, and a band-rate bound on search ambiguities. -/
theorem frontier14 {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (b k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 ≤ p)
    (hsupp : (sourceSupport π).Nonempty)
    (c : ℚ) (hc : 0 < c) (hrate : bandRate π σ b p c k) :
    (∀ γ, 0 < γ → onPlateau π σ γ →
        computedFidelity π σ γ = computedPmax π σ ∧
        fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p))) ∧
    (p = computedPmax π σ → ∀ γ, 0 ≤ γ → onPlateau π σ γ →
        intervalFails b π σ p γ = false) ∧
    (∀ γ, onPlateau π σ γ ↔ γ ≤ firstBreakpoint π σ) ∧
    (intervalFidelitySearch b π σ p k).2.ambiguities
      ≤ Nat.floor (2 * ambiguityBandBound π σ b p / c * (2 : ℚ) ^ k
          / computedWaterHigh π σ) + 1 := by
  have hmax : 0 < computedPmax π σ := computedPmax_pos_of_support π σ hσ hsupp
  have hplateau : ∀ γ, 0 < γ → onPlateau π σ γ →
        computedFidelity π σ γ = computedPmax π σ ∧
        fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by
    intro γ hγ hplate
    refine ⟨computedFidelity_plateau π σ hπ (fun j => (hσ j).le) hγ hplate hmax, ?_⟩
    exact fidelityGap_plateau π σ p hπ (fun j => (hσ j).le) hγ.le hplate
  have hdegen : p = computedPmax π σ → ∀ γ, 0 ≤ γ → onPlateau π σ γ →
        intervalFails b π σ p γ = false := by
    intro hp γ hγ hplate
    exact intervalFails_plateau_false π σ b p hπ (fun j => (hσ j).le) hγ hplate hp
  have hwidth : ∀ γ, onPlateau π σ γ ↔ γ ≤ firstBreakpoint π σ :=
    fun γ => onPlateau_iff_le π σ hπ hσ hsupp γ
  have hcount := ambiguityCount_le b π σ p k hπ (fun j => (hσ j).le) hp c hc hrate
  exact ⟨hplateau, hdegen, hwidth, hcount⟩

/-- Collects plateau gap growth above a positive cutoff, confinement and counting of plateau
ambiguities, and a width-based upper bound on interval operation costs. -/
theorem frontier15 {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (b k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 ≤ p)
    (hsupp : (sourceSupport π).Nonempty)
    (hpp : p < computedPmax π σ)
    (c : ℚ) (hc : 0 < c) (hrate : bandRate π σ b p c k) (γ₀ : ℚ) (hγ₀ : 0 < γ₀) :
    (∀ γ, 0 < γ → onPlateau π σ γ →
        computedFidelity π σ γ = computedPmax π σ ∧
        fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p))) ∧
    (∀ γ₁ γ₂, γ₀ ≤ γ₁ → γ₀ ≤ γ₂ →
        onPlateau π σ γ₁ → onPlateau π σ γ₂ →
        2 * computedPmax π σ * (computedPmax π σ - p) * γ₀ * |γ₁ - γ₂|
          ≤ |fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁|) ∧
    (∀ γ, 0 ≤ γ → onPlateau π σ γ →
        intervalDecision b π σ p γ = .ambiguous →
        γ ^ 2 ≤ plateauAmbiguityLevel π σ b p) ∧
    ((ambiguousPlateauLevelsAbove b π σ p k γ₀).card
      ≤ Nat.floor (ambiguityBandBound π σ b p
          / (computedPmax π σ * (computedPmax π σ - p) * γ₀)
          * (2 : ℚ) ^ k / computedWaterHigh π σ) + 1) ∧
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities
      ≤ intervalRunOperationCount m k (Nat.floor (2 * ambiguityBandBound π σ b p / c
          * (2 : ℚ) ^ k / computedWaterHigh π σ) + 1)) := by
  have hmax : 0 < computedPmax π σ := computedPmax_pos_of_support π σ hσ hsupp
  have hplateau : ∀ γ, 0 < γ → onPlateau π σ γ →
        computedFidelity π σ γ = computedPmax π σ ∧
        fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by
    intro γ hγ hplate
    refine ⟨computedFidelity_plateau π σ hπ (fun j => (hσ j).le) hγ hplate hmax, ?_⟩
    exact fidelityGap_plateau π σ p hπ (fun j => (hσ j).le) hγ.le hplate
  have hrate' : ∀ γ₁ γ₂, γ₀ ≤ γ₁ → γ₀ ≤ γ₂ →
        onPlateau π σ γ₁ → onPlateau π σ γ₂ →
        2 * computedPmax π σ * (computedPmax π σ - p) * γ₀ * |γ₁ - γ₂|
          ≤ |fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁| := by
    intro γ₁ γ₂ hx₀ hy₀ hplate₁ hplate₂
    exact plateau_gap_rate_lower π σ p hπ (fun j => (hσ j).le) hγ₀ hx₀ hy₀
      hplate₁ hplate₂ hpp.le
  have hconf : ∀ γ, 0 ≤ γ → onPlateau π σ γ →
        intervalDecision b π σ p γ = .ambiguous →
        γ ^ 2 ≤ plateauAmbiguityLevel π σ b p := by
    intro γ hγ hplate hamb
    exact plateau_ambiguity_confined π σ b p hπ (fun j => (hσ j).le) hγ hp hmax hpp
      hplate hamb
  have hcount := ambiguousPlateauLevelsAbove_count_le b π σ p k hπ (fun j => (hσ j).le)
    hp hmax hpp γ₀ hγ₀
  have hops := intervalRunOperationCount_le_of_width π σ b p k hπ (fun j => (hσ j).le)
    hp c hc hrate
  exact ⟨hplateau, hrate', hconf, hcount, hops⟩

/-- Combines plateau formulas with the plateau ambiguity count bound, at most one plateau
ambiguity, and accumulated error bounds under the joint termination condition. -/
theorem frontier16 {m : ℕ} (π σ : Fin m → ℚ) (p ε πi : ℚ) (b k n : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hπi : 0 < πi)
    (hsupp : (sourceSupport π).Nonempty) (hpp : p < computedPmax π σ) (hn : 0 < n)
    (hj : jointTerminationSufficient π σ b p ε πi k n) :
    (∀ γ, 0 < γ → onPlateau π σ γ →
        computedFidelity π σ γ = computedPmax π σ ∧
        fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p))) ∧
    ((ambiguousPlateauLevels b π σ p k).card ≤ plateauAmbiguityCountBound π σ b p k) ∧
    ((ambiguousPlateauLevels b π σ p k).card ≤ 1) ∧
    ((n : ℚ) * (gridStep b / 2) / πi ≤ ε * πi / p ∧
      (n : ℚ) * (gridStep b / 2) ≤ πi ^ 2 / 2) := by
  have hmax : 0 < computedPmax π σ := computedPmax_pos_of_support π σ hσ hsupp
  have hplateau : ∀ γ, 0 < γ → onPlateau π σ γ →
        computedFidelity π σ γ = computedPmax π σ ∧
        fidelityGap π σ p γ = γ ^ 2 * (computedPmax π σ * (computedPmax π σ - p)) := by
    intro γ hγ hplate
    refine ⟨computedFidelity_plateau π σ hπ (fun j => (hσ j).le) hγ hplate hmax, ?_⟩
    exact fidelityGap_plateau π σ p hπ (fun j => (hσ j).le) hγ.le hplate
  have hcount := ambiguousPlateauLevels_count_le b π σ p k hπ (fun j => (hσ j).le) hp.le hmax hpp
  obtain ⟨hbits, hcrit⟩ := hj
  obtain ⟨h1, h2⟩ := opBitBudget_sufficient hn hε hp hπi b hbits
  have hone := plateau_resolution_criterion_sufficient b π σ p k hπ (fun j => (hσ j).le)
    hp.le hmax hpp hcrit
  exact ⟨hplateau, hcount, hone, ⟨h1, h2⟩⟩

/-- Collects boundary agreement, the two-piece gap decomposition, and the gap increase bound
from a common lower secant slope. -/
theorem frontier17 {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc₁ : c ≤ freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
          + 2 * satDot π σ S₁ * freeSq π σ S₁)
    (hc₂ : c ≤ freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
          + 2 * satDot π σ S₂ * freeSq π σ S₂) :
    (satDot π σ S₁ + γb * freeSq π σ S₁ = satDot π σ S₂ + γb * freeSq π σ S₂ ∧
      satMass π S₁ + γb ^ 2 * freeSq π σ S₁ = satMass π S₂ + γb ^ 2 * freeSq π σ S₂) ∧
    (fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb - γ₁) * (freeSq π σ S₁ * (freeSq π σ S₁ - p) * (γ₁ + γb)
            + 2 * satDot π σ S₁ * freeSq π σ S₁)
        + (γ₂ - γb) * (freeSq π σ S₂ * (freeSq π σ S₂ - p) * (γb + γ₂)
            + 2 * satDot π σ S₂ * freeSq π σ S₂)) ∧
    (c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁) := by
  obtain ⟨hdot, hmass⟩ := piece_agreement_at_boundary π σ S₁ S₂ γb hsub hbrk
  have hdec := fidelityGap_diff_pieces π σ p S₁ S₂ γ₁ γb γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub hbrk
  have hrate := fidelityGap_rate_across_pieces π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ hγ₁ hγ₂
    hle₁ hle₂ hpat₁ hpat₂ hsub hbrk hc₁ hc₂
  exact ⟨⟨hdot, hmass⟩, hdec, hrate⟩

/-- Collects the two-piece gap decomposition, individual slope bounds from
`crossPieceRateLower`, and the resulting lower bound on gap increase. -/
theorem frontier18 {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (S₁ S₂ : Finset (Fin m))
    (γ₁ γb γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc : 0 < c)
    (hlower : c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂)
    (hsign₁ : 0 ≤ pieceSegmentSlope π σ p S₁ γ₁ γb)
    (hsign₂ : 0 ≤ pieceSegmentSlope π σ p S₂ γb γ₂) :
    (fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb
        + (γ₂ - γb) * pieceSegmentSlope π σ p S₂ γb γ₂) ∧
    (c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂ ∧
      c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb ∧ c ≤ pieceSegmentSlope π σ p S₂ γb γ₂) ∧
    (c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁) := by
  have hdec := fidelityGap_diff_pieces_slope π σ p S₁ S₂ γ₁ γb γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub hbrk
  have hmin : c ≤ min (pieceSegmentSlope π σ p S₁ γ₁ γb)
      (pieceSegmentSlope π σ p S₂ γb γ₂) := by
    rw [crossPieceRateLower] at hlower
    exact hlower
  have hrate := fidelityGap_rate_across_pieces_lower π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ hγ₁ hγ₂
    hle₁ hle₂ hpat₁ hpat₂ hsub hbrk hc hlower hsign₁ hsign₂
  refine ⟨hdec, ⟨hlower, le_trans hmin (min_le_left _ _),
    le_trans hmin (min_le_right _ _)⟩, hrate.2.2.2⟩

/-- Combines the two-piece gap decomposition and absolute rate bound with a band rate obtained
from the stated cross-piece conditions on search midpoints. -/
theorem frontier19 {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ)
    (S₁ S₂ : Finset (Fin m)) (γ₁ γb γ₂ : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb) (hle₂ : γb ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₂)
    (hsub : S₁ ⊆ S₂) (hbrk : pieceBreak π σ γb S₁ S₂)
    (hc : 0 < c)
    (hlower : c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂)
    (hcross : ∀ j j' : ℕ, j < k → j' < k → j ≠ j' →
      |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
      |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
      crossPieceRate π σ p (bracketMidpoint π σ p j) (bracketMidpoint π σ p j') c) :
    (fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb
        + (γ₂ - γb) * pieceSegmentSlope π σ p S₂ γb γ₂) ∧
    (c ≤ crossPieceRateLower π σ p S₁ S₂ γ₁ γb γ₂ ∧
      c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb ∧ c ≤ pieceSegmentSlope π σ p S₂ γb γ₂) ∧
    (c * |γ₁ - γ₂| ≤ |fidelityGap π σ p γ₁ - fidelityGap π σ p γ₂|) ∧
    (bandRate π σ b p c k) := by
  have hdec := fidelityGap_diff_pieces_slope π σ p S₁ S₂ γ₁ γb γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub hbrk
  have hmin : c ≤ min (pieceSegmentSlope π σ p S₁ γ₁ γb)
      (pieceSegmentSlope π σ p S₂ γb γ₂) := by
    have h' := hlower
    rw [crossPieceRateLower] at h'
    exact h'
  have h1 : c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb := le_trans hmin (min_le_left _ _)
  have h2 : c ≤ pieceSegmentSlope π σ p S₂ γb γ₂ := le_trans hmin (min_le_right _ _)
  have habs := fidelityGap_rate_across_pieces_abs π σ p S₁ S₂ γ₁ γb γ₂ c hπ hσ hγ₁ hγ₂
    hle₁ hle₂ hpat₁ hpat₂ hsub hbrk hc (Or.inl hlower)
  have hband := bandRate_of_cross_piece_lower π σ b p c k hπ hσ hc hcross
  refine ⟨hdec, ⟨hlower, h1, h2⟩, habs, hband⟩

/-- Collects the three-piece gap decomposition, individual slope bounds from `chainRateLower`,
and the resulting lower bound on gap increase. -/
theorem frontier20 {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (S₁ S₂ S₃ : Finset (Fin m)) (γ₁ γb₁ γb₂ γ₂ : ℚ) (c : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hle₁ : γ₁ ≤ γb₁) (hle₂ : γb₁ ≤ γb₂) (hle₃ : γb₂ ≤ γ₂)
    (hpat₁ : satSet π σ γ₁ = S₁) (hpat₂ : satSet π σ γ₂ = S₃)
    (hsub₁ : S₁ ⊆ S₂) (hsub₂ : S₂ ⊆ S₃)
    (hbrk₁ : pieceBreak π σ γb₁ S₁ S₂) (hbrk₂ : pieceBreak π σ γb₂ S₂ S₃)
    (hc : 0 < c)
    (hlower : c ≤ chainRateLower π σ p S₁ S₂ S₃ γ₁ γb₁ γb₂ γ₂) :
    (fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁
      = (γb₁ - γ₁) * pieceSegmentSlope π σ p S₁ γ₁ γb₁
        + (γb₂ - γb₁) * pieceSegmentSlope π σ p S₂ γb₁ γb₂
        + (γ₂ - γb₂) * pieceSegmentSlope π σ p S₃ γb₂ γ₂) ∧
    (c ≤ chainRateLower π σ p S₁ S₂ S₃ γ₁ γb₁ γb₂ γ₂ ∧
      c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb₁ ∧
      c ≤ pieceSegmentSlope π σ p S₂ γb₁ γb₂ ∧
      c ≤ pieceSegmentSlope π σ p S₃ γb₂ γ₂) ∧
    (c * (γ₂ - γ₁) ≤ fidelityGap π σ p γ₂ - fidelityGap π σ p γ₁) := by
  have hdec := fidelityGap_diff_pieces_chain π σ p S₁ S₂ S₃ γ₁ γb₁ γb₂ γ₂ hπ hσ hγ₁ hγ₂
    hpat₁ hpat₂ hsub₁ hsub₂ hbrk₁ hbrk₂
  have h1 : c ≤ pieceSegmentSlope π σ p S₁ γ₁ γb₁ := by
    have h' := hlower
    rw [chainRateLower] at h'
    exact le_trans h' (min_le_left _ _)
  have h2 : c ≤ pieceSegmentSlope π σ p S₂ γb₁ γb₂ := by
    have h' := hlower
    rw [chainRateLower] at h'
    exact le_trans h' (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : c ≤ pieceSegmentSlope π σ p S₃ γb₂ γ₂ := by
    have h' := hlower
    rw [chainRateLower] at h'
    exact le_trans h' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrate := fidelityGap_rate_across_chain π σ p S₁ S₂ S₃ γ₁ γb₁ γb₂ γ₂ c hπ hσ hγ₁ hγ₂
    hle₁ hle₂ hle₃ hpat₁ hpat₂ hsub₁ hsub₂ hbrk₁ hbrk₂ hc hlower
  refine ⟨hdec, ⟨hlower, h1, h2, h3⟩, hrate.2⟩

end Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver
