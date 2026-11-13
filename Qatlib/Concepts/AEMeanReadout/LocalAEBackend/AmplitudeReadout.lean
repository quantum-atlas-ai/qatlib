/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutDefs

/-!
# Oracle cost transport for amplitude readout

This module realizes single-record and pathwise oracle cost ledgers for the amplitude estimation
framework of [BrassardEtAl2002]. It proves the controlled marking implementation and output
validation, then transports resource identities to weighted families of records.
`pathLedgerTransport_exists_iff` characterizes exactly when path transport is possible: every
grid must be positive.

## Main statements

* `recordOracleCostTransport`: validates a single AE record and its resource ledger.
* `pathLedgerTransport_exists_iff`: characterizes existence of a path ledger.
* `clause89_fixed`: collects transport guarantees with the required grid positivity assumptions.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The preparation accesses along a path equal twice its marking count plus its number of
records. -/
theorem pathPrep_eq (grids : List ℕ) :
    pathPrep grids = 2 * pathMarks grids + grids.length := by
  induction grids with
  | nil => rfl
  | cons g grids ih =>
    show (2 * (g - 1) + 1) + pathPrep grids =
      2 * ((g - 1) + pathMarks grids) + (grids.length + 1)
    omega

/-- The fixed gate count along a path equals five times its marking count plus three times its
number of records. -/
theorem pathFixed_eq (grids : List ℕ) :
    pathFixed grids = 5 * pathMarks grids + 3 * grids.length := by
  induction grids with
  | nil => rfl
  | cons g grids ih =>
    show (5 * (g - 1) + 3) + pathFixed grids =
      5 * ((g - 1) + pathMarks grids) + 3 * (grids.length + 1)
    omega

/-- The path control-macro count equals the path marking count. -/
theorem pathControl_eq (grids : List ℕ) : pathControl grids = pathMarks grids := rfl

/-- Prepending grid `g` adds `g-1` to the path marking count. -/
theorem pathMarks_cons (g : ℕ) (grids : List ℕ) :
    pathMarks (g :: grids) = (g - 1) + pathMarks grids := by
  simp [pathMarks]

/-- For positive grids, their sum equals the path marking count plus the number of records. -/
theorem sum_eq_pathMarks_add_length_of_one_le (grids : List ℕ)
    (h : ∀ g ∈ grids, 1 ≤ g) : grids.sum = pathMarks grids + grids.length := by
  induction grids with
  | nil => rfl
  | cons g grids ih =>
    have hg : 1 ≤ g := h g (List.mem_cons.mpr (Or.inl rfl))
    have ih' : grids.sum = pathMarks grids + grids.length :=
      ih (fun x hx => h x (List.mem_cons_of_mem g hx))
    rw [List.sum_cons, List.length_cons, pathMarks_cons, ih']
    omega

/-- For any grid list, its sum is at most the path marking count plus the number of records. -/
theorem sum_le_pathMarks_add_length (grids : List ℕ) :
    grids.sum ≤ pathMarks grids + grids.length := by
  induction grids with
  | nil => simp [pathMarks]
  | cons g grids ih =>
    rw [List.sum_cons, List.length_cons, pathMarks_cons]
    omega

/-- A grid list containing zero has sum strictly smaller than its path marking count plus its
length. -/
theorem sum_lt_pathMarks_add_length_of_zero_mem (grids : List ℕ) (h : 0 ∈ grids) :
    grids.sum < pathMarks grids + grids.length := by
  induction grids with
  | nil => simp at h
  | cons g grids ih =>
    rw [List.sum_cons, List.length_cons, pathMarks_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have := sum_le_pathMarks_add_length grids
      omega
    · have := ih h
      omega

/-- A transported path ledger implies that the sum of its grids equals its marking count plus
its record count. -/
theorem pathLedger_conservation (grids : List ℕ) (L : OracleCostLedger)
    (h : PathLedgerTransport grids L) :
    grids.sum = pathMarks grids + grids.length := by
  have h1 : L.sourceEvaluations = grids.sum := h.1
  have h2 : L.controlledMarks = pathMarks grids := h.2.1
  have h3 : L.finalEvaluations = grids.length := h.2.2.1
  have h4 : L.sourceEvaluations = L.controlledMarks + L.finalEvaluations := h.2.2.2.1
  omega

/-- The canonical path ledger obtained by summing the grid, marking, preparation, and fixed gate
counts. -/
def pathLedger (grids : List ℕ) : OracleCostLedger where
  sourceEvaluations := grids.sum
  controlledMarks := pathMarks grids
  prepAccesses := pathPrep grids
  sourceReflections := pathMarks grids
  controlMacros := pathControl grids
  validationQueries := 0
  finalEvaluations := grids.length
  fixedGates := pathFixed grids

/-- For a list of positive grids, the canonical path ledger satisfies `PathLedgerTransport`. -/
theorem pathLedgerTransport_pathLedger (grids : List ℕ) (h : ∀ g ∈ grids, 1 ≤ g) :
    PathLedgerTransport grids (pathLedger grids) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  show grids.sum = pathMarks grids + grids.length
  exact sum_eq_pathMarks_add_length_of_one_le grids h

/-- Every list of positive grids possesses a transported path ledger with source evaluations
equal to the grid sum. -/
theorem pathLedgerTransport_of_one_le (grids : List ℕ) (h : ∀ g ∈ grids, 1 ≤ g) :
    ∃ L : OracleCostLedger, PathLedgerTransport grids L ∧ L.sourceEvaluations = grids.sum :=
  ⟨pathLedger grids, pathLedgerTransport_pathLedger grids h, rfl⟩

/-- A grid list containing zero possesses no transported path ledger. -/
theorem not_pathLedgerTransport_of_zero_mem {grids : List ℕ} (h : 0 ∈ grids) :
    ¬ ∃ L : OracleCostLedger, PathLedgerTransport grids L := by
  rintro ⟨L, hL⟩
  exact (sum_lt_pathMarks_add_length_of_zero_mem grids h).ne
    (pathLedger_conservation grids L hL)

/-- A transported path ledger exists exactly when every grid in the list is at least one. -/
theorem pathLedgerTransport_exists_iff (grids : List ℕ) :
    (∃ L : OracleCostLedger, PathLedgerTransport grids L) ↔ ∀ g ∈ grids, 1 ≤ g := by
  constructor
  · rintro ⟨L, hL⟩ g hg
    rcases Nat.eq_zero_or_pos g with rfl | hpos
    · exact absurd ⟨L, hL⟩ (not_pathLedgerTransport_of_zero_mem hg)
    · exact hpos
  · intro h
    exact (pathLedgerTransport_of_one_le grids h).imp (fun _ h => h.1)

/-- A finite weighted sum distributes over pointwise addition. -/
theorem sum_mul_add_split {Ω : Type} [Fintype Ω] (w : Ω → ℝ) (a b : Ω → ℝ) :
    (∑ ω, w ω * (a ω + b ω)) = (∑ ω, w ω * a ω) + ∑ ω, w ω * b ω :=
  calc (∑ ω, w ω * (a ω + b ω))
      = ∑ ω, (w ω * a ω + w ω * b ω) :=
        Finset.sum_congr rfl (fun ω _ => mul_add (w ω) (a ω) (b ω))
    _ = (∑ ω, w ω * a ω) + ∑ ω, w ω * b ω := Finset.sum_add_distrib

/-- A constant real factor can be pulled out of a finite weighted sum. -/
theorem sum_mul_const_mul {Ω : Type} [Fintype Ω] (w : Ω → ℝ) (a : Ω → ℝ) (c : ℝ) :
    (∑ ω, w ω * (c * a ω)) = c * (∑ ω, w ω * a ω) :=
  calc (∑ ω, w ω * (c * a ω))
      = ∑ ω, (c * (w ω * a ω)) := Finset.sum_congr rfl (fun ω _ => by ring)
    _ = c * (∑ ω, w ω * a ω) :=
      (Finset.mul_sum (Finset.univ : Finset Ω) (fun ω => w ω * a ω) c).symm

/-- A weighted family of paths with positive grids satisfies all expected ledger transport
identities. -/
theorem expectedLedgerTransport_of_one_le {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (gridsOf : Ω → List ℕ) (hpos : ∀ ω, ∀ g ∈ gridsOf ω, 1 ≤ g) :
    ExpectedLedgerTransport w gridsOf := by
  have hcons : ∀ ω, (gridsOf ω).sum = pathMarks (gridsOf ω) + (gridsOf ω).length := fun ω =>
    sum_eq_pathMarks_add_length_of_one_le (gridsOf ω) (hpos ω)
  have hsum : (∑ ω, w ω * ((gridsOf ω).sum : ℝ))
      = (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)) + ∑ ω, w ω * ((gridsOf ω).length : ℝ) :=
    calc (∑ ω, w ω * ((gridsOf ω).sum : ℝ))
        = ∑ ω, w ω * (((pathMarks (gridsOf ω) + (gridsOf ω).length : ℕ)) : ℝ) :=
          Finset.sum_congr rfl (fun ω _ => by rw [hcons ω])
      _ = ∑ ω, w ω * ((pathMarks (gridsOf ω) : ℝ) + ((gridsOf ω).length : ℝ)) :=
          Finset.sum_congr rfl (fun ω _ => by rw [Nat.cast_add])
      _ = (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)) + ∑ ω, w ω * ((gridsOf ω).length : ℝ) :=
          sum_mul_add_split w (fun ω => (pathMarks (gridsOf ω) : ℝ))
            (fun ω => ((gridsOf ω).length : ℝ))
  have hprep : (∑ ω, w ω * (pathPrep (gridsOf ω) : ℝ))
      = 2 * (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)) + ∑ ω, w ω * ((gridsOf ω).length : ℝ) :=
    calc (∑ ω, w ω * (pathPrep (gridsOf ω) : ℝ))
        = ∑ ω, w ω * (((2 * pathMarks (gridsOf ω) + (gridsOf ω).length : ℕ)) : ℝ) :=
          Finset.sum_congr rfl (fun ω _ => by rw [pathPrep_eq])
      _ = ∑ ω, w ω * (2 * (pathMarks (gridsOf ω) : ℝ) + ((gridsOf ω).length : ℝ)) :=
          Finset.sum_congr rfl (fun ω _ => by push_cast; rfl)
      _ = (∑ ω, w ω * (2 * (pathMarks (gridsOf ω) : ℝ))) + ∑ ω, w ω * ((gridsOf ω).length : ℝ) :=
          sum_mul_add_split w (fun ω => (2 * (pathMarks (gridsOf ω) : ℝ)))
            (fun ω => ((gridsOf ω).length : ℝ))
      _ = 2 * (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)) + ∑ ω, w ω * ((gridsOf ω).length : ℝ) :=
          congrArg (· + ∑ ω, w ω * ((gridsOf ω).length : ℝ))
            (sum_mul_const_mul w (fun ω => (pathMarks (gridsOf ω) : ℝ)) 2)
  have hfixed : (∑ ω, w ω * (pathFixed (gridsOf ω) : ℝ))
      = 5 * (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ))
          + 3 * (∑ ω, w ω * ((gridsOf ω).length : ℝ)) :=
    calc (∑ ω, w ω * (pathFixed (gridsOf ω) : ℝ))
        = ∑ ω, w ω * (((5 * pathMarks (gridsOf ω) + 3 * (gridsOf ω).length : ℕ)) : ℝ) :=
          Finset.sum_congr rfl (fun ω _ => by rw [pathFixed_eq])
      _ = ∑ ω, w ω * (5 * (pathMarks (gridsOf ω) : ℝ) + 3 * ((gridsOf ω).length : ℝ)) :=
          Finset.sum_congr rfl (fun ω _ => by push_cast; rfl)
      _ = (∑ ω, w ω * (5 * (pathMarks (gridsOf ω) : ℝ)))
            + ∑ ω, w ω * (3 * ((gridsOf ω).length : ℝ)) :=
          sum_mul_add_split w (fun ω => (5 * (pathMarks (gridsOf ω) : ℝ)))
            (fun ω => (3 * ((gridsOf ω).length : ℝ)))
      _ = 5 * (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ))
            + ∑ ω, w ω * (3 * ((gridsOf ω).length : ℝ)) :=
          congrArg (· + ∑ ω, w ω * (3 * ((gridsOf ω).length : ℝ)))
            (sum_mul_const_mul w (fun ω => (pathMarks (gridsOf ω) : ℝ)) 5)
      _ = 5 * (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ))
            + 3 * (∑ ω, w ω * ((gridsOf ω).length : ℝ)) :=
          congrArg (5 * (∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)) + ·)
            (sum_mul_const_mul w (fun ω => ((gridsOf ω).length : ℝ)) 3)
  refine ⟨hsum, hprep, ?_, ?_, hfixed⟩
  · show (∑ ω, w ω * (pathControl (gridsOf ω) : ℝ)) =
      ∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)
    rfl
  · simp

/-- Positive grids and agreement of each source ledger with its grid sum imply joint pathwise
and expected oracle cost transport. -/
theorem jointRecordOracleCostTransport_of_one_le {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (gridsOf : Ω → List ℕ) (sourceLedger : Ω → ℕ)
    (hpos : ∀ ω, ∀ g ∈ gridsOf ω, 1 ≤ g)
    (hsrc : ∀ ω, sourceLedger ω = (gridsOf ω).sum) :
    JointRecordOracleCostTransport w gridsOf sourceLedger := by
  refine ⟨?_, expectedLedgerTransport_of_one_le w gridsOf hpos, ?_⟩
  · intro ω
    obtain ⟨L, hL, hsum⟩ := pathLedgerTransport_of_one_le (gridsOf ω) (hpos ω)
    exact ⟨L, hL, hsum.trans (hsrc ω).symm⟩
  · refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [hsrc ω]

/-- A zero grid on any path prevents joint record oracle cost transport. -/
theorem not_jointRecordOracleCostTransport_of_zero_mem {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (gridsOf : Ω → List ℕ) (sourceLedger : Ω → ℕ) (ω : Ω) (h : 0 ∈ gridsOf ω) :
    ¬ JointRecordOracleCostTransport w gridsOf sourceLedger := by
  rintro ⟨hpath, _, _⟩
  obtain ⟨L, hL, _⟩ := hpath ω
  exact not_pathLedgerTransport_of_zero_mem h ⟨L, hL⟩

/-- A grid occurs in `recordGrids` exactly when it is the final grid or an executed prefix grid. -/
theorem mem_recordGrids_iff {n : ℕ} (grid : Fin n → ℕ) (exec : Fin n → Bool) (m : ℕ) (g : ℕ) :
    g ∈ recordGrids grid exec m ↔ g = m ∨ ∃ l, exec l = true ∧ g = grid l := by
  constructor
  · intro hg
    rw [recordGrids, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · right
      simp only [List.mem_filterMap, List.mem_ofFn, id_eq] at hg
      obtain ⟨a, ⟨l, hl⟩, he⟩ := hg
      subst a
      by_cases hx : exec l = true
      · simp only [if_pos hx] at hl
        exact ⟨l, hx, (Option.some.inj hl).symm⟩
      · simp only [if_neg hx] at hl
        exact absurd hl (by simp)
    · left
      rfl
  · rintro (rfl | ⟨l, hl, rfl⟩)
    · simp [recordGrids]
    · rw [recordGrids, List.mem_append]
      left
      simp only [List.mem_filterMap, List.mem_ofFn, id_eq]
      exact ⟨some (grid l), ⟨l, if_pos hl⟩, rfl⟩

/-- All recorded grids are positive if the prefix grids and final grid are positive. -/
theorem one_le_of_mem_recordGrids {n : ℕ} (grid : Fin n → ℕ) (exec : Fin n → Bool) (m : ℕ)
    (hgrid : ∀ l, 1 ≤ grid l) (hm : 1 ≤ m) (g : ℕ) (hg : g ∈ recordGrids grid exec m) :
    1 ≤ g := by
  rcases (mem_recordGrids_iff grid exec m g).1 hg with rfl | ⟨l, _, rfl⟩
  · exact hm
  · exact hgrid l

/-- A record with final grid zero contains a zero grid. -/
theorem zero_mem_recordGrids_zero {n : ℕ} (grid : Fin n → ℕ) (exec : Fin n → Bool) :
    (0 : ℕ) ∈ recordGrids grid exec 0 :=
  (mem_recordGrids_iff grid exec 0 0).2 (Or.inl rfl)

/-- Every grid of the form `2*2^l` is at least one. -/
theorem one_le_two_mul_two_pow (l : ℕ) : 1 ≤ 2 * 2 ^ l := by
  have hp : (0 : ℕ) < 2 ^ l := pow_pos (by norm_num) l
  omega

/-- The basic counting record has positive grids whenever its final grid is positive. -/
theorem one_le_of_mem_basicRecordGrids {L : ℕ} (grid : Fin L → Bool) (m : ℕ) (hm : 1 ≤ m)
    (g : ℕ) (hg : g ∈ recordGrids (fun l : Fin L => 2 * 2 ^ l.val) grid m) : 1 ≤ g :=
  one_le_of_mem_recordGrids (fun l : Fin L => 2 * 2 ^ l.val) grid m
    (fun l => one_le_two_mul_two_pow l.val) hm g hg

/-- A record with two rough grids and one final grid has positive grids if both grid sizes are
positive. -/
theorem one_le_of_mem_exactRecordGrids {M0 : ℕ} (m : ℕ) (hM0 : 1 ≤ M0) (hm : 1 ≤ m)
    (g : ℕ) (hg : g ∈ recordGrids (fun _ : Fin 2 => M0) (fun _ => true) m) : 1 ≤ g :=
  one_le_of_mem_recordGrids (fun _ : Fin 2 => M0) (fun _ => true) m (fun _ => hM0) hm g hg

/-- Basic counting records satisfy joint oracle cost transport when all final grids are positive
and source ledgers equal their grid sums. -/
theorem clause89_basic_of_pos (L : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
    (exec : Ω → Fin L → Bool) (Mfin sourceLedger : Ω → ℕ)
    (hMfin : ∀ ω, 1 ≤ Mfin ω)
    (hsrc : ∀ ω, sourceLedger ω =
      (recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω)).sum) :
    JointRecordOracleCostTransport w
      (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
      sourceLedger :=
  jointRecordOracleCostTransport_of_one_le w
    (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
    sourceLedger
    (fun ω g hg => one_le_of_mem_basicRecordGrids (exec ω) (Mfin ω) (hMfin ω) g hg)
    hsrc

/-- Two-rough-grid exact counting records satisfy joint oracle cost transport when the rough and
final grids are positive and source ledgers equal their grid sums. -/
theorem clause89_exact_of_pos (M0 : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
    (Mfin sourceLedger : Ω → ℕ)
    (hM0 : 1 ≤ M0) (hMfin : ∀ ω, 1 ≤ Mfin ω)
    (hsrc : ∀ ω, sourceLedger ω =
      (recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω)).sum) :
    JointRecordOracleCostTransport w
      (fun ω => recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω))
      sourceLedger :=
  jointRecordOracleCostTransport_of_one_le w
    (fun ω => recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω))
    sourceLedger
    (fun ω g hg => one_le_of_mem_exactRecordGrids (Mfin ω) hM0 (hMfin ω) g hg)
    hsrc

/-- The canonical single-grid oracle cost ledger, including `G-1` controlled marks and one final
evaluation. -/
def recordLedger (G : ℕ) : OracleCostLedger where
  sourceEvaluations := G
  controlledMarks := G - 1
  prepAccesses := 2 * (G - 1) + 1
  sourceReflections := G - 1
  controlMacros := G - 1
  validationQueries := 0
  finalEvaluations := 1
  fixedGates := 5 * (G - 1) + 3

/-- For `G ≥ 2`, the canonical single-grid ledger satisfies the record transport identities. -/
theorem recordLedgerTransport_recordLedger (G : ℕ) (hG : 2 ≤ G) :
    RecordLedgerTransport G (recordLedger G) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  show G = (G - 1) + 1
  omega

/-- For `G ≥ 2`, the counted amplitude estimation circuit realizes the canonical record ledger. -/
theorem circuitRealizesLedger_recordLedger (G : ℕ) (hG : 2 ≤ G) (A : Matrix I I ℂ) (j : I) :
    CircuitRealizesLedger G A j (recordLedger G) := by
  have hl := prepared_ae_access_ledger G (by omega) A j
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (G - 1) = QueryCount (countedAECircuit G A j)
    rw [hl.1]
  · show (5 * (G - 1) + 3) = GateCount (countedAECircuit G A j)
    rw [hl.2.1]
  · show (2 * (G - 1) + 1) = aeInputAccesses (aeAccessWord (I := I) G)
    rw [hl.2.2.1]
  · show (G - 1) = aeSourceReflections (aeAccessWord (I := I) G)
    rw [hl.2.2.2]

/-- A unitary preparation and grid `G ≥ 2` give a unitary counted circuit, a normalized
clean-flag output, and the prescribed label probabilities. -/
theorem recordValidates_of (G : ℕ) (hG : 2 ≤ G) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : RecordValidates G A j S hA hG := by
  have h := prepared_ae_expanded_access_and_output G hG A j S hA
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

/-- A Boolean phase oracle with a controlled implementation satisfies the complete single-record
cost transport specification for `G ≥ 2`. -/
theorem recordOracleCostTransport (A : Matrix I I ℂ) (j : I) (S : Finset I) (O : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hO : BooleanEvaluationOracle O S) (hC : ControlledPhaseImplementation O S)
    (G : ℕ) (hG : 2 ≤ G) : RecordOracleCostTransport G A j S O hA hG :=
  ⟨hO, hC, recordLedger G, recordLedgerTransport_recordLedger G hG,
    circuitRealizesLedger_recordLedger G hG A j, recordValidates_of G hG A j S hA⟩

/-- A Boolean phase oracle and its controlled implementation provide single-record oracle cost
transport for every grid at least two. -/
theorem clause89_record (A : Matrix I I ℂ) (j : I) (S : Finset I) (O : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    BooleanEvaluationOracle O S →
    ControlledPhaseImplementation O S →
    (∀ M : ℕ, ∀ hM : 2 ≤ M, RecordOracleCostTransport M A j S O hA hM) :=
  fun hO hC M hM => recordOracleCostTransport A j S O hA hO hC M hM

/-- The prepared marking matrix is diagonal with entry `-1` on `S` and `1` elsewhere. -/
theorem preparedMark_eq_diagonal (S : Finset I) :
    preparedMark S = Matrix.diagonal fun i => if i ∈ S then (-1 : ℂ) else 1 := by
  ext x y
  simp only [preparedMark, Projector, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    by_cases hx : x ∈ S
    · simp only [hx, if_true]
      norm_num
    · simp only [hx, if_false]
      norm_num
  · simp [hxy]

/-- The prepared marking matrix satisfies the Boolean evaluation oracle specification. -/
theorem booleanEvaluationOracle_preparedMark (S : Finset I) :
    BooleanEvaluationOracle (preparedMark S) S := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x
    rw [preparedMark_eq_diagonal]
    simp
  · intro x y hxy
    rw [preparedMark_eq_diagonal]
    simp [hxy]

/-- The prepared marking matrix is unitary. -/
theorem preparedMark_mem_unitaryGroup (S : Finset I) :
    preparedMark S ∈ Matrix.unitaryGroup I ℂ := by
  have hR : ReflectionAbout (Projector S) ∈ Matrix.unitaryGroup I ℂ :=
    reflectionAbout_unitary (projector_isOrthogonalProjector S)
  have hneg : preparedMark S = -(ReflectionAbout (Projector S)) := by
    unfold preparedMark ReflectionAbout
    module
  rw [hneg, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_neg, neg_mul_neg]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hR
  exact hR

omit [Fintype I] in

/-- The controlled oracle is block diagonal, with the identity on the false block and `U` on the
true block. -/
theorem controlOracle_apply (U : Matrix I I ℂ) (b c : Bool) (x y : I) :
    controlOracle U (b, x) (c, y) =
      if b = c then (if b then U else (1 : Matrix I I ℂ)) x y else 0 :=
  rfl

/-- The prepared marking matrix has the specified unitary controlled-phase implementation. -/
theorem controlledPhaseImplementation_preparedMark (S : Finset I) :
    ControlledPhaseImplementation (preparedMark S) S := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact controlOracle_unitary (preparedMark_mem_unitaryGroup S)
  · intro x y
    simp [controlOracle_apply, Matrix.one_apply]
  · intro x y
    simp [controlOracle_apply]
  · intro x y
    simp [controlOracle_apply]

/-- The identity matrix on a finite index type is unitary. -/
theorem one_mem_unitaryGroup (n : Type) [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp

/-- The universal basic counting transport statement without positivity of final grids is false. -/
theorem clause89_basic_false :
    ¬ (∀ (L : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (exec : Ω → Fin L → Bool) (Mfin sourceLedger : Ω → ℕ),
      (∀ ω, sourceLedger ω =
        (recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω)).sum) →
      JointRecordOracleCostTransport w
        (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
        sourceLedger) := by
  intro h
  let exec : Fin 1 → Fin 0 → Bool := fun _ _ => false
  let Mfin : Fin 1 → ℕ := fun _ => 0
  let w : Fin 1 → ℝ := fun _ => 0
  let gridsOf : Fin 1 → List ℕ := fun ω =>
    recordGrids (fun l : Fin 0 => 2 * 2 ^ l.val) (exec ω) (Mfin ω)
  let sourceLedger : Fin 1 → ℕ := fun ω => (gridsOf ω).sum
  have hsrc : ∀ ω, sourceLedger ω = (gridsOf ω).sum := fun _ => rfl
  have hjoint : JointRecordOracleCostTransport w gridsOf sourceLedger :=
    h 0 (Fin 1) w exec Mfin sourceLedger hsrc
  have hzero : (0 : ℕ) ∈ gridsOf 0 := by
    show (0 : ℕ) ∈ recordGrids (fun l : Fin 0 => 2 * 2 ^ l.val) (exec 0) (Mfin 0)
    simp only [Mfin]
    exact zero_mem_recordGrids_zero (fun l : Fin 0 => 2 * 2 ^ l.val) (exec 0)
  exact not_jointRecordOracleCostTransport_of_zero_mem w gridsOf sourceLedger 0 hzero hjoint

/-- The universal two-rough-grid counting transport statement without grid positivity
assumptions is false. -/
theorem clause89_exact_false :
    ¬ (∀ (M0 : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (Mfin sourceLedger : Ω → ℕ),
      (∀ ω, sourceLedger ω =
        (recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω)).sum) →
      JointRecordOracleCostTransport w
        (fun ω => recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω))
        sourceLedger) := by
  intro h
  let Mfin : Fin 1 → ℕ := fun _ => 0
  let w : Fin 1 → ℝ := fun _ => 0
  let gridsOf : Fin 1 → List ℕ := fun ω =>
    recordGrids (fun _ : Fin 2 => (0 : ℕ)) (fun _ => true) (Mfin ω)
  let sourceLedger : Fin 1 → ℕ := fun ω => (gridsOf ω).sum
  have hsrc : ∀ ω, sourceLedger ω = (gridsOf ω).sum := fun _ => rfl
  have hjoint : JointRecordOracleCostTransport w gridsOf sourceLedger :=
    h 0 (Fin 1) w Mfin sourceLedger hsrc
  have hzero : (0 : ℕ) ∈ gridsOf 0 := by
    show (0 : ℕ) ∈ recordGrids (fun _ : Fin 2 => (0 : ℕ)) (fun _ => true) (Mfin 0)
    simp only [Mfin]
    exact zero_mem_recordGrids_zero (fun _ : Fin 2 => (0 : ℕ)) (fun _ => true)
  exact not_jointRecordOracleCostTransport_of_zero_mem w gridsOf sourceLedger 0 hzero hjoint

/-- Collects single-record cost transport and the basic and exact counting path transport
guarantees under their grid positivity assumptions. -/
theorem clause89_fixed :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (O : Matrix I I ℂ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ),
    BooleanEvaluationOracle O S →
    ControlledPhaseImplementation O S →
    (∀ M : ℕ, ∀ hM : 2 ≤ M, RecordOracleCostTransport M A j S O hA hM) ∧
    (∀ (L : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (exec : Ω → Fin L → Bool) (Mfin sourceLedger : Ω → ℕ),
      (∀ ω, 1 ≤ Mfin ω) →
      (∀ ω, sourceLedger ω =
        (recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω)).sum) →
      JointRecordOracleCostTransport w
        (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
        sourceLedger) ∧
    (∀ (M0 : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (Mfin sourceLedger : Ω → ℕ),
      1 ≤ M0 →
      (∀ ω, 1 ≤ Mfin ω) →
      (∀ ω, sourceLedger ω =
        (recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω)).sum) →
      JointRecordOracleCostTransport w
        (fun ω => recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω))
        sourceLedger) :=
  fun _I _inst₁ _inst₂ A j S O hA hO hC =>
    ⟨clause89_record A j S O hA hO hC,
      fun L Ω _instΩ w exec Mfin sourceLedger hMfin hsrc =>
        clause89_basic_of_pos L Ω w exec Mfin sourceLedger hMfin hsrc,
      fun M0 Ω _instΩ w Mfin sourceLedger hM0 hMfin hsrc =>
        clause89_exact_of_pos M0 Ω w Mfin sourceLedger hM0 hMfin hsrc⟩

/-- The combined universal record and path transport statement without grid positivity
assumptions is false. -/
theorem clause89_false :
    ¬ (∀ (I : Type) [Fintype I] [DecidableEq I]
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (O : Matrix I I ℂ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ),
    BooleanEvaluationOracle O S →
    ControlledPhaseImplementation O S →
    (∀ M : ℕ, ∀ hM : 2 ≤ M, RecordOracleCostTransport M A j S O hA hM) ∧
    (∀ (L : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (exec : Ω → Fin L → Bool) (Mfin sourceLedger : Ω → ℕ),
      (∀ ω, sourceLedger ω =
        (recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω)).sum) →
      JointRecordOracleCostTransport w
        (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
        sourceLedger) ∧
    (∀ (M0 : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (Mfin sourceLedger : Ω → ℕ),
      (∀ ω, sourceLedger ω =
        (recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω)).sum) →
      JointRecordOracleCostTransport w
        (fun ω => recordGrids (fun _ : Fin 2 => M0) (fun _ => true) (Mfin ω))
        sourceLedger)) := by
  intro h
  apply clause89_basic_false
  intro L Ω _instΩ w exec Mfin sourceLedger hsrc
  exact (h (Fin 1) (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 (∅ : Finset (Fin 1))
    (preparedMark (∅ : Finset (Fin 1))) (one_mem_unitaryGroup (Fin 1))
    (booleanEvaluationOracle_preparedMark (∅ : Finset (Fin 1)))
    (controlledPhaseImplementation_preparedMark (∅ : Finset (Fin 1)))).2.1
    L Ω w exec Mfin sourceLedger hsrc

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
