/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleFindingDefs
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphSUCSourceCorrectedQuan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.WalkSearch.Primitives

open Qatlib
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

theorem clause21 : Qatlib.Concepts.WalkSearch.Primitives.StoredCheckerNativeSpec := by
  intro n adj hs hl U
  refine ⟨⟨[Step.query], [Step.query], by simp, rfl, by simp, rfl, ?_, ?_⟩,
    storedReplay_setup adj U, storedReplay_update adj hs hl U, ?_⟩
  · intro p _
    rw [run_query_bitOracleOn_ket]
    simp
  · intro v p _
    rw [run_query_bitOracleOn_ket]
    simp
  · intro kcs ncs r' c₀ hk hn stape ntape
    exact (freshValidationChecker_answer n adj U kcs ncs r' c₀ hk hn).2.2 stape ntape

theorem clause22 : Qatlib.Concepts.WalkSearch.Primitives.RealExponentTh5Spec := by
  refine ⟨realExponentTransport_answer, ?_⟩
  intro kcs hκ
  have hκR : (0 : ℝ) < (kcs.κ : ℝ) := by exact_mod_cast (by omega : 0 < kcs.κ)
  refine ⟨2 * (kcs.κ : ℝ) * (4 + 1 + 4), by linarith, ?_⟩
  intro k hk n hn H hv adj
  obtain ⟨r, hr, hl, hu⟩ := correctedSubsetWindow (n ^ (k - 1)) k (pow_pos hn _) (by omega)
  refine ⟨r, 1, fun _ => PMF.pure emptySearchTrace, hr, hl, hu, ?_, ?_, ?_⟩
  · intro K tr htr
    have htr' : tr ∈ (PMF.pure emptySearchTrace).support := htr
    rw [PMF.mem_support_pure_iff] at htr'
    subst htr'
    exact ⟨fun w hw => by simp [emptySearchTrace] at hw, by simp [emptySearchTrace]⟩
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hn1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (r : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
      Real.one_le_rpow (by exact_mod_cast hr) (by positivity)
    rw [Nat.cast_one]
    have h3 : (1 : ℝ) ≤
        (n : ℝ) ^ ((1 : ℝ) / 2) * ((r : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
      nlinarith [h1, h2, sq_nonneg ((n : ℝ) ^ ((1 : ℝ) / 2) - 1),
        sq_nonneg ((r : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) - 1)]
    linarith
  · intro stape
    have hc := kcs.charges r (hCandRel adj H hv) (r * r) r 1 (stape 0)
    have hraw : (hAlg adj H hv kcs r 1 stape).2 ≤
        kcs.κ * (Nat.log 2 (n + 1) + 2) *
          (r * r + (n / r) ^ ((k - 1) / 2) * (1 + Nat.sqrt r * r)) := by
      cases he : kcs.run r (hCandRel adj H hv) (r * r) r 1 (stape 0) with
      | none => simpa only [hAlg, he] using hc
      | some K => simp only [hAlg, he]; split_ifs <;> exact hc
    have hnum := least_power_numeric_charge n k r 1 1 hn hk hr hl hu (by omega)
    rw [Nat.cast_one] at hnum
    have hlog : ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) ≤
        2 * ((Nat.log 2 n + 2 : ℕ) : ℝ) := by exact_mod_cast corrected_log_succ_le n hn
    have hL : (2 : ℝ) ≤ ((Nat.log 2 n + 2 : ℕ) : ℝ) :=
      by exact_mod_cast (show 2 ≤ Nat.log 2 n + 2 by omega)
    have hL3 : ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤ ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 3 := by
      nlinarith [sq_nonneg (((Nat.log 2 n + 2 : ℕ) : ℝ) - 1)]
    calc
      ((hAlg adj H hv kcs r 1 stape).2 : ℝ) ≤
          (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
            (((r * r + (n / r) ^ ((k - 1) / 2) * (1 + Nat.sqrt r * r) : ℕ)) : ℝ) :=
        by exact_mod_cast hraw
      _ ≤ (kcs.κ : ℝ) * (2 * ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 3) *
          ((4 + (1 : ℝ) + 4) * (n : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hlog.trans (by linarith)) (Nat.cast_nonneg _))
          hnum (by positivity) (by positivity)
      _ = _ := by ring

private theorem list_head?_mem {α : Type} {l : List α} {t : α} (ht : l.head? = some t) :
    t ∈ l := by
  cases l with
  | nil => simp at ht
  | cons a as =>
    simp only [List.head?_cons, Option.some.injEq] at ht
    subst ht
    simp

private theorem list_head?_ne_none_of_mem {α : Type} {l : List α} {t : α} (hmem : t ∈ l) :
    l.head? ≠ none := by
  cases l with
  | nil => simp at hmem
  | cons a as => simp

theorem clause24 : Qatlib.Concepts.WalkSearch.Primitives.FiniteSmallBranchSpec := by
  intro _ _ _
  refine ⟨1, ?_⟩
  intro n _hn _hdj adj _hs hl
  refine ⟨by simp only [triangleScan, Nat.le_refl], ?_, ?_⟩
  · intro t ht
    simp only [triangleScan] at ht
    have hmem : t ∈ (Finset.univ.filter (fun s : Fin n × Fin n × Fin n =>
        decide (s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2 ∧
          adj s.1 s.2.1 ∧ adj s.1 s.2.2 ∧ adj s.2.1 s.2.2))).toList :=
      list_head?_mem ht
    exact of_decide_eq_true (Finset.mem_filter.mp (Finset.mem_toList.mp hmem)).2
  · rintro ⟨t, ht⟩
    rw [triRel, decide_eq_true_eq] at ht
    obtain ⟨hne, hadj, w, hw1, hw2⟩ := ht
    have hw0 : w ≠ t 0 := by
      intro h
      subst h
      rw [hl (t 0)] at hw1
      simp at hw1
    have hw1' : w ≠ t 1 := by
      intro h
      subst h
      rw [hl (t 1)] at hw2
      simp at hw2
    have hmem : (t 0, t 1, w) ∈ (Finset.univ.filter (fun s : Fin n × Fin n × Fin n =>
        decide (s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2 ∧
          adj s.1 s.2.1 ∧ adj s.1 s.2.2 ∧ adj s.2.1 s.2.2))).toList := by
      refine Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      simp only [decide_eq_true_eq]
      exact ⟨hne, hw0.symm, hw1'.symm, hadj, hw1, hw2⟩
    intro hnone
    simp only [triangleScan] at hnone
    exact list_head?_ne_none_of_mem hmem hnone

end Qatlib.Concepts.WalkSearch.Primitives
