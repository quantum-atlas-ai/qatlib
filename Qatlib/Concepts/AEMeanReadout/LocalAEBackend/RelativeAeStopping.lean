/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeCertifiedStopping
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix Filter
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw
open Qatlib
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped BigOperators Classical Topology
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev FreshBlock (r : ℕ → ℕ) (k : ℕ) := Fin (2 * r k + 1) → Fin (adaptiveGrid k)

abbrev FreshHistory (r : ℕ → ℕ) (N : ℕ) := ∀ k : Fin N, FreshBlock r k.val

noncomputable def freshHistoryLaw (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    FinDist (FreshHistory r N) :=
  independent (fun k => freshStageLaw k.val (r k.val) A j S hA)

def freshHistoryReady (eps : ℝ) (r : ℕ → ℕ) {N : ℕ} (ω : FreshHistory r N) (k : Fin N) : Prop :=
  freshMedianReady eps (adaptiveGrid k.val) (r k.val) (ω k)

def freshHistoryWindowBad (r : ℕ → ℕ) {N : ℕ} (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (ω : FreshHistory r N) (k : Fin N) : Prop :=
  nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S) <
    |freshMedianEstimate (adaptiveGrid k.val) (r k.val) (ω k)
      - MeasureProb (preparedAAState A j) S|

def freshHistoryRelativeBad (eps : ℝ) (r : ℕ → ℕ) {N : ℕ}
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (ω : FreshHistory r N) (k : Fin N) : Prop :=
  eps * MeasureProb (preparedAAState A j) S <
    |freshMedianEstimate (adaptiveGrid k.val) (r k.val) (ω k)
      - MeasureProb (preparedAAState A j) S|

def freshHistoryFirstStop (eps : ℝ) (r : ℕ → ℕ) {N : ℕ}
    (ω : FreshHistory r N) (k : Fin N) : Prop :=
  freshHistoryReady eps r ω k ∧ ∀ l < k, ¬ freshHistoryReady eps r ω l

def freshHistoryPending (eps : ℝ) (r : ℕ → ℕ) {N : ℕ} (ω : FreshHistory r N) : Prop :=
  ∀ k, ¬ freshHistoryReady eps r ω k

noncomputable def freshHistoryStopMass (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (k : Fin N) : ℝ :=
  eventMass (freshHistoryLaw r N A j S hA) (fun ω => freshHistoryFirstStop eps r ω k)

noncomputable def freshHistoryPendingMass (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) : ℝ :=
  eventMass (freshHistoryLaw r N A j S hA) (freshHistoryPending eps r)

noncomputable def freshHistoryFailureMass (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) : ℝ :=
  eventMass (freshHistoryLaw r N A j S hA) (fun ω =>
    ∃ k, freshHistoryFirstStop eps r ω k ∧ freshHistoryRelativeBad eps r A j S ω k)

theorem independent_marginal {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (k : J) (g : X k → ℝ) :
    (independent p).expect (fun ω => g (ω k)) = (p k).expect g := by
  classical
  let g' : ∀ m, X m → ℝ := fun m x => if h : m = k then g (h ▸ x) else 1
  have hsplit (ω : ∀ i, X i) :
      g (ω k) = ∏ m, g' m (ω m) := by
    rw [Finset.prod_eq_single k]
    · simp [g']
    · intro m _ hm
      simp [g', hm]
    · simp
  have hrewrite : (independent p).expect (fun ω => g (ω k))
      = (independent p).expect (fun ω => ∏ m, g' m (ω m)) := by
    apply Finset.sum_congr rfl
    intro ω _
    change (independent p).prob ω * g (ω k) = _
    rw [hsplit ω]
  rw [hrewrite, independent_expect_prod p g']
  rw [Finset.prod_eq_single k]
  · simp [g']
  · intro m _ hm
    simp [g', hm, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, (p m).sum_one]
  · simp

theorem freshHistory_coordinate_event (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (k : Fin N) (E : FreshBlock r k.val → Prop) [DecidablePred E] :
    eventMass (freshHistoryLaw r N A j S hA) (fun ω => E (ω k))
      = eventMass (freshStageLaw k.val (r k.val) A j S hA) E := by
  classical
  rw [eventMass_eq_expect, eventMass_eq_expect]
  exact independent_marginal (fun k => freshStageLaw k.val (r k.val) A j S hA) k
    (fun x => if E x then (1 : ℝ) else 0)

theorem eventMass_congr {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) {E F : X → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ x, E x ↔ F x) : eventMass p E = eventMass p F := by
  classical
  unfold eventMass
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x
  · intro x _
    rfl

theorem freshHistoryFirstStop_unique (eps : ℝ) (r : ℕ → ℕ) {N : ℕ}
    {ω : FreshHistory r N} {k l : Fin N}
    (hk : freshHistoryFirstStop eps r ω k) (hl : freshHistoryFirstStop eps r ω l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact (hl.2 k h hk.1).elim
  · exact h
  · exact (hk.2 l h hl.1).elim

theorem freshHistory_pending_or_stop (eps : ℝ) (r : ℕ → ℕ) {N : ℕ} (ω : FreshHistory r N) :
    freshHistoryPending eps r ω ∨ ∃ k, freshHistoryFirstStop eps r ω k := by
  classical
  by_cases hp : freshHistoryPending eps r ω
  · exact Or.inl hp
  · right
    obtain ⟨k, hk⟩ := not_forall.mp hp
    have hk' : freshHistoryReady eps r ω k := not_not.mp hk
    let P : ℕ → Prop := fun n => ∃ hn : n < N, freshHistoryReady eps r ω ⟨n, hn⟩
    have hex : ∃ n, P n := ⟨k.val, k.isLt, hk'⟩
    let k0 : Fin N := ⟨Nat.find hex, (Nat.find_spec hex).1⟩
    refine ⟨k0, (Nat.find_spec hex).2, ?_⟩
    intro l hl
    have hlt : l.val < Nat.find hex := hl
    have hnone := Nat.find_min hex hlt
    intro hr
    exact hnone ⟨l.isLt, hr⟩

theorem freshHistory_stop_partition (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    freshHistoryPendingMass eps r N A j S hA
      + (∑ k, freshHistoryStopMass eps r N A j S hA k) = 1 := by
  classical
  let law := freshHistoryLaw r N A j S hA
  have hsum : (∑ k, freshHistoryStopMass eps r N A j S hA k)
      = law.expect (fun ω => ∑ k, (if freshHistoryFirstStop eps r ω k then (1 : ℝ) else 0)) := by
    simp_rw [freshHistoryStopMass, eventMass_eq_expect]
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    calc
      (∑ k, ∑ ω, law.prob ω * (if freshHistoryFirstStop eps r ω k then (1 : ℝ) else 0))
          = ∑ ω, ∑ k, law.prob ω * (if freshHistoryFirstStop eps r ω k then (1 : ℝ) else 0) :=
        Finset.sum_comm
      _ = ∑ ω, law.prob ω * ∑ k, (if freshHistoryFirstStop eps r ω k then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.mul_sum]
  rw [freshHistoryPendingMass, eventMass_eq_expect, hsum]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ ω, law.prob ω * 1 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [← mul_add]
      have hpoint : (if freshHistoryPending eps r ω then (1 : ℝ) else 0)
          + (∑ k, if freshHistoryFirstStop eps r ω k then (1 : ℝ) else 0) = 1 := by
        by_cases hp : freshHistoryPending eps r ω
        · have hnone : ∀ k, ¬ freshHistoryFirstStop eps r ω k := by
            intro k hk
            exact hp k hk.1
          simp [hp, hnone]
        · obtain ⟨k, hk⟩ := (freshHistory_pending_or_stop eps r ω).resolve_left hp
          have heq (l : Fin N) : freshHistoryFirstStop eps r ω l ↔ l = k := by
            constructor
            · intro hl
              exact freshHistoryFirstStop_unique eps r hl hk
            · intro h
              simpa [h] using! hk
          simp [hp, heq]
      rw [hpoint]
    _ = 1 := by simpa only [mul_one] using! law.sum_one

theorem freshHistoryFailureMass_le_window_union (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (heps : 0 < eps) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    freshHistoryFailureMass eps r N A j S hA ≤
      ∑ k, eventMass (freshHistoryLaw r N A j S hA) (fun ω =>
        freshHistoryFirstStop eps r ω k ∧ freshHistoryWindowBad r A j S ω k) := by
  classical
  calc
    freshHistoryFailureMass eps r N A j S hA
        ≤ eventMass (freshHistoryLaw r N A j S hA) (fun ω =>
          ∃ k, freshHistoryFirstStop eps r ω k ∧ freshHistoryWindowBad r A j S ω k) := by
      apply eventMass_mono
      intro ω hω
      obtain ⟨k, hstop, hbad⟩ := hω
      refine ⟨k, hstop, ?_⟩
      by_contra hgood
      exact (not_le.mpr hbad) (freshMedian_relative_band (adaptiveGrid_pos k.val)
        A j S hA (ω k) eps heps ha1 (le_of_not_gt hgood) hstop.1)
    _ ≤ _ := by
      convert! (eventMass_exists_le_sum (freshHistoryLaw r N A j S hA)
        (fun k ω => freshHistoryFirstStop eps r ω k ∧ freshHistoryWindowBad r A j S ω k)) using 1
      unfold eventMass
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem freshHistory_stop_windowBad_le (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (k : Fin N) :
    eventMass (freshHistoryLaw r N A j S hA) (fun ω =>
      freshHistoryFirstStop eps r ω k ∧ freshHistoryWindowBad r A j S ω k)
      ≤ (8 / 9 : ℝ) ^ (r k.val) := by
  classical
  calc
    _ ≤ eventMass (freshHistoryLaw r N A j S hA) (fun ω => freshHistoryWindowBad r A j S ω k) := by
      apply eventMass_mono
      intro ω hω
      exact hω.2
    _ = eventMass (freshStageLaw k.val (r k.val) A j S hA) (fun x =>
        nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid k.val) (r k.val) x
            - MeasureProb (preparedAAState A j) S|) := by
      simpa only [freshHistoryWindowBad] using!
        (freshHistory_coordinate_event r N A j S hA k (fun x =>
          nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S) <
            |freshMedianEstimate (adaptiveGrid k.val) (r k.val) x
              - MeasureProb (preparedAAState A j) S|))
    _ ≤ _ := freshStageLaw_window_failure k.val (r k.val) A j S hA

theorem freshHistoryFailureMass_le_sum (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (heps : 0 < eps) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    freshHistoryFailureMass eps r N A j S hA ≤ ∑ k : Fin N, (8 / 9 : ℝ) ^ (r k.val) := by
  calc
    _ ≤ _ := freshHistoryFailureMass_le_window_union eps r N A j S hA heps ha1
    _ ≤ _ := Finset.sum_le_sum fun k _ => freshHistory_stop_windowBad_le eps r N A j S hA k

noncomputable def relativeAeFineIndex (eps a : ℝ) : ℕ :=
  Nat.ceil (32 * Real.pi / (eps * Real.sqrt a))

theorem relativeAeFineIndex_spec (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a) :
    32 * Real.pi ≤ eps * (adaptiveGrid (relativeAeFineIndex eps a) : ℝ) * Real.sqrt a := by
  have hden : 0 < eps * Real.sqrt a := mul_pos heps (Real.sqrt_pos.2 ha0)
  have hceil : 32 * Real.pi / (eps * Real.sqrt a) ≤ (relativeAeFineIndex eps a : ℝ) :=
    Nat.le_ceil _
  have hindex : relativeAeFineIndex eps a ≤ adaptiveGrid (relativeAeFineIndex eps a) := by
    have h := adaptiveGrid_ge_two_add_k (relativeAeFineIndex eps a)
    omega
  have hgrid : (relativeAeFineIndex eps a : ℝ)
      ≤ (adaptiveGrid (relativeAeFineIndex eps a) : ℝ) := by exact_mod_cast hindex
  have hratio : 32 * Real.pi / (eps * Real.sqrt a)
      ≤ (adaptiveGrid (relativeAeFineIndex eps a) : ℝ) := hceil.trans hgrid
  have hmul := (div_le_iff₀ hden).mp hratio
  nlinarith

theorem relativeAeFineIndex_spec_at (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a)
    {k : ℕ} (hk : relativeAeFineIndex eps a ≤ k) :
    32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ) * Real.sqrt a := by
  have hbase := relativeAeFineIndex_spec eps a heps ha0
  have hgridNat : adaptiveGrid (relativeAeFineIndex eps a) ≤ adaptiveGrid k := by
    unfold adaptiveGrid
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hgrid : (adaptiveGrid (relativeAeFineIndex eps a) : ℝ) ≤ (adaptiveGrid k : ℝ) := by
    exact_mod_cast hgridNat
  have hmul := mul_le_mul_of_nonneg_left hgrid
    (mul_nonneg heps.le (Real.sqrt_nonneg a))
  nlinarith

theorem relativeAeFine_exists (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a) :
    ∃ k : ℕ, 32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ) * Real.sqrt a :=
  ⟨relativeAeFineIndex eps a, relativeAeFineIndex_spec eps a heps ha0⟩

noncomputable def relativeAeLeastFineIndex (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a) : ℕ :=
  Nat.find (relativeAeFine_exists eps a heps ha0)

theorem relativeAeLeastFineIndex_spec (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a) :
    32 * Real.pi ≤ eps * (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) * Real.sqrt a :=
  Nat.find_spec (relativeAeFine_exists eps a heps ha0)

theorem relativeAeLeastFineIndex_not_fine (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a)
    {k : ℕ} (hk : k < relativeAeLeastFineIndex eps a heps ha0) :
    ¬ 32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ) * Real.sqrt a :=
  Nat.find_min (relativeAeFine_exists eps a heps ha0) hk

theorem relativeAeLeastFineIndex_spec_at (eps a : ℝ) (heps : 0 < eps) (ha0 : 0 < a)
    {k : ℕ} (hk : relativeAeLeastFineIndex eps a heps ha0 ≤ k) :
    32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ) * Real.sqrt a := by
  have hbase := relativeAeLeastFineIndex_spec eps a heps ha0
  have hgridNat : adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) ≤ adaptiveGrid k := by
    unfold adaptiveGrid
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hgrid : (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) ≤
      (adaptiveGrid k : ℝ) := by exact_mod_cast hgridNat
  have hmul := mul_le_mul_of_nonneg_left hgrid
    (mul_nonneg heps.le (Real.sqrt_nonneg a))
  nlinarith

theorem relativeAeLeastFineIndex_grid_upper (eps a : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) ≤
      64 * Real.pi / (eps * Real.sqrt a) := by
  let K := relativeAeLeastFineIndex eps a heps ha0
  have hden : 0 < eps * Real.sqrt a := mul_pos heps (Real.sqrt_pos.2 ha0)
  by_cases hK : K = 0
  · have hsqrt1 : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha1
    have hprod : eps * Real.sqrt a ≤ 1 := by
      nlinarith [Real.sqrt_nonneg a]
    dsimp [K] at hK
    rw [hK]
    norm_num [adaptiveGrid]
    apply (le_div_iff₀ hden).mpr
    nlinarith [Real.pi_gt_three]
  · have hKpos : 0 < K := by omega
    have hprev := relativeAeLeastFineIndex_not_fine eps a heps ha0
      (show K - 1 < K by omega)
    have hlt : eps * (adaptiveGrid (K - 1) : ℝ) * Real.sqrt a < 32 * Real.pi :=
      lt_of_not_ge hprev
    have hs := adaptiveGrid_succ (K - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ K)] at hs
    change (adaptiveGrid K : ℝ) ≤ _
    rw [hs]
    push_cast
    apply (le_div_iff₀ hden).mpr
    nlinarith

theorem relativeAe_coarse_backward_weight (eps a : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) {k : ℕ}
    (hk : k < relativeAeLeastFineIndex eps a heps ha0)
    (hη : ¬ Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4 ≤ 1 / 16) :
    1 ≤ (128 * Real.pi ^ 2 / eps) *
      (1 / 2 : ℝ) ^ (relativeAeLeastFineIndex eps a heps ha0 - k) := by
  let K := relativeAeLeastFineIndex eps a heps ha0
  have hMr : (0 : ℝ) < adaptiveGrid k := by exact_mod_cast adaptiveGrid_pos k
  have hηlt : 1 / 16 < Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4 := lt_of_not_ge hη
  have hη4 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hηlt
  have hs : 1 / 4 < ((adaptiveGrid k : ℝ) * Real.sqrt a) ^ 2 * Real.pi ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha0.le]
    nlinarith
  have hs' : (1 / (2 * Real.pi)) ^ 2 < ((adaptiveGrid k : ℝ) * Real.sqrt a) ^ 2 := by
    have hdiv : (1 / 4) / Real.pi ^ 2 < ((adaptiveGrid k : ℝ) * Real.sqrt a) ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr hs
    convert! hdiv using 1
    ring
  have hlarge : 1 / (2 * Real.pi) < (adaptiveGrid k : ℝ) * Real.sqrt a :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mp hs'
  have hgrid : (adaptiveGrid K : ℝ) =
      (2 : ℝ) ^ (K - k) * (adaptiveGrid k : ℝ) := by
    unfold adaptiveGrid
    push_cast
    rw [show K + 1 = (K - k) + (k + 1) by omega, pow_add]
  have hupper := relativeAeLeastFineIndex_grid_upper eps a heps heps1 ha0 ha1
  change (adaptiveGrid K : ℝ) ≤ _ at hupper
  have hscale : (2 : ℝ) ^ (K - k) * (1 / (2 * Real.pi)) ≤ 64 * Real.pi / eps := by
    calc
      _ ≤ (2 : ℝ) ^ (K - k) * ((adaptiveGrid k : ℝ) * Real.sqrt a) :=
        mul_le_mul_of_nonneg_left hlarge.le (by positivity)
      _ = (adaptiveGrid K : ℝ) * Real.sqrt a := by rw [hgrid]; ring
      _ ≤ (64 * Real.pi / (eps * Real.sqrt a)) * Real.sqrt a :=
        mul_le_mul_of_nonneg_right hupper (Real.sqrt_nonneg a)
      _ = 64 * Real.pi / eps := by
        field_simp [ne_of_gt heps, ne_of_gt (Real.sqrt_pos.2 ha0)]
  have hpow : (2 : ℝ) ^ (K - k) ≤ 128 * Real.pi ^ 2 / eps := by
    apply (le_div_iff₀ heps).mpr
    have hm := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ 2 * eps * Real.pi by positivity)
    have hleft : 2 * eps * Real.pi * ((2 : ℝ) ^ (K - k) * (1 / (2 * Real.pi))) =
        (2 : ℝ) ^ (K - k) * eps := by
      field_simp [Real.pi_ne_zero]
    have hright : 2 * eps * Real.pi * (64 * Real.pi / eps) = 128 * Real.pi ^ 2 := by
      field_simp [ne_of_gt heps]
      ring
    rw [hleft, hright] at hm
    exact hm
  have hweight : 1 ≤ (128 * Real.pi ^ 2 / eps) / (2 : ℝ) ^ (K - k) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul] using! hpow
  change 1 ≤ (128 * Real.pi ^ 2 / eps) * (1 / 2 : ℝ) ^ (K - k)
  simpa only [div_eq_mul_inv, one_div, one_mul, inv_pow] using! hweight

theorem freshHistoryPendingMass_le_of_fine (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r : ℕ → ℕ) (N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) (k : Fin N)
    (hfine : 32 * Real.pi ≤ eps * (adaptiveGrid k.val : ℝ)
      * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    freshHistoryPendingMass eps r N A j S hA ≤ (8 / 9 : ℝ) ^ (r k.val) := by
  classical
  calc
    freshHistoryPendingMass eps r N A j S hA
        ≤ eventMass (freshHistoryLaw r N A j S hA)
            (fun ω => freshHistoryWindowBad r A j S ω k) := by
      apply eventMass_mono
      intro ω hp
      by_contra hbad
      exact hp k (freshMedian_fires_at_fine_stage eps heps heps1 A j S hA ha0 ha1
        (le_of_not_gt hbad) hfine)
    _ = eventMass (freshStageLaw k.val (r k.val) A j S hA) (fun x =>
        nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid k.val) (r k.val) x
            - MeasureProb (preparedAAState A j) S|) := by
      simpa only [freshHistoryWindowBad] using!
        (freshHistory_coordinate_event r N A j S hA k (fun x =>
          nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S) <
            |freshMedianEstimate (adaptiveGrid k.val) (r k.val) x
              - MeasureProb (preparedAAState A j) S|))
    _ ≤ _ := freshStageLaw_window_failure k.val (r k.val) A j S hA

def linearFreshSchedule (r0 k : ℕ) : ℕ := r0 + k

theorem freshHistoryPendingMass_le_public (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) {K : ℕ} (hK : K < N)
    (hfineK : relativeAeFineIndex eps (MeasureProb (preparedAAState A j) S) ≤ K) :
    freshHistoryPendingMass eps (linearFreshSchedule r0) N A j S hA
      ≤ (8 / 9 : ℝ) ^ (r0 + K) := by
  exact freshHistoryPendingMass_le_of_fine eps heps heps1 (linearFreshSchedule r0) N
    A j S hA ha0 ha1 ⟨K, hK⟩
    (relativeAeFineIndex_spec_at eps _ heps ha0 hfineK)

theorem linearFreshSchedule_failure_budget (r0 N : ℕ) :
    (∑ k : Fin N, (8 / 9 : ℝ) ^ (linearFreshSchedule r0 k.val)) ≤ 9 * (8 / 9 : ℝ) ^ r0 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (8 / 9 : ℝ) ^ (linearFreshSchedule r0 k)) N]
  simp_rw [linearFreshSchedule, pow_add]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (8 / 9 : ℝ) ≠ 1)]
  have hgeom : ((8 / 9 : ℝ) ^ N - 1) / ((8 / 9 : ℝ) - 1)
      = 9 * (1 - (8 / 9 : ℝ) ^ N) := by
    rw [div_eq_iff (by norm_num : (8 / 9 : ℝ) - 1 ≠ 0)]
    ring
  rw [hgeom]
  have hpow : 0 ≤ (8 / 9 : ℝ) ^ N := by positivity
  calc
    _ ≤ (8 / 9 : ℝ) ^ r0 * 9 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring

theorem freshHistoryFailureMass_le_nine (eps : ℝ) (heps : 0 < eps) (r0 N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    freshHistoryFailureMass eps (linearFreshSchedule r0) N A j S hA
      ≤ 9 * (8 / 9 : ℝ) ^ r0 :=
  (freshHistoryFailureMass_le_sum eps (linearFreshSchedule r0) N A j S hA heps ha1).trans
    (linearFreshSchedule_failure_budget r0 N)

theorem exists_linearFreshSchedule_failure_budget (eps : ℝ) (heps : 0 < eps) (δ : ℝ) (hδ : 0 < δ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    ∃ r0 : ℕ, ∀ N : ℕ,
      freshHistoryFailureMass eps (linearFreshSchedule r0) N A j S hA ≤ δ := by
  obtain ⟨r0, hr0⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 9 by positivity)
    (show (8 / 9 : ℝ) < 1 by norm_num)
  refine ⟨r0, fun N => (freshHistoryFailureMass_le_nine eps heps r0 N A j S hA ha1).trans ?_⟩
  exact (by nlinarith [hr0] : 9 * (8 / 9 : ℝ) ^ r0 ≤ δ)

theorem freshHistoryPendingMass_vanishes (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, (8 / 9 : ℝ) ^ (r0 + K) < η ∧ ∀ N : ℕ, K < N →
      freshHistoryPendingMass eps (linearFreshSchedule r0) N A j S hA
        ≤ (8 / 9 : ℝ) ^ (r0 + K) := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (show (8 / 9 : ℝ) < 1 by norm_num)
  let K := n + relativeAeFineIndex eps (MeasureProb (preparedAAState A j) S)
  have hsmall : (8 / 9 : ℝ) ^ (r0 + K) < η := by
    apply lt_of_le_of_lt _ hn
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by dsimp [K]; omega)
  refine ⟨K, hsmall, fun N hN => ?_⟩
  exact freshHistoryPendingMass_le_public eps heps heps1 r0 N A j S hA ha0 ha1 hN
    (by dsimp [K]; omega)

def freshZeroBlock (k r : ℕ) : Fin (2 * r + 1) → Fin (adaptiveGrid k) :=
  fun _ => ⟨0, adaptiveGrid_pos k⟩

theorem freshMedianEstimate_zeroBlock (k r : ℕ) :
    freshMedianEstimate (adaptiveGrid k) r (freshZeroBlock k r) = 0 := by
  rw [freshMedianLabel_spec]
  simp [freshMedianLabel, freshZeroBlock, aeEstimate]

theorem freshMedianNotReady_zeroBlock (eps : ℝ) (k r : ℕ) :
    ¬ freshMedianReady eps (adaptiveGrid k) r (freshZeroBlock k r) := by
  intro hready
  have hest := freshMedianEstimate_zeroBlock k r
  have hL : freshMedianLower (adaptiveGrid k) r (freshZeroBlock k r) = 0 := by
    unfold freshMedianLower certifiedLowerBound recordEstimate
    rw [← freshMedianLabel_spec, hest, Real.sqrt_zero]
    have hc := gridCorrection_nonneg (adaptiveGrid_pos k)
    rw [max_eq_left (by linarith)]
    norm_num
  have hU : 0 < freshMedianUpper (adaptiveGrid k) r (freshZeroBlock k r) := by
    unfold freshMedianUpper certifiedUpperBound
    have hc := gridCorrection_pos (adaptiveGrid_pos k)
    positivity
  unfold freshMedianReady at hready
  rw [hL] at hready
  linarith

theorem eventMass_singleton {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (x : X) : eventMass p (fun y => y = x) = p.prob x := by
  classical
  unfold eventMass
  apply Finset.sum_eq_single x
  · intro y hy hyx
    exact (hyx (Finset.mem_filter.mp hy).2).elim
  · intro hx
    simp at hx

theorem eventMass_le_one {X : Type*} [Fintype X]
    (p : FinDist X) (E : X → Prop) [DecidablePred E] : eventMass p E ≤ 1 := by
  classical
  rw [eventMass_eq_expect]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  calc
    (∑ x, p.prob x * (if E x then (1 : ℝ) else 0)) ≤ ∑ x, p.prob x * 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      split <;> norm_num
    _ = 1 := by simpa only [mul_one] using! p.sum_one

theorem freshStageLaw_zeroBlock_prob (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    (freshStageLaw k r A j S hA).prob (freshZeroBlock k r) = 1 := by
  change (∏ i, (adaptiveStageLaw k A j S hA).prob (freshZeroBlock k r i)) = 1
  apply Finset.prod_eq_one
  intro i _
  exact (adaptiveStageLaw_zero k A j S hA 0 ha).1

theorem freshStageLaw_all_zero (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    eventMass (freshStageLaw k r A j S hA)
      (fun ω => ∀ i, ω i = freshZeroBlock k r i) = 1 := by
  classical
  apply le_antisymm (eventMass_le_one _ _)
  have hsingle : eventMass (freshStageLaw k r A j S hA)
      (fun ω => ω = freshZeroBlock k r) = 1 := by
    rw [eventMass_singleton, freshStageLaw_zeroBlock_prob k r A j S hA ha]
  rw [← hsingle]
  apply eventMass_mono
  intro ω hω
  subst ω
  intro i
  rfl

def freshZeroHistory (r : ℕ → ℕ) (N : ℕ) : FreshHistory r N :=
  fun k => freshZeroBlock k.val (r k.val)

theorem freshHistoryLaw_all_zero (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    eventMass (freshHistoryLaw r N A j S hA)
      (fun ω => ∀ k i, ω k i = freshZeroBlock k.val (r k.val) i) = 1 := by
  classical
  have hprob : (freshHistoryLaw r N A j S hA).prob (freshZeroHistory r N) = 1 := by
    change (∏ k : Fin N, (freshStageLaw k.val (r k.val) A j S hA).prob
      (freshZeroBlock k.val (r k.val))) = 1
    apply Finset.prod_eq_one
    intro k _
    exact freshStageLaw_zeroBlock_prob k.val (r k.val) A j S hA ha
  apply le_antisymm (eventMass_le_one _ _)
  have hsingle : eventMass (freshHistoryLaw r N A j S hA)
      (fun ω => ω = freshZeroHistory r N) = 1 := by
    rw [eventMass_singleton, hprob]
  rw [← hsingle]
  apply eventMass_mono
  intro ω hω
  subst ω
  intro k i
  rfl

theorem freshHistoryPendingMass_eq_one_of_zero (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    freshHistoryPendingMass eps r N A j S hA = 1 := by
  classical
  have hall := freshHistoryLaw_all_zero r N A j S hA ha
  have hlow : 1 ≤ freshHistoryPendingMass eps r N A j S hA := by
    rw [← hall]
    apply eventMass_mono
    intro ω hω k
    have hblock : ω k = freshZeroBlock k.val (r k.val) := funext (hω k)
    change ¬ freshMedianReady eps (adaptiveGrid k.val) (r k.val) (ω k)
    rw [hblock]
    exact freshMedianNotReady_zeroBlock eps k.val (r k.val)
  exact le_antisymm (eventMass_le_one _ _) hlow

theorem freshHistoryStopMass_eq_zero_of_zero (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 0) (k : Fin N) :
    freshHistoryStopMass eps r N A j S hA k = 0 := by
  classical
  have hpartition := freshHistory_stop_partition eps r N A j S hA
  rw [freshHistoryPendingMass_eq_one_of_zero eps r N A j S hA ha] at hpartition
  have hsum_nonneg : 0 ≤ ∑ l, freshHistoryStopMass eps r N A j S hA l := by
    apply Finset.sum_nonneg
    intro l _
    exact eventMass_nonneg _ _
  have hk_le : freshHistoryStopMass eps r N A j S hA k
      ≤ ∑ l, freshHistoryStopMass eps r N A j S hA l := by
    exact Finset.single_le_sum
      (fun l _ => show 0 ≤ freshHistoryStopMass eps r N A j S hA l from eventMass_nonneg _ _)
      (Finset.mem_univ k)
  have hk_nonneg : 0 ≤ freshHistoryStopMass eps r N A j S hA k := eventMass_nonneg _ _
  linarith

def freshHistoryActive (eps : ℝ) (r : ℕ → ℕ) {N : ℕ}
    (ω : FreshHistory r N) (k : Fin N) : Prop :=
  ∀ l < k, ¬ freshHistoryReady eps r ω l

def freshStageForwardCost (r : ℕ → ℕ) (k : ℕ) : ℕ :=
  (2 * r k + 1) * adaptiveGrid k

noncomputable def freshHistoryConsumedForward (eps : ℝ) (r : ℕ → ℕ) {N : ℕ}
    (ω : FreshHistory r N) : ℕ :=
  ∑ k, if freshHistoryActive eps r ω k then freshStageForwardCost r k.val else 0

noncomputable def freshHistoryExpectedForward (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) : ℝ :=
  (freshHistoryLaw r N A j S hA).expect
    (fun ω => (freshHistoryConsumedForward eps r ω : ℝ))

theorem freshHistoryExpectedForward_eq_sum (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    freshHistoryExpectedForward eps r N A j S hA =
      ∑ k : Fin N, (freshStageForwardCost r k.val : ℝ) *
        eventMass (freshHistoryLaw r N A j S hA) (fun ω => freshHistoryActive eps r ω k) := by
  classical
  simp_rw [freshHistoryExpectedForward, freshHistoryConsumedForward, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero]
  simp_rw [eventMass_eq_expect]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  calc
    (∑ ω, (freshHistoryLaw r N A j S hA).prob ω *
        ∑ k, if freshHistoryActive eps r ω k then (freshStageForwardCost r k.val : ℝ) else 0)
        = ∑ ω, ∑ k, (freshHistoryLaw r N A j S hA).prob ω *
            (if freshHistoryActive eps r ω k then (freshStageForwardCost r k.val : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum]
    _ = ∑ k : Fin N, ∑ ω, (freshHistoryLaw r N A j S hA).prob ω *
          (if freshHistoryActive eps r ω k then (freshStageForwardCost r k.val : ℝ) else 0) :=
      Finset.sum_comm
    _ = ∑ k : Fin N, (freshStageForwardCost r k.val : ℝ) *
          ∑ ω, (freshHistoryLaw r N A j S hA).prob ω *
            (if freshHistoryActive eps r ω k then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hk : freshHistoryActive eps r ω k <;> simp [hk, mul_comm]

theorem freshHistoryActiveMass_le_of_fine_prev (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r : ℕ → ℕ) (N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) {k : Fin N} (hk : 0 < k.val)
    (hfine : 32 * Real.pi ≤ eps * (adaptiveGrid (k.val - 1) : ℝ)
      * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    eventMass (freshHistoryLaw r N A j S hA) (fun ω => freshHistoryActive eps r ω k)
      ≤ (8 / 9 : ℝ) ^ (r (k.val - 1)) := by
  classical
  let kp : Fin N := ⟨k.val - 1, by omega⟩
  have hfine' : 32 * Real.pi ≤ eps * (adaptiveGrid kp.val : ℝ)
      * Real.sqrt (MeasureProb (preparedAAState A j) S) := by
    simpa only [kp] using! hfine
  calc
    eventMass (freshHistoryLaw r N A j S hA) (fun ω => freshHistoryActive eps r ω k)
        ≤ eventMass (freshHistoryLaw r N A j S hA)
            (fun ω => freshHistoryWindowBad r A j S ω kp) := by
      apply eventMass_mono
      intro ω hactive
      by_contra hbad
      have hready := freshMedian_fires_at_fine_stage eps heps heps1 A j S hA ha0 ha1
        (le_of_not_gt hbad) hfine'
      exact hactive kp (by change k.val - 1 < k.val; omega) hready
    _ = eventMass (freshStageLaw kp.val (r kp.val) A j S hA) (fun x =>
        nextAeWindow (adaptiveGrid kp.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid kp.val) (r kp.val) x
            - MeasureProb (preparedAAState A j) S|) := by
      simpa only [freshHistoryWindowBad] using!
        (freshHistory_coordinate_event r N A j S hA kp (fun x =>
          nextAeWindow (adaptiveGrid kp.val) (MeasureProb (preparedAAState A j) S) <
            |freshMedianEstimate (adaptiveGrid kp.val) (r kp.val) x
              - MeasureProb (preparedAAState A j) S|))
    _ ≤ (8 / 9 : ℝ) ^ (r kp.val) := freshStageLaw_window_failure kp.val (r kp.val) A j S hA
    _ = (8 / 9 : ℝ) ^ (r (k.val - 1)) := by rfl

theorem freshHistoryActiveMass_le_fine_prefix (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) {K k : ℕ}
    (hKk : K < k) (hkN : k < N)
    (hfine : ∀ n, K ≤ n → n < k → 32 * Real.pi ≤ eps * (adaptiveGrid n : ℝ)
      * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    eventMass (freshHistoryLaw (fun _ => r0) N A j S hA)
        (fun ω => freshHistoryActive eps (fun _ => r0) ω ⟨k, hkN⟩)
      ≤ ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^ (k - K) := by
  classical
  let f : Fin (k - K) → Fin N := fun n => ⟨K + n.val, by omega⟩
  let s : Finset (Fin N) := Finset.univ.image f
  have hf_spec (n : Fin (k - K)) : K ≤ (f n).val ∧ (f n).val < k := by
    dsimp [f]
    omega
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have h := congrArg Fin.val hxy
    dsimp [f] at h
    omega
  calc
    eventMass (freshHistoryLaw (fun _ => r0) N A j S hA)
        (fun ω => freshHistoryActive eps (fun _ => r0) ω ⟨k, hkN⟩)
        ≤ eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
          ∀ l ∈ s, nextAeWindow (adaptiveGrid l.val) (MeasureProb (preparedAAState A j) S) <
            |freshMedianEstimate (adaptiveGrid l.val) r0 (ω l)
              - MeasureProb (preparedAAState A j) S|) := by
      apply eventMass_mono
      intro ω hactive l hl
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hl
      by_contra hbad
      have hready := freshMedian_fires_at_fine_stage eps heps heps1 A j S hA ha0 ha1
        (le_of_not_gt hbad) (hfine (f n).val (hf_spec n).1 (hf_spec n).2)
      exact hactive (f n) (hf_spec n).2 hready
    _ = ∏ l ∈ s, eventMass (freshStageLaw l.val r0 A j S hA) (fun x =>
        nextAeWindow (adaptiveGrid l.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid l.val) r0 x
            - MeasureProb (preparedAAState A j) S|) := by
      have h := independent_event_all_finset
        (fun l : Fin N => freshStageLaw l.val r0 A j S hA) s
        (fun l x => nextAeWindow (adaptiveGrid l.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid l.val) r0 x
            - MeasureProb (preparedAAState A j) S|)
      rw [← h]
      unfold eventMass
      apply Finset.sum_congr
      · ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro ω _
        rfl
    _ = ∏ n : Fin (k - K), eventMass (freshStageLaw (K + n.val) r0 A j S hA) (fun x =>
        nextAeWindow (adaptiveGrid (K + n.val)) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid (K + n.val)) r0 x
            - MeasureProb (preparedAAState A j) S|) := by
      dsimp [s]
      rw [Finset.prod_image (fun x _ y _ hxy => hf_inj hxy)]
    _ ≤ ∏ _n : Fin (k - K), ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) := by
      apply Finset.prod_le_prod₀
      · intro n _
        exact eventMass_nonneg _ _
      · intro n _
        exact freshStageLaw_window_failure_precise (K + n.val) r0 A j S hA
    _ = ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^ (k - K) := by simp

theorem freshHistoryStopWindowBadMass_le_fine_prefix (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) {K k : ℕ}
    (hKk : K ≤ k) (hkN : k < N)
    (hfine : ∀ n, K ≤ n → n < k → 32 * Real.pi ≤ eps * (adaptiveGrid n : ℝ)
      * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
      freshHistoryFirstStop eps (fun _ => r0) ω ⟨k, hkN⟩ ∧
        freshHistoryWindowBad (fun _ => r0) A j S ω ⟨k, hkN⟩)
      ≤ ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^ (k - K + 1) := by
  classical
  let kf : Fin N := ⟨k, hkN⟩
  let f : Fin (k - K) → Fin N := fun n => ⟨K + n.val, by omega⟩
  let s : Finset (Fin N) := Finset.univ.image f
  let t : Finset (Fin N) := insert kf s
  have hf_spec (n : Fin (k - K)) : K ≤ (f n).val ∧ (f n).val < k := by
    dsimp [f]
    omega
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have h := congrArg Fin.val hxy
    dsimp [f] at h
    omega
  have hkf_not_s : kf ∉ s := by
    intro h
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp h
    have hv := congrArg Fin.val hn
    have hlt := (hf_spec n).2
    dsimp [f, kf] at hv
    omega
  have htcard : t.card = k - K + 1 := by
    dsimp [t]
    rw [Finset.card_insert_of_notMem hkf_not_s]
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
        ∀ l ∈ t, nextAeWindow (adaptiveGrid l.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid l.val) r0 (ω l)
            - MeasureProb (preparedAAState A j) S|) := by
      apply eventMass_mono
      intro ω hω l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hω.2
      · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hl
        by_contra hbad
        have hready := freshMedian_fires_at_fine_stage eps heps heps1 A j S hA ha0 ha1
          (le_of_not_gt hbad) (hfine (f n).val (hf_spec n).1 (hf_spec n).2)
        exact hω.1.2 (f n) (hf_spec n).2 hready
    _ = ∏ l ∈ t, eventMass (freshStageLaw l.val r0 A j S hA) (fun x =>
        nextAeWindow (adaptiveGrid l.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid l.val) r0 x
            - MeasureProb (preparedAAState A j) S|) := by
      have h := independent_event_all_finset
        (fun l : Fin N => freshStageLaw l.val r0 A j S hA) t
        (fun l x => nextAeWindow (adaptiveGrid l.val) (MeasureProb (preparedAAState A j) S) <
          |freshMedianEstimate (adaptiveGrid l.val) r0 x
            - MeasureProb (preparedAAState A j) S|)
      rw [← h]
      unfold eventMass
      apply Finset.sum_congr
      · ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro ω _
        rfl
    _ ≤ ∏ _l ∈ t, ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) := by
      apply Finset.prod_le_prod₀
      · intro l _
        exact eventMass_nonneg _ _
      · intro l _
        exact freshStageLaw_window_failure_precise l.val r0 A j S hA
    _ = ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^ t.card := by simp
    _ = _ := by rw [htcard]

theorem pow_succ_le_scaled {η τ : ℝ} (hη0 : 0 ≤ η) (hτ0 : 0 ≤ τ)
    (hητ : η ≤ τ) (r : ℕ) (hr : 1 ≤ r) : η ^ (r + 1) ≤ τ ^ r * η := by
  have hp : η ^ (r - 1) ≤ τ ^ (r - 1) := pow_le_pow_left₀ hη0 hητ _
  have hs : η ^ 2 ≤ τ * η := by nlinarith
  calc
    η ^ (r + 1) = η ^ (r - 1) * η ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ τ ^ (r - 1) * (τ * η) := mul_le_mul hp hs (sq_nonneg _) (pow_nonneg hτ0 _)
    _ = τ ^ r * η := by
      calc
        τ ^ (r - 1) * (τ * η) = (τ ^ (r - 1) * τ) * η := by ring
        _ = τ ^ (r - 1 + 1) * η := by rw [pow_succ]
        _ = _ := by rw [Nat.sub_add_cancel hr]

theorem freshHistoryStopWindowBadMass_le_coarse (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a) (hr0 : 1 ≤ r0) {k : ℕ}
    (hk : k < relativeAeLeastFineIndex eps a heps ha0) (hkN : k < N) :
    eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
      freshHistoryFirstStop eps (fun _ => r0) ω ⟨k, hkN⟩ ∧
        freshHistoryWindowBad (fun _ => r0) A j S ω ⟨k, hkN⟩)
      ≤ (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 *
          (Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4) +
        ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps) *
          (1 / 2 : ℝ) ^ (relativeAeLeastFineIndex eps a heps ha0 - k) := by
  classical
  let K := relativeAeLeastFineIndex eps a heps ha0
  let kf : Fin N := ⟨k, hkN⟩
  let E := fun x : Fin (2 * r0 + 1) → Fin (adaptiveGrid k) =>
    nextAeWindow (adaptiveGrid k) a <
      |freshMedianEstimate (adaptiveGrid k) r0 x - a|
  have hcoord : eventMass (freshHistoryLaw (fun _ => r0) N A j S hA)
      (fun ω => E (ω kf)) = eventMass (freshStageLaw k r0 A j S hA) E := by
    exact freshHistory_coordinate_event (fun _ => r0) N A j S hA kf E
  have hstart : eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
      freshHistoryFirstStop eps (fun _ => r0) ω kf ∧
        freshHistoryWindowBad (fun _ => r0) A j S ω kf)
      ≤ eventMass (freshStageLaw k r0 A j S hA) E := by
    calc
      _ ≤ eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω => E (ω kf)) := by
        apply eventMass_mono
        intro ω hω
        simpa only [E, freshHistoryWindowBad, ha] using! hω.2
      _ = _ := hcoord
  change eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
    freshHistoryFirstStop eps (fun _ => r0) ω kf ∧
      freshHistoryWindowBad (fun _ => r0) A j S ω kf) ≤ _
  by_cases hη : Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4 ≤ 1 / 16
  · have ha1lt : a < 1 := by
      by_contra hlt
      have haeq : a = 1 := le_antisymm ha1 (le_of_not_gt hlt)
      have hM2 : (2 : ℝ) ≤ adaptiveGrid k := by exact_mod_cast adaptiveGrid_two k
      have hM4 : (4 : ℝ) ≤ (adaptiveGrid k : ℝ) ^ 2 := by nlinarith
      have hprod := mul_le_mul_of_nonneg_left hM4 (sq_nonneg Real.pi)
      rw [haeq] at hη
      nlinarith [Real.pi_gt_three]
    have hsmall := freshStageLaw_window_failure_small_amplitude k r0 A j S hA a ha0 ha1lt ha
      (hη.trans (by norm_num))
    have hp := pow_succ_le_scaled (η := Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4)
      (τ := 1 / 16) (by positivity) (by norm_num) hη r0 hr0
    calc
      _ ≤ eventMass (freshStageLaw k r0 A j S hA) E := hstart
      _ ≤ (2 : ℝ) ^ (2 * r0 + 1) *
          (Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4) ^ (r0 + 1) := hsmall
      _ ≤ (2 : ℝ) ^ (2 * r0 + 1) * ((1 / 16 : ℝ) ^ r0 *
          (Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 *
          (Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4) := by ring
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hgeneric := freshStageLaw_window_failure_precise k r0 A j S hA
    have hweight := relativeAe_coarse_backward_weight eps a heps heps1 ha0 ha1 hk hη
    change 1 ≤ (128 * Real.pi ^ 2 / eps) * (1 / 2 : ℝ) ^ (K - k) at hweight
    have hq : ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ≤
        ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps) *
          (1 / 2 : ℝ) ^ (K - k) := by
      calc
        _ = ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * 1 := (mul_one _).symm
        _ ≤ ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) *
            ((128 * Real.pi ^ 2 / eps) * (1 / 2 : ℝ) ^ (K - k)) :=
          mul_le_mul_of_nonneg_left hweight (by positivity)
        _ = _ := by ring
    calc
      _ ≤ eventMass (freshStageLaw k r0 A j S hA) E := hstart
      _ ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 := by
        simpa only [E, ha] using! hgeneric
      _ ≤ ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps) *
          (1 / 2 : ℝ) ^ (K - k) := hq
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem relativeAe_sum_pow_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, q ^ k) ≤ 1 / (1 - q) := by
  have hs : Summable fun k : ℕ => q ^ k := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑' k : ℕ, q ^ k := hs.sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1, one_div]

theorem relativeAe_sum_pow_succ_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, q ^ (k + 1)) ≤ q / (1 - q) := by
  calc
    _ = q * ∑ k ∈ Finset.range n, q ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring
    _ ≤ q * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left (relativeAe_sum_pow_le q hq0 hq1 n) hq0
    _ = _ := by ring

theorem relativeAe_sum_pow_sub_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, q ^ (n - k)) ≤ q / (1 - q) := by
  calc
    _ = ∑ k ∈ Finset.range n, q ^ (k + 1) := by
      rw [← Finset.sum_range_reflect (fun k => q ^ (k + 1)) n]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt := Finset.mem_range.mp hk
      congr 1
      omega
    _ ≤ _ := relativeAe_sum_pow_succ_le q hq0 hq1 n

theorem relativeAe_sum_grid_le (K : ℕ) :
    (∑ k ∈ Finset.range K, (adaptiveGrid k : ℝ)) ≤ adaptiveGrid K := by
  induction K with
  | zero => simp [adaptiveGrid]
  | succ K ih =>
    rw [Finset.sum_range_succ, adaptiveGrid_succ]
    push_cast
    have hM : 0 ≤ (adaptiveGrid K : ℝ) := by positivity
    linarith

theorem relativeAe_sum_grid_sq_le (K : ℕ) :
    (∑ k ∈ Finset.range K, (adaptiveGrid k : ℝ) ^ 2) ≤ (adaptiveGrid K : ℝ) ^ 2 := by
  induction K with
  | zero => simp [adaptiveGrid]
  | succ K ih =>
    rw [Finset.sum_range_succ, adaptiveGrid_succ]
    push_cast
    have hM : 0 ≤ (adaptiveGrid K : ℝ) := by positivity
    nlinarith

theorem freshHistoryFailureMass_le_fixed_split (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a) (hr0 : 1 ≤ r0) :
    freshHistoryFailureMass eps (fun _ => r0) N A j S hA ≤
      ∑ k : Fin N, if k.val < relativeAeLeastFineIndex eps a heps ha0 then
        (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 *
            (Real.pi ^ 2 * (adaptiveGrid k.val : ℝ) ^ 2 * a / 4) +
          ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps) *
            (1 / 2 : ℝ) ^ (relativeAeLeastFineIndex eps a heps ha0 - k.val)
        else ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^
          (k.val - relativeAeLeastFineIndex eps a heps ha0 + 1) := by
  classical
  calc
    _ ≤ ∑ k, eventMass (freshHistoryLaw (fun _ => r0) N A j S hA) (fun ω =>
        freshHistoryFirstStop eps (fun _ => r0) ω k ∧
          freshHistoryWindowBad (fun _ => r0) A j S ω k) :=
      freshHistoryFailureMass_le_window_union eps (fun _ => r0) N A j S hA heps
        (by simpa only [ha] using! ha1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k.val < relativeAeLeastFineIndex eps a heps ha0
      · rw [if_pos hk]
        exact freshHistoryStopWindowBadMass_le_coarse eps heps heps1 r0 N A j S hA
          a ha0 ha1 ha hr0 hk k.isLt
      · rw [if_neg hk]
        apply freshHistoryStopWindowBadMass_le_fine_prefix eps heps heps1 r0 N A j S hA
          (by simpa only [ha] using! ha0) (by simpa only [ha] using! ha1)
          (Nat.le_of_not_gt hk) k.isLt
        intro n hKn _
        simpa only [ha] using! relativeAeLeastFineIndex_spec_at eps a heps ha0 hKn

theorem freshHistoryExpectedForward_le_fixed_split (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a) :
    freshHistoryExpectedForward eps (fun _ => r0) N A j S hA ≤
      ∑ k : Fin N, if k.val ≤ relativeAeLeastFineIndex eps a heps ha0 then
        (freshStageForwardCost (fun _ => r0) k.val : ℝ)
        else (freshStageForwardCost (fun _ => r0) k.val : ℝ) *
          ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^
            (k.val - relativeAeLeastFineIndex eps a heps ha0) := by
  classical
  rw [freshHistoryExpectedForward_eq_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val ≤ relativeAeLeastFineIndex eps a heps ha0
  · rw [if_pos hk]
    have hm := eventMass_le_one (freshHistoryLaw (fun _ => r0) N A j S hA)
      (fun ω => freshHistoryActive eps (fun _ => r0) ω k)
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left hm
      (show 0 ≤ (freshStageForwardCost (fun _ => r0) k.val : ℝ) by positivity)
  · rw [if_neg hk]
    have hKk : relativeAeLeastFineIndex eps a heps ha0 < k.val := Nat.lt_of_not_ge hk
    have hm := freshHistoryActiveMass_le_fine_prefix eps heps heps1 r0 N A j S hA
      (by simpa only [ha] using! ha0) (by simpa only [ha] using! ha1) hKk k.isLt (by
        intro n hKn _
        simpa only [ha] using! relativeAeLeastFineIndex_spec_at eps a heps ha0 hKn)
    exact mul_le_mul_of_nonneg_left hm
      (show 0 ≤ (freshStageForwardCost (fun _ => r0) k.val : ℝ) by positivity)

theorem relativeAe_piecewise_failure_sum_le (P D c : ℝ) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (K N : ℕ) :
    (∑ k : Fin N, if k.val < K then
      P * (adaptiveGrid k.val : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^ (K - k.val)
      else c ^ (k.val - K + 1)) ≤
        P * (adaptiveGrid K : ℝ) ^ 2 + D + c / (1 - c) := by
  classical
  let f : ℕ → ℝ := fun k => if k < K then
    P * (adaptiveGrid k : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^ (K - k)
    else c ^ (k - K + 1)
  have hb := relativeAe_sum_pow_sub_le (1 / 2 : ℝ) (by norm_num) (by norm_num) K
  norm_num at hb
  have hprefix : (∑ k ∈ Finset.range K,
      (P * (adaptiveGrid k : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^ (K - k))) ≤
        P * (adaptiveGrid K : ℝ) ^ 2 + D := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ ≤ P * (adaptiveGrid K : ℝ) ^ 2 + D * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (relativeAe_sum_grid_sq_le K) hP)
        (mul_le_mul_of_nonneg_left hb hD)
      _ = _ := by ring
  change (∑ k : Fin N, f k.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range f N]
  by_cases hKN : K ≤ N
  · rw [← Finset.sum_range_add_sum_Ico f hKN]
    have hpre : (∑ k ∈ Finset.range K, f k) = ∑ k ∈ Finset.range K,
        (P * (adaptiveGrid k : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^ (K - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      rw [if_pos (Finset.mem_range.mp hk)]
    have htail : (∑ k ∈ Finset.Ico K N, f k) =
        ∑ n ∈ Finset.range (N - K), c ^ (n + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      dsimp [f]
      rw [if_neg (by omega : ¬ K + n < K)]
      congr 1
      omega
    rw [hpre, htail]
    exact (add_le_add hprefix (relativeAe_sum_pow_succ_le c hc0 hc1 (N - K))).trans_eq
      (by ring)
  · have hNK : N ≤ K := Nat.le_of_not_ge hKN
    have hcur : (∑ k ∈ Finset.range N, f k) = ∑ k ∈ Finset.range N,
        (P * (adaptiveGrid k : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^ (K - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      rw [if_pos ((Finset.mem_range.mp hk).trans_le hNK)]
    rw [hcur]
    calc
      _ ≤ ∑ k ∈ Finset.range K,
          (P * (adaptiveGrid k : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^ (K - k)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
        intro k _ _
        exact add_nonneg (mul_nonneg hP (sq_nonneg _))
          (mul_nonneg hD (pow_nonneg (by norm_num) _))
      _ ≤ _ := hprefix
      _ ≤ _ := by
        have hcdiv : 0 ≤ c / (1 - c) := div_nonneg hc0 (by linarith)
        linarith

theorem relativeAe_piecewise_cost_sum_le (P c : ℝ) (hP : 0 ≤ P)
    (hc0 : 0 ≤ c) (hc : 2 * c ≤ 1 / 2) (K N : ℕ) :
    (∑ k : Fin N, if k.val ≤ K then P * (adaptiveGrid k.val : ℝ)
      else P * (adaptiveGrid k.val : ℝ) * c ^ (k.val - K)) ≤
        3 * P * (adaptiveGrid K : ℝ) := by
  classical
  let f : ℕ → ℝ := fun k => if k ≤ K then P * (adaptiveGrid k : ℝ)
    else P * (adaptiveGrid k : ℝ) * c ^ (k - K)
  have hpre : (∑ k ∈ Finset.range (K + 1), P * (adaptiveGrid k : ℝ)) ≤
      2 * P * (adaptiveGrid K : ℝ) := by
    rw [← Finset.mul_sum]
    have hs := relativeAe_sum_grid_le (K + 1)
    rw [adaptiveGrid_succ] at hs
    push_cast at hs
    calc
      _ ≤ P * (2 * (adaptiveGrid K : ℝ)) := mul_le_mul_of_nonneg_left hs hP
      _ = _ := by ring
  have hq0 : 0 ≤ 2 * c := mul_nonneg (by norm_num) hc0
  have hq1 : 2 * c < 1 := by linarith
  have hdiv : (2 * c) / (1 - 2 * c) ≤ 1 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - 2 * c)).mpr
    linarith
  change (∑ k : Fin N, f k.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range f N]
  by_cases hKN : K + 1 ≤ N
  · rw [← Finset.sum_range_add_sum_Ico f hKN]
    have hpreEq : (∑ k ∈ Finset.range (K + 1), f k) =
        ∑ k ∈ Finset.range (K + 1), P * (adaptiveGrid k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      rw [if_pos (by have := Finset.mem_range.mp hk; omega)]
    have htailEq : (∑ k ∈ Finset.Ico (K + 1) N, f k) =
        (P * (adaptiveGrid K : ℝ)) * ∑ n ∈ Finset.range (N - (K + 1)), (2 * c) ^ (n + 1) := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp [f]
      rw [if_neg (by omega : ¬ K + 1 + n ≤ K)]
      have hgrid : (adaptiveGrid (K + 1 + n) : ℝ) =
          (adaptiveGrid K : ℝ) * (2 : ℝ) ^ (n + 1) := by
        unfold adaptiveGrid
        push_cast
        rw [show K + 1 + n + 1 = (K + 1) + (n + 1) by omega, pow_add]
      rw [hgrid, show K + 1 + n - K = n + 1 by omega, mul_pow]
      ring
    rw [hpreEq, htailEq]
    have htail : (P * (adaptiveGrid K : ℝ)) *
        (∑ n ∈ Finset.range (N - (K + 1)), (2 * c) ^ (n + 1)) ≤
          P * (adaptiveGrid K : ℝ) := by
      have hs := (relativeAe_sum_pow_succ_le (2 * c) hq0 hq1 (N - (K + 1))).trans hdiv
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left hs
        (mul_nonneg hP (by positivity : 0 ≤ (adaptiveGrid K : ℝ)))
    linarith
  · have hNK : N ≤ K + 1 := Nat.le_of_not_ge hKN
    have hcur : (∑ k ∈ Finset.range N, f k) =
        ∑ k ∈ Finset.range N, P * (adaptiveGrid k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      rw [if_pos (by have := Finset.mem_range.mp hk; omega)]
    rw [hcur]
    calc
      _ ≤ ∑ k ∈ Finset.range (K + 1), P * (adaptiveGrid k : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
        intro k _ _
        exact mul_nonneg hP (by positivity)
      _ ≤ _ := hpre
      _ ≤ _ := by
        have hnonneg : 0 ≤ P * (adaptiveGrid K : ℝ) := mul_nonneg hP (by positivity)
        linarith

theorem freshHistoryFailureMass_le_fixed_budget (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a) (hr0 : 1 ≤ r0)
    (hc0 : 0 ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0)
    (hc1 : (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 < 1) :
    freshHistoryFailureMass eps (fun _ => r0) N A j S hA ≤
      (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 *
          (Real.pi ^ 2 * (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) ^ 2 * a / 4) +
        ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps) +
        ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) / (1 - (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) := by
  classical
  let P : ℝ := (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 * (Real.pi ^ 2 * a / 4)
  let D : ℝ := ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    _ ≤ _ := freshHistoryFailureMass_le_fixed_split eps heps heps1 r0 N A j S hA
      a ha0 ha1 ha hr0
    _ = ∑ k : Fin N, if k.val < relativeAeLeastFineIndex eps a heps ha0 then
        P * (adaptiveGrid k.val : ℝ) ^ 2 + D * (1 / 2 : ℝ) ^
          (relativeAeLeastFineIndex eps a heps ha0 - k.val)
        else ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^
          (k.val - relativeAeLeastFineIndex eps a heps ha0 + 1) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val < relativeAeLeastFineIndex eps a heps ha0
      · rw [if_pos hk, if_pos hk]
        dsimp [P, D]
        ring
      · rw [if_neg hk, if_neg hk]
    _ ≤ _ := relativeAe_piecewise_failure_sum_le P D _ hP hD hc0 hc1 _ N
    _ = _ := by dsimp [P, D]; ring

theorem freshHistoryExpectedForward_le_three_grid (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a)
    (hc0 : 0 ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0)
    (hc : 2 * ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ≤ 1 / 2) :
    freshHistoryExpectedForward eps (fun _ => r0) N A j S hA ≤
      3 * (2 * (r0 : ℝ) + 1) * (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) := by
  classical
  let P : ℝ := 2 * (r0 : ℝ) + 1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  calc
    _ ≤ _ := freshHistoryExpectedForward_le_fixed_split eps heps heps1 r0 N A j S hA
      a ha0 ha1 ha
    _ = ∑ k : Fin N, if k.val ≤ relativeAeLeastFineIndex eps a heps ha0 then
        P * (adaptiveGrid k.val : ℝ)
        else P * (adaptiveGrid k.val : ℝ) * ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^
          (k.val - relativeAeLeastFineIndex eps a heps ha0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val ≤ relativeAeLeastFineIndex eps a heps ha0
      · rw [if_pos hk, if_pos hk]
        unfold freshStageForwardCost
        push_cast
        dsimp [P]
      · rw [if_neg hk, if_neg hk]
        unfold freshStageForwardCost
        push_cast
        dsimp [P]
    _ ≤ 3 * P * (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) :=
      relativeAe_piecewise_cost_sum_le P _ hP hc0 hc _ N
    _ = _ := by rfl

theorem freshHistoryExpectedForward_le_rate (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a)
    (hc0 : 0 ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0)
    (hc : 2 * ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ≤ 1 / 2) :
    freshHistoryExpectedForward eps (fun _ => r0) N A j S hA ≤
      (192 * Real.pi * (2 * (r0 : ℝ) + 1)) / (eps * Real.sqrt a) := by
  calc
    _ ≤ _ := freshHistoryExpectedForward_le_three_grid eps heps heps1 r0 N A j S hA
      a ha0 ha1 ha hc0 hc
    _ ≤ (3 * (2 * (r0 : ℝ) + 1)) * (64 * Real.pi / (eps * Real.sqrt a)) :=
      mul_le_mul_of_nonneg_left
        (relativeAeLeastFineIndex_grid_upper eps a heps heps1 ha0 ha1) (by positivity)
    _ = _ := by ring

theorem relativeAe_repetition_factor (r : ℕ) :
    (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ r = 2 * (1 / 4 : ℝ) ^ r := by
  rw [pow_add, pow_mul, pow_one]
  calc
    _ = (((2 : ℝ) ^ 2) * (1 / 16 : ℝ)) ^ r * 2 := by rw [mul_pow]; ring
    _ = _ := by norm_num [mul_comm]

noncomputable def fixedFreshFailureBudget (eps : ℝ) (r0 : ℕ) : ℝ :=
  (2048 * Real.pi ^ 4 / eps ^ 2) * (1 / 4 : ℝ) ^ r0 +
    (256 * Real.pi ^ 2 / (3 * eps) + 4 / 3) * (8 / 9 : ℝ) ^ r0

theorem freshHistoryFailureMass_le_public_budget (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a) (hr0 : 1 ≤ r0)
    (hc : (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 ≤ 1 / 4) :
    freshHistoryFailureMass eps (fun _ => r0) N A j S hA ≤ fixedFreshFailureBudget eps r0 := by
  have hc0 : 0 ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 := by positivity
  have hc1 : (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 < 1 := by linarith
  have hmain := freshHistoryFailureMass_le_fixed_budget eps heps heps1 r0 N A j S hA
    a ha0 ha1 ha hr0 hc0 hc1
  have hgrid := relativeAeLeastFineIndex_grid_upper eps a heps heps1 ha0 ha1
  have hsquare := pow_le_pow_left₀
    (show 0 ≤ (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) by positivity) hgrid 2
  have hscale : Real.pi ^ 2 * (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) ^ 2 *
      a / 4 ≤ Real.pi ^ 2 * (64 * Real.pi / (eps * Real.sqrt a)) ^ 2 * a / 4 := by
    have hm := mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ Real.pi ^ 2 * a / 4 by positivity)
    convert! hm using 1 <;> ring
  have hamp := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 by positivity)
  have hamp' : (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 *
      (Real.pi ^ 2 * (adaptiveGrid (relativeAeLeastFineIndex eps a heps ha0) : ℝ) ^ 2 * a / 4) ≤
        (2048 * Real.pi ^ 4 / eps ^ 2) * (1 / 4 : ℝ) ^ r0 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * r0 + 1) * (1 / 16 : ℝ) ^ r0 *
          (Real.pi ^ 2 * (64 * Real.pi / (eps * Real.sqrt a)) ^ 2 * a / 4) := hamp
      _ = _ := by
        rw [relativeAe_repetition_factor]
        field_simp [ne_of_gt heps, ne_of_gt (Real.sqrt_pos.2 ha0), Real.sq_sqrt ha0.le]
        rw [Real.sq_sqrt ha0.le]
        ring
  have hfine : ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) /
      (1 - (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ≤ (4 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 := by
    have hden : 0 < 1 - (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 := by linarith
    have hle : ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) /
        (1 - (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ≤
          2 * ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) := by
      apply (div_le_iff₀ hden).mpr
      have hn := mul_nonneg hc0
        (show 0 ≤ 1 - 2 * ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) by linarith)
      nlinarith
    exact hle.trans_eq (by ring)
  have hback : ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) * (128 * Real.pi ^ 2 / eps) =
      (256 * Real.pi ^ 2 / (3 * eps)) * (8 / 9 : ℝ) ^ r0 := by ring
  unfold fixedFreshFailureBudget
  calc
    _ ≤ _ := hmain
    _ ≤ (2048 * Real.pi ^ 4 / eps ^ 2) * (1 / 4 : ℝ) ^ r0 +
        (256 * Real.pi ^ 2 / (3 * eps)) * (8 / 9 : ℝ) ^ r0 +
        (4 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 := by
      rw [← hback]
      exact add_le_add (add_le_add hamp' (le_refl _)) hfine
    _ = _ := by ring

theorem freshHistoryPendingMass_lt_fixed (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a)
    (hc0 : 0 ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0)
    (hc1 : (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 < 1) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ N : ℕ, B < N →
      freshHistoryPendingMass eps (fun _ => r0) N A j S hA < η := by
  classical
  let K := relativeAeLeastFineIndex eps a heps ha0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη hc1
  refine ⟨K + n + 1, fun N hN => ?_⟩
  have hkN : N - 1 < N := by omega
  have hKk : K < N - 1 := by omega
  have hp : freshHistoryPendingMass eps (fun _ => r0) N A j S hA ≤
      eventMass (freshHistoryLaw (fun _ => r0) N A j S hA)
        (fun ω => freshHistoryActive eps (fun _ => r0) ω ⟨N - 1, hkN⟩) := by
    apply eventMass_mono
    intro ω hω l _
    exact hω l
  have hactive := freshHistoryActiveMass_le_fine_prefix eps heps heps1 r0 N A j S hA
    (by simpa only [ha] using! ha0) (by simpa only [ha] using! ha1) hKk hkN (by
      intro m hKm _
      simpa only [ha] using! relativeAeLeastFineIndex_spec_at eps a heps ha0 hKm)
  have hpow : ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^ (N - 1 - K) ≤
      ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ^ n :=
    pow_le_pow_of_le_one hc0 hc1.le (by omega)
  exact hp.trans_lt (hactive.trans_lt (hpow.trans_lt hn))

theorem exists_fixedFreshSchedule_calibration (eps δ : ℝ) (heps : 0 < eps) (hδ : 0 < δ) :
    ∃ r0 : ℕ, 1 ≤ r0 ∧ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 ≤ 1 / 4 ∧
      fixedFreshFailureBudget eps r0 ≤ δ := by
  let C1 : ℝ := 2048 * Real.pi ^ 4 / eps ^ 2
  let C2 : ℝ := 256 * Real.pi ^ 2 / (3 * eps) + 4 / 3
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hC2 : 0 < C2 := by dsimp [C2]; positivity
  obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one
    (show 0 < δ / (3 * C1) by positivity) (show (1 / 4 : ℝ) < 1 by norm_num)
  obtain ⟨n2, hn2⟩ := exists_pow_lt_of_lt_one
    (show 0 < δ / (3 * C2) by positivity) (show (8 / 9 : ℝ) < 1 by norm_num)
  obtain ⟨n3, hn3⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 3 / 8 by norm_num) (show (8 / 9 : ℝ) < 1 by norm_num)
  let r0 := max 1 (max n1 (max n2 n3))
  have hr0 : 1 ≤ r0 := le_max_left _ _
  have hn1r : n1 ≤ r0 := (le_max_left _ _).trans (le_max_right _ _)
  have hn2r : n2 ≤ r0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hn3r : n3 ≤ r0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hp1 : (1 / 4 : ℝ) ^ r0 < δ / (3 * C1) :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1r).trans_lt hn1
  have hp2 : (8 / 9 : ℝ) ^ r0 < δ / (3 * C2) :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2r).trans_lt hn2
  have hp3 : (8 / 9 : ℝ) ^ r0 < 3 / 8 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn3r).trans_lt hn3
  have hc : (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 ≤ 1 / 4 := by
    calc
      _ ≤ (2 / 3 : ℝ) * (3 / 8) := mul_le_mul_of_nonneg_left hp3.le (by norm_num)
      _ = _ := by norm_num
  have ht1 : C1 * (1 / 4 : ℝ) ^ r0 < δ / 3 := by
    calc
      _ < C1 * (δ / (3 * C1)) := mul_lt_mul_of_pos_left hp1 hC1
      _ = _ := by field_simp [ne_of_gt hC1]
  have ht2 : C2 * (8 / 9 : ℝ) ^ r0 < δ / 3 := by
    calc
      _ < C2 * (δ / (3 * C2)) := mul_lt_mul_of_pos_left hp2 hC2
      _ = _ := by field_simp [ne_of_gt hC2]
  refine ⟨r0, hr0, hc, ?_⟩
  unfold fixedFreshFailureBudget
  change C1 * (1 / 4 : ℝ) ^ r0 + C2 * (8 / 9 : ℝ) ^ r0 ≤ δ
  linarith

theorem exists_fixedFreshSchedule_failure_expected_tail
    (eps δ : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hδ : 0 < δ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : MeasureProb (preparedAAState A j) S = a) :
    ∃ r0 : ℕ,
      (∀ N : ℕ, freshHistoryFailureMass eps (fun _ => r0) N A j S hA ≤ δ) ∧
      (∀ N : ℕ, freshHistoryExpectedForward eps (fun _ => r0) N A j S hA ≤
        (192 * Real.pi * (2 * (r0 : ℝ) + 1)) / (eps * Real.sqrt a)) ∧
      (∀ η : ℝ, 0 < η → ∃ B : ℕ, ∀ N : ℕ, B < N →
        freshHistoryPendingMass eps (fun _ => r0) N A j S hA < η) := by
  obtain ⟨r0, hr0, hc, hbudget⟩ := exists_fixedFreshSchedule_calibration eps δ heps hδ
  have hc0 : 0 ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 := by positivity
  have hc1 : (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0 < 1 := by linarith
  have hc2 : 2 * ((2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r0) ≤ 1 / 2 := by linarith
  refine ⟨r0, ?_, ?_, ?_⟩
  · intro N
    exact (freshHistoryFailureMass_le_public_budget eps heps heps1 r0 N A j S hA
      a ha0 ha1 ha hr0 hc).trans hbudget
  · intro N
    exact freshHistoryExpectedForward_le_rate eps heps heps1 r0 N A j S hA
      a ha0 ha1 ha hc0 hc2
  · intro η hη
    exact freshHistoryPendingMass_lt_fixed eps heps heps1 r0 A j S hA
      a ha0 ha1 ha hc0 hc1 η hη

theorem freshHistoryExpectedForward_le_linear_split (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (r0 N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) {K : ℕ} (hK : K < N)
    (hfineK : relativeAeFineIndex eps (MeasureProb (preparedAAState A j) S) ≤ K) :
    freshHistoryExpectedForward eps (linearFreshSchedule r0) N A j S hA ≤
      ∑ k : Fin N, if k.val ≤ K then (freshStageForwardCost (linearFreshSchedule r0) k.val : ℝ)
        else (freshStageForwardCost (linearFreshSchedule r0) k.val : ℝ) *
          (8 / 9 : ℝ) ^ (r0 + (k.val - 1)) := by
  classical
  rw [freshHistoryExpectedForward_eq_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val ≤ K
  · rw [if_pos hk]
    have hm := eventMass_le_one (freshHistoryLaw (linearFreshSchedule r0) N A j S hA)
      (fun ω => freshHistoryActive eps (linearFreshSchedule r0) ω k)
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left hm
      (show 0 ≤ (freshStageForwardCost (linearFreshSchedule r0) k.val : ℝ) by positivity)
  · rw [if_neg hk]
    have hkpos : 0 < k.val := by omega
    have hfinePrev : relativeAeFineIndex eps (MeasureProb (preparedAAState A j) S)
        ≤ k.val - 1 := by omega
    have hm := freshHistoryActiveMass_le_of_fine_prev eps heps heps1
      (linearFreshSchedule r0) N A j S hA ha0 ha1 hkpos
      (relativeAeFineIndex_spec_at eps _ heps ha0 hfinePrev)
    exact mul_le_mul_of_nonneg_left (by simpa only [linearFreshSchedule] using! hm)
      (show 0 ≤ (freshStageForwardCost (linearFreshSchedule r0) k.val : ℝ) by positivity)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
