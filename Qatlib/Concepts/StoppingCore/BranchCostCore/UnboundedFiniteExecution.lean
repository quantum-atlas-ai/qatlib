/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.StoppingCore.BranchCostCore

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

section PointMass

variable {α : Type}

theorem event_point_mass (p : PMF α) (y : α) : CostedLaw.event p (fun x => x = y) = p y := by
  have hbind : (PMF.bind p PMF.pure) y = p y := by rw [PMF.bind_pure]
  rw [PMF.bind_apply] at hbind
  show ∑' x, p x * (if x = y then (1 : ℝ≥0∞) else 0) = p y
  rw [← hbind]
  exact tsum_congr fun x => by simp [PMF.pure_apply, eq_comm]

theorem charge_point_mass (q : CostedLaw α) (n : ℕ) (a : α) (j : ℕ) :
    CostedLaw.charge n q (a, j) = if n ≤ j then q (a, j - n) else 0 := by
  classical
  rw [show CostedLaw.charge n q (a, j)
      = CostedLaw.event (CostedLaw.charge n q) (fun z : α × ℕ => z = (a, j))
        from (event_point_mass _ _).symm,
    CostedLaw.event_charge_general]
  by_cases hn : n ≤ j
  · have hcongr : ∀ w : α × ℕ, ((w.1, n + w.2) = (a, j)) ↔ (w = (a, j - n)) := by
      intro w
      constructor
      · intro hw
        simp only [Prod.mk.injEq] at hw
        exact Prod.ext hw.1 (by have h2 := hw.2; omega)
      · intro hw
        subst hw
        exact congrArg (Prod.mk a) (by omega)
    rw [CostedLaw.event_congr hcongr, event_point_mass, if_pos hn]
  · have hnone : ∀ w : α × ℕ, ¬((w.1, n + w.2) = (a, j)) := by
      intro w hw
      simp only [Prod.mk.injEq] at hw
      obtain ⟨_, h2⟩ := hw
      omega
    rw [CostedLaw.event_zero _ _ hnone, if_neg hn]

end PointMass

section RunForPoints

theorem tick_point_running (next : S → PMF (Configuration S O)) (s : S)
    (c : Configuration S O) (j : ℕ) :
    RandomizedExecution.tick next (Sum.inr s) (c, j) = if j = 1 then next s c else 0 := by
  classical
  have htick : RandomizedExecution.tick next (Sum.inr s)
      = PMF.map (fun d : Configuration S O => (d, 1)) (next s) := rfl
  rw [show RandomizedExecution.tick next (Sum.inr s) (c, j)
      = CostedLaw.event (RandomizedExecution.tick next (Sum.inr s))
        (fun z : Configuration S O × ℕ => z = (c, j))
        from (event_point_mass _ _).symm,
    htick, CostedLaw.event_map]
  by_cases hj : j = 1
  · subst hj
    have hc1 : ∀ d : Configuration S O, ((d, 1) = (c, 1)) ↔ (d = c) := by
      intro d
      simp only [Prod.mk.injEq, and_true]
    rw [if_pos rfl, CostedLaw.event_congr hc1, event_point_mass]
  · have hc0 : ∀ d : Configuration S O, ¬((d, 1) = (c, j)) := by
      intro d hd
      simp only [Prod.mk.injEq] at hd
      omega
    rw [if_neg hj, CostedLaw.event_zero _ _ hc0]

theorem runFor_point_halt_zero (next : S → PMF (Configuration S O)) :
    ∀ (fuel : ℕ) (s : S) (o : O),
      runFor next fuel (Sum.inr s) ((Sum.inl o : Configuration S O), (0 : ℕ)) = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro s o
      show PMF.pure ((Sum.inr s : Configuration S O), (0 : ℕ))
        ((Sum.inl o : Configuration S O), (0 : ℕ)) = 0
      rw [PMF.pure_apply]
      simp
  | succ fuel ih =>
      intro s o
      have hbind : CostedLaw.bind (RandomizedExecution.tick next (Sum.inr s)) (runFor next fuel)
          = PMF.bind (RandomizedExecution.tick next (Sum.inr s))
            (fun x : Configuration S O × ℕ => CostedLaw.charge x.2 (runFor next fuel x.1)) := rfl
      show CostedLaw.bind (RandomizedExecution.tick next (Sum.inr s)) (runFor next fuel)
        ((Sum.inl o : Configuration S O), (0 : ℕ)) = 0
      rw [hbind, PMF.bind_apply _ _ ((Sum.inl o : Configuration S O), (0 : ℕ))]
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      rcases x with ⟨c, j⟩
      show RandomizedExecution.tick next (Sum.inr s) (c, j)
        * CostedLaw.charge j (runFor next fuel c)
          ((Sum.inl o : Configuration S O), (0 : ℕ)) = 0
      by_cases hj : j = 1
      · subst hj
        rw [tick_point_running, if_pos rfl, charge_point_mass]
        simp
      · rw [tick_point_running, if_neg hj, zero_mul]

theorem runFor_point_running_off_fuel (next : S → PMF (Configuration S O)) :
    ∀ (fuel : ℕ) (s s' : S) (j : ℕ), j ≠ fuel →
      runFor next fuel (Sum.inr s) ((Sum.inr s' : Configuration S O), (j : ℕ)) = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro s s' j hj
      show PMF.pure ((Sum.inr s : Configuration S O), (0 : ℕ))
        ((Sum.inr s' : Configuration S O), (j : ℕ)) = 0
      rw [PMF.pure_apply]
      by_cases hs : s = s'
      · subst hs
        simp only [Prod.mk.injEq, true_and]
        exact if_neg hj
      · refine if_neg (fun hcon => hs ?_)
        simp only [Prod.mk.injEq, Sum.inr.injEq] at hcon
        exact hcon.1.symm
  | succ fuel ih =>
      intro s s' j hj
      have hbind : CostedLaw.bind (RandomizedExecution.tick next (Sum.inr s)) (runFor next fuel)
          = PMF.bind (RandomizedExecution.tick next (Sum.inr s))
            (fun x : Configuration S O × ℕ => CostedLaw.charge x.2 (runFor next fuel x.1)) := rfl
      show CostedLaw.bind (RandomizedExecution.tick next (Sum.inr s)) (runFor next fuel)
        ((Sum.inr s' : Configuration S O), (j : ℕ)) = 0
      rw [hbind, PMF.bind_apply _ _ ((Sum.inr s' : Configuration S O), (j : ℕ))]
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      rcases x with ⟨c, i⟩
      show RandomizedExecution.tick next (Sum.inr s) (c, i)
        * CostedLaw.charge i (runFor next fuel c)
          ((Sum.inr s' : Configuration S O), (j : ℕ)) = 0
      by_cases hi1 : i = 1
      · subst hi1
        rw [tick_point_running, if_pos rfl, charge_point_mass]
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          simp
        · have h1j : (1 : ℕ) ≤ j := hj0
          rw [if_pos h1j]
          cases c with
          | inl a =>
              rw [runFor_halted]
              simp [CostedLaw.ret, PMF.pure_apply]
          | inr t =>
              rw [ih t s' (j - 1) (fun h => hj (by omega)), mul_zero]
      · rw [tick_point_running, if_neg hi1, zero_mul]

theorem runFor_point_running_lt_fuel (next : S → PMF (Configuration S O)) :
    ∀ (fuel : ℕ) (cfg : Configuration S O) (s : S) (i : ℕ), i < fuel →
      runFor next fuel cfg ((Sum.inr s : Configuration S O), (i : ℕ)) = 0 := by
  intro fuel cfg
  cases cfg with
  | inl o0 =>
      intro s i hi
      simp [runFor_halted, CostedLaw.ret, PMF.pure_apply]
  | inr s0 =>
      intro s i hi
      exact runFor_point_running_off_fuel next fuel s0 s i (Nat.ne_of_lt hi)

theorem runFor_point_cost_gt_fuel (next : S → PMF (Configuration S O)) (fuel : ℕ)
    (cfg : Configuration S O) (c : Configuration S O) (j : ℕ) (hj : fuel < j) :
    runFor next fuel cfg (c, j) = 0 := by
  have hsup : (c, j) ∉ (runFor next fuel cfg).support := fun hmem => by
    have h2 : j ≤ fuel := runFor_bounded next fuel cfg (c, j) hmem
    omega
  exact not_not.mp ((PMF.mem_support_iff (runFor next fuel cfg) (c, j)).not.mp hsup)

theorem runFor_point_halt_ge (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (o : O) :
    ∀ (fuel k : ℕ), k ≤ fuel →
      runFor next fuel cfg ((Sum.inl o : Configuration S O), (k : ℕ))
        = runFor next k cfg ((Sum.inl o : Configuration S O), (k : ℕ)) := by
  classical
  intro fuel k hle
  obtain ⟨m, rfl⟩ : ∃ m, fuel = k + m := ⟨fuel - k, by omega⟩
  rw [show (runFor next (k + m) cfg : CostedLaw (Configuration S O))
      = CostedLaw.bind (runFor next k cfg) (runFor next m) from runFor_add next k m cfg,
    show CostedLaw.bind (runFor next k cfg) (runFor next m)
      = PMF.bind (runFor next k cfg)
        (fun x : Configuration S O × ℕ => CostedLaw.charge x.2 (runFor next m x.1)) from rfl,
    PMF.bind_apply]
  have hpoint : ∀ x : Configuration S O × ℕ,
      runFor next k cfg x * CostedLaw.charge x.2 (runFor next m x.1)
          ((Sum.inl o : Configuration S O), (k : ℕ))
        = runFor next k cfg x
          * (if x = ((Sum.inl o : Configuration S O), (k : ℕ)) then (1 : ℝ≥0∞) else 0) := by
    intro x
    rcases x with ⟨c, j⟩
    rw [charge_point_mass]
    by_cases hp : runFor next k cfg (c, j) = 0
    · simp [hp]
    · have hsup : j ≤ k :=
        runFor_bounded next k cfg (c, j) ((PMF.mem_support_iff _ _).mp hp)
      by_cases he : (c, j) = ((Sum.inl o : Configuration S O), (k : ℕ))
      · rw [if_pos he]
        simp only [Prod.mk.injEq] at he
        obtain ⟨hc, hjk⟩ := he
        subst hc
        subst hjk
        rw [if_pos (Nat.le_refl j), runFor_halted]
        simp [CostedLaw.ret, PMF.pure_apply]
      · rw [if_neg he]
        have hzero : runFor next m c ((Sum.inl o : Configuration S O), (k - j : ℕ)) = 0 := by
          cases c with
          | inl a =>
              rw [runFor_halted]
              simp only [CostedLaw.ret, PMF.pure_apply]
              have hne : ¬(((Sum.inl o : Configuration S O), (k - j : ℕ)) = (Sum.inl a, (0 : ℕ))) := by
                intro hcon
                simp only [Prod.mk.injEq, Sum.inl.injEq] at hcon
                refine he ?_
                rw [Prod.mk.injEq]
                exact ⟨congrArg Sum.inl hcon.1.symm, by omega⟩
              rw [if_neg hne]
          | inr t =>
              have hjk : j = k := by
                rcases Nat.lt_trichotomy j k with hlt | heq | hgt
                · exact absurd hp
                    (by rw [runFor_point_running_lt_fuel next k cfg t j (by omega)]; simp)
                · exact heq
                · exact absurd hp
                    (by rw [runFor_point_cost_gt_fuel next k cfg (Sum.inr t) j (by omega)]; simp)
              subst hjk
              rw [Nat.sub_self]
              exact runFor_point_halt_zero next m t o
        by_cases hjk : j ≤ k
        · rw [if_pos hjk, hzero]
        · rw [if_neg hjk]
  have hmass : ∑' x : Configuration S O × ℕ,
      runFor next k cfg x
          * (if x = ((Sum.inl o : Configuration S O), (k : ℕ)) then (1 : ℝ≥0∞) else 0)
    = runFor next k cfg ((Sum.inl o : Configuration S O), (k : ℕ)) := by
    have hbind : (PMF.bind (runFor next k cfg) PMF.pure)
        ((Sum.inl o : Configuration S O), (k : ℕ))
      = runFor next k cfg ((Sum.inl o : Configuration S O), (k : ℕ)) := by
      rw [PMF.bind_pure]
    rw [PMF.bind_apply] at hbind
    rw [← hbind]
    exact tsum_congr fun x => by
      by_cases hxy : x = ((Sum.inl o : Configuration S O), (k : ℕ))
      · rw [if_pos hxy, hxy, PMF.pure_apply_self]
      · rw [if_neg hxy, PMF.pure_apply, if_neg (Ne.symm hxy)]
  exact (tsum_congr hpoint).trans hmass

end RunForPoints

noncomputable def haltJoint (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (o : O) (k : ℕ) : ℝ≥0∞ :=
  RandomizedExecution.runFor next k cfg ((Sum.inl o : Configuration S O), (k : ℕ))

noncomputable def pendingMass (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (fuel : ℕ) : ℝ≥0∞ :=
  ∑ s : S, ∑ k ∈ Finset.range (fuel + 1),
    RandomizedExecution.runFor next fuel cfg ((Sum.inr s : Configuration S O), (k : ℕ))

theorem unbounded_first_halt_joint_stability (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (o : O) (k fuel : ℕ) :
    haltJoint next cfg o k = (RandomizedExecution.runFor next k cfg) (Sum.inl o, k) ∧
      (k ≤ fuel → (RandomizedExecution.runFor next fuel cfg) (Sum.inl o, k)
        = haltJoint next cfg o k) :=
  ⟨rfl, fun h => runFor_point_halt_ge next cfg o fuel k h⟩

theorem haltJoint_eq_runFor_of_le {next : S → PMF (Configuration S O)} {cfg : Configuration S O}
    {o : O} {k fuel : ℕ} (h : k ≤ fuel) :
    runFor next fuel cfg ((Sum.inl o : Configuration S O), (k : ℕ)) = haltJoint next cfg o k :=
  (unbounded_first_halt_joint_stability next cfg o k fuel).2 h

theorem pendingMass_eq_finiteSurvival (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    pendingMass next cfg fuel = finiteSurvival next fuel cfg := by
  classical
  have hev : CostedLaw.event (runFor next fuel cfg)
      (fun x : (O ⊕ S) × ℕ => ∃ s, x.1 = Sum.inr s)
    = ∑' x : (O ⊕ S) × ℕ, runFor next fuel cfg x *
      (if (∃ s, x.1 = Sum.inr s) then (1 : ℝ≥0∞) else 0) := by
    rw [CostedLaw.event_eq, show ∑' x : (O ⊕ S) × ℕ, runFor next fuel cfg x
          * (if (∃ s, x.1 = Sum.inr s) then (1 : ℝ≥0∞) else 0)
        = CostedLaw.expectation (runFor next fuel cfg)
            (fun x => if (∃ s, x.1 = Sum.inr s) then (1 : ℝ≥0∞) else 0) from rfl]
    refine CostedLaw.expectation_congr fun x => ?_
    by_cases h : (∃ s, x.1 = Sum.inr s)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  have hzero : ∀ a : O, (∑' j : ℕ, runFor next fuel cfg ((Sum.inl a : O ⊕ S), (j : ℕ))
        * (if (∃ s : S, (Sum.inl a : O ⊕ S) = Sum.inr s) then (1 : ℝ≥0∞) else 0)) = 0 := by
    intro a
    refine ENNReal.tsum_eq_zero.mpr fun j => ?_
    rw [if_neg (fun h : (∃ s : S, (Sum.inl a : O ⊕ S) = Sum.inr s) => Sum.inl_ne_inr h.choose_spec),
      mul_zero]
  have hone : ∀ b : S, (∑' j : ℕ, runFor next fuel cfg ((Sum.inr b : O ⊕ S), (j : ℕ))
        * (if (∃ s : S, (Sum.inr b : O ⊕ S) = Sum.inr s) then (1 : ℝ≥0∞) else 0))
      = ∑' j : ℕ, runFor next fuel cfg ((Sum.inr b : O ⊕ S), (j : ℕ)) := by
    intro b
    refine tsum_congr fun j => ?_
    have hc : (∃ s : S, (Sum.inr b : O ⊕ S) = Sum.inr s) := Exists.intro b rfl
    rw [if_pos hc, mul_one]
  have hsplit : finiteSurvival next fuel cfg
      = ∑' s : S, ∑' j : ℕ,
        runFor next fuel cfg ((Sum.inr s : Configuration S O), (j : ℕ)) := by
    show CostedLaw.event (runFor next fuel cfg)
      (fun x : (O ⊕ S) × ℕ => ∃ s, x.1 = Sum.inr s) = _
    rw [hev, tsum_prod_type', tsum_sum_type',
      tsum_congr (fun a : O => hzero a), tsum_zero, zero_add,
      tsum_congr (fun b : S => hone b)]
  have hinner : ∀ s : S, (∑' j : ℕ, runFor next fuel cfg ((Sum.inr s : O ⊕ S), (j : ℕ)))
      = ∑ k ∈ Finset.range (fuel + 1), runFor next fuel cfg ((Sum.inr s : O ⊕ S), (k : ℕ)) := by
    intro s
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range (fuel + 1))
      (f := fun j => runFor next fuel cfg ((Sum.inr s : O ⊕ S), (j : ℕ))) ?_
    intro j hj
    refine runFor_point_cost_gt_fuel next fuel cfg (Sum.inr s) j ?_
    have hj1 : ¬ (j < fuel + 1) := Finset.mem_range.not.mp hj
    omega
  show ∑ s : S, ∑ k ∈ Finset.range (fuel + 1),
    runFor next fuel cfg ((Sum.inr s : Configuration S O), (k : ℕ)) = _
  rw [← tsum_fintype (L := SummationFilter.unconditional S) (fun s : S => ∑ k ∈ Finset.range (fuel + 1),
    runFor next fuel cfg ((Sum.inr s : Configuration S O), (k : ℕ))),
    ← tsum_congr (fun s => hinner s)]
  exact hsplit.symm

theorem pendingMass_succ_le (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (n : ℕ) : pendingMass next cfg (n + 1) ≤ pendingMass next cfg n := by
  rw [pendingMass_eq_finiteSurvival, pendingMass_eq_finiteSurvival]
  exact finiteSurvival_succ_le next n cfg

theorem unbounded_finite_halt_pending_partition (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    pendingMass next cfg fuel
        = ∑ s : S, ∑ k ∈ Finset.range (fuel + 1),
          (RandomizedExecution.runFor next fuel cfg) (Sum.inr s, k) ∧
      (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + pendingMass next cfg fuel = 1 ∧
      pendingMass next cfg (fuel + 1) ≤ pendingMass next cfg fuel := by
  refine ⟨rfl, ?_, pendingMass_succ_le next cfg fuel⟩
  classical
  have hhalt : ∀ o : O, ∑' j : ℕ, runFor next fuel cfg ((Sum.inl o : Configuration S O), (j : ℕ))
      = ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j := by
    intro o
    refine (tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range (fuel + 1))
      (f := fun j => runFor next fuel cfg ((Sum.inl o : Configuration S O), (j : ℕ))) ?_).trans ?_
    · intro j hj
      refine runFor_point_cost_gt_fuel next fuel cfg (Sum.inl o) j ?_
      have hj1 : ¬ (j < fuel + 1) := Finset.mem_range.not.mp hj
      omega
    · refine Finset.sum_congr rfl fun j hj => ?_
      exact haltJoint_eq_runFor_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hpend : ∀ s : S, ∑' j : ℕ, runFor next fuel cfg ((Sum.inr s : Configuration S O), (j : ℕ))
      = ∑ j ∈ Finset.range (fuel + 1), runFor next fuel cfg (Sum.inr s, j) := by
    intro s
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range (fuel + 1))
      (f := fun j => runFor next fuel cfg ((Sum.inr s : Configuration S O), (j : ℕ))) ?_
    intro j hj
    refine runFor_point_cost_gt_fuel next fuel cfg (Sum.inr s) j ?_
    have hj1 : ¬ (j < fuel + 1) := Finset.mem_range.not.mp hj
    omega
  have hstep1 : (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
      = ∑' o : O, ∑' j : ℕ,
        runFor next fuel cfg ((Sum.inl o : Configuration S O), (j : ℕ)) := by
    rw [← tsum_fintype (L := SummationFilter.unconditional O)]
    exact tsum_congr fun o => (hhalt o).symm
  have hstep2 : pendingMass next cfg fuel
      = ∑' s : S, ∑' j : ℕ,
        runFor next fuel cfg ((Sum.inr s : Configuration S O), (j : ℕ)) := by
    show ∑ s : S, ∑ k ∈ Finset.range (fuel + 1),
      runFor next fuel cfg ((Sum.inr s : Configuration S O), (k : ℕ)) = _
    rw [← tsum_fintype (L := SummationFilter.unconditional S)]
    exact tsum_congr fun s => (hpend s).symm
  rw [hstep1, hstep2, ← tsum_sum_type'
    (F := fun c : O ⊕ S => ∑' j : ℕ, runFor next fuel cfg (c, j)),
    ← tsum_prod_type' (F := fun z : (O ⊕ S) × ℕ => runFor next fuel cfg z),
    PMF.tsum_coe]

noncomputable def nonterminationMass (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : ℝ≥0∞ :=
  ⨅ fuel : ℕ, pendingMass next cfg fuel

theorem pendingMass_antitone (next : S → PMF (Configuration S O)) (cfg : Configuration S O) :
    Antitone (pendingMass next cfg) :=
  antitone_nat_of_succ_le fun n => pendingMass_succ_le next cfg n

theorem pendingMass_tendsto_iInf (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) :
    Filter.Tendsto (pendingMass next cfg) Filter.atTop (nhds (nonterminationMass next cfg)) :=
  tendsto_atTop_iInf (pendingMass_antitone next cfg)

private theorem tendsto_finset_sum_ennreal {ι : Type} (s : Finset ι)
    (f : ι → ℕ → ℝ≥0∞) (g : ι → ℝ≥0∞)
    (h : ∀ i ∈ s, Filter.Tendsto (f i) Filter.atTop (nhds (g i))) :
    Filter.Tendsto (fun n => ∑ i ∈ s, f i n) Filter.atTop (nhds (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact Filter.Tendsto.add (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem haltJoint_partial_sum_tendsto (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) :
    Filter.Tendsto (fun fuel => ∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
      Filter.atTop (nhds (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)) := by
  rw [tsum_fintype (L := SummationFilter.unconditional O) (fun o : O => ∑' k : ℕ, haltJoint next cfg o k)]
  refine tendsto_finset_sum_ennreal Finset.univ _ _ fun o _ => ?_
  exact (HasSum.tendsto_sum_nat
    (ENNReal.summable (f := haltJoint next cfg o)).hasSum).comp
    (Filter.tendsto_add_atTop_nat 1)

theorem haltJoint_tsum_add_nonterminationMass (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) :
    (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + nonterminationMass next cfg = 1 := by
  have hpart : ∀ fuel : ℕ, (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
      + pendingMass next cfg fuel = 1 := fun fuel =>
    (unbounded_finite_halt_pending_partition next cfg fuel).2.1
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ≥0∞))
      Filter.atTop (nhds ((∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)
        + nonterminationMass next cfg)) := by
    refine ((haltJoint_partial_sum_tendsto next cfg).add
      (pendingMass_tendsto_iInf next cfg)).congr'
      (Filter.Eventually.of_forall fun fuel => ?_)
    exact hpart fuel
  exact tendsto_nhds_unique hconst tendsto_const_nhds

private def optionSumUnitEquiv (α : Type) : Option α ≃ Unit ⊕ α where
  toFun
    | none => Sum.inl ()
    | some a => Sum.inr a
  invFun
    | Sum.inl () => none
    | Sum.inr a => some a
  left_inv
    | none => rfl
    | some _ => rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr _ => rfl

private theorem tsum_option_split {α : Type} (F : Option α → ℝ≥0∞) :
    ∑' z : Option α, F z = F none + ∑' a : α, F (some a) := by
  have hsum := (ENNReal.summable
    (f := fun x : Unit ⊕ α => F ((optionSumUnitEquiv α).symm x))).hasSum
  rw [tsum_sum_type'] at hsum
  have hunit : (∑' x : Unit, F ((optionSumUnitEquiv α).symm (Sum.inl x))) = F none := by
    rw [tsum_fintype (L := SummationFilter.unconditional Unit)]
    simp [optionSumUnitEquiv]
  rw [hunit, tsum_congr (fun a : α => rfl)] at hsum
  exact ((Equiv.hasSum_iff (optionSumUnitEquiv α).symm).mp hsum).tsum_eq

noncomputable def unboundedMass (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : Option (O × ℕ) → ℝ≥0∞
  | none => nonterminationMass next cfg
  | some p => haltJoint next cfg p.1 p.2

theorem unboundedMass_none (next : S → PMF (Configuration S O)) (cfg : Configuration S O) :
    unboundedMass next cfg none = nonterminationMass next cfg := rfl

theorem unboundedMass_some (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (o : O) (k : ℕ) : unboundedMass next cfg (some (o, k)) = haltJoint next cfg o k := rfl

theorem unboundedMass_tsum (next : S → PMF (Configuration S O)) (cfg : Configuration S O) :
    ∑' z : Option (O × ℕ), unboundedMass next cfg z = 1 := by
  rw [tsum_option_split, unboundedMass_none, add_comm]
  have hprod : ∑' a : O × ℕ, unboundedMass next cfg (some a)
      = ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k := by
    rw [tsum_prod_type' (F := fun a : O × ℕ => unboundedMass next cfg (some a))]
    exact tsum_congr fun o => tsum_congr fun k => rfl
  rw [hprod, haltJoint_tsum_add_nonterminationMass]

noncomputable def unboundedLaw (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : PMF (Option (O × ℕ)) := by
  have h1 : HasSum (unboundedMass next cfg) (1 : ℝ≥0∞) := by
    rw [← unboundedMass_tsum next cfg]
    exact (ENNReal.summable (f := unboundedMass next cfg)).hasSum
  exact ⟨unboundedMass next cfg, h1⟩

theorem unboundedLaw_apply (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (z : Option (O × ℕ)) : (unboundedLaw next cfg) z = unboundedMass next cfg z := rfl

theorem unbounded_nontermination_limit_and_joint_law (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) :
    (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + nonterminationMass next cfg = 1 ∧
      Filter.Tendsto (pendingMass next cfg) Filter.atTop
        (nhds (nonterminationMass next cfg)) ∧
      (unboundedLaw next cfg) none = nonterminationMass next cfg ∧
      ∀ o k, (unboundedLaw next cfg) (some (o, k)) = haltJoint next cfg o k :=
  ⟨haltJoint_tsum_add_nonterminationMass next cfg, pendingMass_tendsto_iInf next cfg,
    unboundedLaw_apply .., fun _ _ => unboundedLaw_apply ..⟩

end Qatlib.Concepts.StoppingCore.BranchCostCore
