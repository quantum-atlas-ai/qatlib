/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedFiniteExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical
variable {S O : Type}

namespace GeneralExecution
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

end GeneralExecution
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

noncomputable def generalPendingMass (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (fuel : ℕ) : ℝ≥0∞ :=
  CostedLaw.event (runFor next fuel cfg) (fun z => ∃ s, z.1 = Sum.inr s)

noncomputable def generalNeverMass (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) : ℝ≥0∞ :=
  ⨅ fuel, generalPendingMass next cfg fuel

noncomputable def generalUnboundedTime (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) : ℝ≥0∞ :=
  ∑' fuel, generalPendingMass next cfg fuel

theorem general_unbounded_actual_first_halt_stability :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (o : O) (k T : ℕ),
      k ≤ T → runFor next T cfg (Sum.inl o, k) = haltJoint next cfg o k := by
  intro S O next cfg o k T h
  exact GeneralExecution.runFor_point_halt_ge next cfg o T k h

theorem generalPendingMass_eq_tsum (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (fuel : ℕ) : generalPendingMass next cfg fuel =
      ∑' s : S, ∑' j : ℕ, runFor next fuel cfg (Sum.inr s, j) := by
  classical
  have hev : CostedLaw.event (runFor next fuel cfg)
      (fun x : (O ⊕ S) × ℕ => ∃ s, x.1 = Sum.inr s)
    = ∑' x : (O ⊕ S) × ℕ, runFor next fuel cfg x *
      (if (∃ s, x.1 = Sum.inr s) then (1 : ℝ≥0∞) else 0) := by
    rw [CostedLaw.event_eq, show ∑' x : (O ⊕ S) × ℕ, runFor next fuel cfg x
          * (if (∃ s, x.1 = Sum.inr s) then (1 : ℝ≥0∞) else 0)
        = CostedLaw.expectation (runFor next fuel cfg)
            (fun x => if (∃ s, x.1 = Sum.inr s) then (1 : ℝ≥0∞) else 0) from rfl]

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
  have hsplit : generalPendingMass next cfg fuel
      = ∑' s : S, ∑' j : ℕ,
        runFor next fuel cfg ((Sum.inr s : Configuration S O), (j : ℕ)) := by
    show CostedLaw.event (runFor next fuel cfg)
      (fun x : (O ⊕ S) × ℕ => ∃ s, x.1 = Sum.inr s) = _
    rw [hev, tsum_prod_type', tsum_sum_type',
      tsum_congr (fun a : O => hzero a), tsum_zero, zero_add,
      tsum_congr (fun b : S => hone b)]
  exact hsplit

theorem general_unbounded_finite_partition_and_pending :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S),
      Antitone (generalPendingMass next cfg) ∧ ∀ T : ℕ,
        (∑' o : O, ∑ k ∈ Finset.range (T + 1), haltJoint next cfg o k) +
          generalPendingMass next cfg T = 1 := by
  intro S O next cfg
  refine ⟨antitone_nat_of_succ_le (fun n => finiteSurvival_succ_le next n cfg), ?_⟩
  intro fuel
  classical
  have hhalt : ∀ o : O, ∑' j : ℕ, runFor next fuel cfg ((Sum.inl o : Configuration S O), (j : ℕ))
      = ∑ j ∈ Finset.range (fuel + 1), haltJoint next cfg o j := by
    intro o
    refine (tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range (fuel + 1))
      (f := fun j => runFor next fuel cfg ((Sum.inl o : Configuration S O), (j : ℕ))) ?_).trans ?_
    · intro j hj
      refine GeneralExecution.runFor_point_cost_gt_fuel next fuel cfg (Sum.inl o) j ?_
      have hj1 : ¬ (j < fuel + 1) := Finset.mem_range.not.mp hj
      omega
    · refine Finset.sum_congr rfl fun j hj => ?_
      exact GeneralExecution.runFor_point_halt_ge next cfg o fuel j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [tsum_congr (fun o => (hhalt o).symm), generalPendingMass_eq_tsum,
    ← tsum_sum_type' (F := fun c : O ⊕ S => ∑' j : ℕ, runFor next fuel cfg (c, j)),
    ← tsum_prod_type' (F := fun z : (O ⊕ S) × ℕ => runFor next fuel cfg z), PMF.tsum_coe]

theorem general_haltJoint_tsum_add_never (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) :
    (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + generalNeverMass next cfg = 1 := by
  have hpart := (general_unbounded_finite_partition_and_pending S O next cfg).2
  have hlimit : Filter.Tendsto
      (fun T => ∑' o : O, ∑ k ∈ Finset.range (T + 1), haltJoint next cfg o k)
      Filter.atTop (nhds (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)) := by
    simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    rw [ENNReal.tsum_comm]
    exact (ENNReal.tendsto_nat_tsum (fun k => ∑' o : O, haltJoint next cfg o k)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hn : Filter.Tendsto (generalPendingMass next cfg) Filter.atTop
      (nhds (generalNeverMass next cfg)) :=
    tendsto_atTop_iInf (general_unbounded_finite_partition_and_pending S O next cfg).1
  exact tendsto_nhds_unique ((hlimit.add hn).congr'
    (Filter.Eventually.of_forall fun T => hpart T)) tendsto_const_nhds

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

noncomputable def generalUnboundedMass (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : Option (O × ℕ) → ℝ≥0∞
  | none => generalNeverMass next cfg
  | some p => haltJoint next cfg p.1 p.2

theorem generalUnboundedMass_none (next : S → PMF (Configuration S O)) (cfg : Configuration S O) :
    generalUnboundedMass next cfg none = generalNeverMass next cfg := rfl

theorem generalUnboundedMass_some (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (o : O) (k : ℕ) : generalUnboundedMass next cfg (some (o, k)) = haltJoint next cfg o k := rfl

theorem generalUnboundedMass_tsum (next : S → PMF (Configuration S O)) (cfg : Configuration S O) :
    ∑' z : Option (O × ℕ), generalUnboundedMass next cfg z = 1 := by
  rw [tsum_option_split, generalUnboundedMass_none, add_comm]
  have hprod : ∑' a : O × ℕ, generalUnboundedMass next cfg (some a)
      = ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k := by
    rw [tsum_prod_type' (F := fun a : O × ℕ => generalUnboundedMass next cfg (some a))]
    exact tsum_congr fun o => tsum_congr fun k => rfl
  rw [hprod, general_haltJoint_tsum_add_never]

noncomputable def generalUnboundedLaw (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : PMF (Option (O × ℕ)) := by
  have h1 : HasSum (generalUnboundedMass next cfg) (1 : ℝ≥0∞) := by
    rw [← generalUnboundedMass_tsum next cfg]
    exact (ENNReal.summable (f := generalUnboundedMass next cfg)).hasSum
  exact ⟨generalUnboundedMass next cfg, h1⟩

theorem generalUnboundedLaw_apply (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (z : Option (O × ℕ)) : (generalUnboundedLaw next cfg) z = generalUnboundedMass next cfg z := rfl

theorem general_unbounded_never_and_joint_pmf :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S),
      (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + generalNeverMass next cfg = 1 ∧
      generalUnboundedLaw next cfg none = generalNeverMass next cfg ∧
      (∀ o k, generalUnboundedLaw next cfg (some (o, k)) = haltJoint next cfg o k) := by
  intro S O next cfg
  exact ⟨general_haltJoint_tsum_add_never next cfg, rfl, fun _ _ => rfl⟩

theorem general_haltJoint_tsum_split (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
    (o : O) (n : ℕ) :
    (∑' k : ℕ, haltJoint next cfg o k)
      = (∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) := by
  have hpt : ∀ k : ℕ, haltJoint next cfg o k
      = (if k < n + 1 then haltJoint next cfg o k else 0)
        + haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) := by
    intro k
    by_cases hk : n < k
    · rw [if_pos hk, if_neg (by omega), zero_add, mul_one]
    · rw [if_neg hk, mul_zero, add_zero, if_pos (by omega)]
  calc (∑' k : ℕ, haltJoint next cfg o k)
      = ∑' k : ℕ, ((if k < n + 1 then haltJoint next cfg o k else 0)
          + haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0)) :=
        tsum_congr hpt
    _ = (∑' k : ℕ, if k < n + 1 then haltJoint next cfg o k else 0)
          + ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) :=
        ENNReal.tsum_add
    _ = (∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
          + ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) := by
        refine congrArg (· + _) ?_
        exact (tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range (n + 1))
          (f := fun k => if k < n + 1 then haltJoint next cfg o k else 0)
          (fun k hk => if_neg (Finset.mem_range.not.mp hk))).trans
          (Finset.sum_congr rfl fun k hk => if_pos (Finset.mem_range.mp hk))

theorem generalPendingMass_eq_tail_add_never (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (n : ℕ) :
    generalPendingMass next cfg n
      = (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
        + generalNeverMass next cfg := by
  have hpart := (general_unbounded_finite_partition_and_pending S O next cfg).2 n
  have hlimit := general_haltJoint_tsum_add_never next cfg
  have hsplit : (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)
      = (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) := by
    calc (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)
        = ∑' o : O, ((∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0)) :=
          tsum_congr fun o => general_haltJoint_tsum_split next cfg o n
      _ = (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_add
  have hHn : (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (by rw [← hpart]; exact le_self_add)
  have hsum : (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + generalPendingMass next cfg n
      = (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + ((∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
          + generalNeverMass next cfg) := by
    calc (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
          + generalPendingMass next cfg n
        = 1 := hpart
      _ = (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + generalNeverMass next cfg :=
          hlimit.symm
      _ = ((∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0))
          + generalNeverMass next cfg := by rw [hsplit]
      _ = (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
          + ((∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0))
            + generalNeverMass next cfg) := add_assoc _ _ _
  exact WithTop.add_left_cancel hHn hsum

theorem general_tsum_indicator_lt_ennreal (k : ℕ) :
    ∑' n : ℕ, (if n < k then (1 : ℝ≥0∞) else 0) = (k : ℝ≥0∞) := by
  refine (tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range k)
    (f := fun n => if n < k then (1 : ℝ≥0∞) else 0)
    (fun n hn => if_neg (Finset.mem_range.not.mp hn))).trans ?_
  rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn) :
      ∀ n ∈ Finset.range k, (if n < k then (1 : ℝ≥0∞) else 0) = 1),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem general_tsum_const_nat_ennreal (c : ℝ≥0∞) : ∑' _n : ℕ, c = ⊤ * c := by
  rw [ENNReal.tsum_const]
  simp

theorem general_tsum_tail_eq_cost_weighted_haltJoint (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) :
    ∑' n : ℕ, ∑' o : O, ∑' k : ℕ,
        haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0)
      = ∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k := by
  calc ∑' n : ℕ, ∑' o : O, ∑' k : ℕ,
        haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0)
      = ∑' o : O, ∑' n : ℕ, ∑' k : ℕ,
          haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_comm
    _ = ∑' o : O, ∑' k : ℕ, ∑' n : ℕ,
          haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) :=
        tsum_congr fun o => ENNReal.tsum_comm
    _ = ∑' o : O, ∑' k : ℕ,
          haltJoint next cfg o k * ∑' n : ℕ, (if n < k then (1 : ℝ≥0∞) else 0) :=
        tsum_congr fun o => tsum_congr fun k => ENNReal.tsum_mul_left
    _ = ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (k : ℝ≥0∞) :=
        tsum_congr fun o => tsum_congr fun k => by rw [general_tsum_indicator_lt_ennreal]
    _ = ∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k :=
        tsum_congr fun o => tsum_congr fun k => mul_comm _ _

theorem general_unbounded_actual_expected_time :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S),
      generalUnboundedTime next cfg =
        (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k) +
          ⊤ * generalNeverMass next cfg ∧
      (generalUnboundedTime next cfg < ⊤ → generalNeverMass next cfg = 0) ∧
      ∀ T : ℕ, CostedLaw.expectedCost (runFor next T cfg) =
        ∑ t ∈ Finset.range T, generalPendingMass next cfg t := by
  intro S O next cfg
  have h2 : generalUnboundedTime next cfg
      = (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k)
        + (⊤ : ℝ≥0∞) * generalNeverMass next cfg := by
    show (∑' n : ℕ, generalPendingMass next cfg n) = _
    calc (∑' n : ℕ, generalPendingMass next cfg n)
        = ∑' n : ℕ, ((∑' o : O, ∑' k : ℕ,
              haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
            + generalNeverMass next cfg) :=
          tsum_congr fun n => generalPendingMass_eq_tail_add_never next cfg n
      _ = (∑' n : ℕ, ∑' o : O, ∑' k : ℕ,
              haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
            + ∑' n : ℕ, generalNeverMass next cfg := ENNReal.tsum_add
      _ = (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k)
            + (⊤ : ℝ≥0∞) * generalNeverMass next cfg := by
          rw [general_tsum_tail_eq_cost_weighted_haltJoint, general_tsum_const_nat_ennreal]
  refine ⟨h2, ?_, fun T => finite_stopping_cost_tail_sum next cfg T⟩
  intro hlt
  by_contra hN
  rw [h2, ENNReal.top_mul hN, add_top] at hlt
  exact absurd hlt (lt_irrefl _)

theorem general_online_cutoff (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ) :
    (fuel + 1 : ℝ≥0∞) * generalPendingMass next cfg fuel ≤ generalUnboundedTime next cfg ∧
    generalPendingMass next cfg fuel ≤ generalUnboundedTime next cfg / (fuel + 1 : ℝ≥0∞) := by
  have h1 : (fuel+1 : ℝ≥0∞) * generalPendingMass next cfg fuel ≤ generalUnboundedTime next cfg := by
    calc (fuel+1 : ℝ≥0∞) * generalPendingMass next cfg fuel
        = ∑ _n ∈ Finset.range (fuel + 1), generalPendingMass next cfg fuel := by
          rw [← Nat.cast_add_one]
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.range (fuel + 1), generalPendingMass next cfg n :=
          Finset.sum_le_sum fun n hn =>
            (general_unbounded_finite_partition_and_pending S O next cfg).1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      _ ≤ ∑' n : ℕ, generalPendingMass next cfg n := ENNReal.sum_le_tsum _
      _ = generalUnboundedTime next cfg := rfl
  refine ⟨h1, ?_⟩
  have hne : (fuel+1 : ℝ≥0∞) ≠ 0 := by
    rw [← Nat.cast_add_one]
    simp
  have htop : (fuel+1 : ℝ≥0∞) ≠ ⊤ := by
    rw [← Nat.cast_add_one]
    exact ENNReal.natCast_ne_top _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl htop), mul_comm]
  exact h1

theorem general_output_event_cutoff (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (fuel : ℕ) (E : Finset O) :
    (∑ o ∈ E, ∑ k ∈ Finset.range (fuel+1), haltJoint next cfg o k) ≤
        ∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k ∧
    (∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k) ≤
        (∑ o ∈ E, ∑ k ∈ Finset.range (fuel+1), haltJoint next cfg o k) +
          generalPendingMass next cfg fuel := by
  refine ⟨Finset.sum_le_sum fun o _ => ENNReal.sum_le_tsum _, ?_⟩
  calc (∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k)
      = ∑ o ∈ E, ((∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + ∑' k : ℕ, haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0)) :=
        Finset.sum_congr rfl fun o _ => general_haltJoint_tsum_split next cfg o fuel
    _ = (∑ o ∈ E, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + ∑ o ∈ E, ∑' k : ℕ,
            haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (∑ o ∈ E, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + generalPendingMass next cfg fuel := by
        have htail : (∑ o ∈ E, ∑' k : ℕ,
              haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0))
            ≤ generalPendingMass next cfg fuel := by
          calc (∑ o ∈ E, ∑' k : ℕ,
                  haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0))
              ≤ ∑' o : O, ∑' k : ℕ,
                  haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0) :=
                ENNReal.sum_le_tsum E
            _ ≤ generalPendingMass next cfg fuel := by
                rw [generalPendingMass_eq_tail_add_never]
                exact le_self_add
        exact add_le_add (le_refl _) htail

theorem general_unbounded_online_markov_and_event_cutoff :
    ∀ (S O : Type) (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (T : ℕ) (E : Finset O),
      generalPendingMass next cfg T ≤ generalUnboundedTime next cfg / (T+1 : ℝ≥0∞) ∧
      (∑ o ∈ E, ∑ k ∈ Finset.range (T+1), haltJoint next cfg o k) ≤
        (∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k) ∧
      (∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k) ≤
        (∑ o ∈ E, ∑ k ∈ Finset.range (T+1), haltJoint next cfg o k) +
          generalPendingMass next cfg T := by
  intro S O next cfg T E
  exact ⟨(general_online_cutoff next cfg T).2, general_output_event_cutoff next cfg T E⟩

theorem general_finite_output_mass (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (T : ℕ) (o : O) :
    CostedLaw.event (runFor next T cfg) (fun z => z.1 = Sum.inl o) =
      ∑ k ∈ Finset.range (T+1), haltJoint next cfg o k := by
  classical
  have hm : CostedLaw.event (runFor next T cfg) (fun z => z.1 = Sum.inl o) =
      ∑' k : ℕ, runFor next T cfg (Sum.inl o,k) := by
    unfold CostedLaw.event CostedLaw.expectation
    rw [tsum_prod_type']
    apply (tsum_eq_single (Sum.inl o) (fun c hc => ?_)).trans
    · simp
    · simp [hc]
  rw [hm]
  refine (tsum_eq_sum (s := Finset.range (T+1)) (fun k hk => ?_)).trans ?_
  · exact GeneralExecution.runFor_point_cost_gt_fuel next T cfg (Sum.inl o) k
      (by have := Finset.mem_range.not.mp hk; omega)
  · exact Finset.sum_congr rfl fun k hk =>
      general_unbounded_actual_first_halt_stability S O next cfg o k T
        (by have := Finset.mem_range.mp hk; omega)

theorem general_zero_pending_budget (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (T : ℕ) (h : generalPendingMass next cfg T = 0) :
    generalNeverMass next cfg = 0 ∧ generalUnboundedTime next cfg ≤ (T : ℝ≥0∞) := by
  have ha := (general_unbounded_finite_partition_and_pending S O next cfg).1
  have hz : ∀ n, T ≤ n → generalPendingMass next cfg n = 0 :=
    fun n hn => le_antisymm (h ▸ ha hn) (bot_le)
  refine ⟨le_antisymm (h ▸ iInf_le _ T) (bot_le), ?_⟩
  change (∑' n, generalPendingMass next cfg n) ≤ _
  rw [tsum_eq_sum (s := Finset.range T) (fun n hn => hz n
    (by have := Finset.mem_range.not.mp hn; omega))]
  rw [← (general_unbounded_actual_expected_time S O next cfg).2.2 T]
  exact runFor_expectedCost_le next T cfg

end Qatlib.Concepts.StoppingCore.BranchCostCore
