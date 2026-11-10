/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
namespace Qatlib.Concepts.FairRandomBits.GeometricRetry
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

theorem branchRetry_positive (coin : PMF Bool) (good bad : ℕ) (hg : 0 < good) (hb : 0 < bad) :
    ∀ s cfg k, Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad s (cfg,k) ≠ 0 → 1 ≤ k := by
  intro s cfg k hm
  by_contra h
  have hk : k=0 := by omega
  subst k
  apply hm
  simp [Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext, PMF.map_apply, tsum_fintype,
    show (0:ℕ) ≠ good by omega, show (0:ℕ) ≠ bad by omega]

theorem branchRetry_point (coin : PMF Bool) (good bad n k : ℕ) (o : Bool) :
    Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (n+1) (.inr ()) (.inl o,k) =
      coin false * (if bad ≤ k then Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) n (.inr ()) (.inl o,k-bad) else 0) +
      (if (.inl true : Bool ⊕ Unit)=.inl o ∧ good=k then coin true else 0) := by
  rw [Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun, branchCostTick]
  simp only [Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext, CostedLaw.bind, PMF.bind_map, Function.comp_def, PMF.bind_apply,
    tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, branchCostRun_halted]
  rw [show CostedLaw.charge good (PMF.pure ((.inl true : Bool ⊕ Unit),0)) =
      PMF.pure (.inl true,good) from Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret (α := Bool ⊕ Unit) good (.inl true), Qatlib.Concepts.StoppingCore.BranchCostCore.charge_point_mass]
  by_cases ho : true=o <;> by_cases hk : good=k <;>
    simp [PMF.pure_apply, ho, hk, eq_comm, mul_ite, add_comm]

theorem branchRetry_below_good (coin : PMF Bool) (good bad n k : ℕ) (hk : k < good) :
    Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) n (.inr ()) (.inl true,k)=0 := by
  induction n generalizing k with
  | zero => simp [Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ n ih =>
    rw [branchRetry_point]
    have hne : good ≠ k := by omega
    simp only [true_and, if_neg hne, add_zero]
    by_cases hfit : bad ≤ k
    · rw [if_pos hfit, ih (k-bad) (by omega), mul_zero]
    · simp [hfit]

theorem branchRetry_false (coin : PMF Bool) (good bad n k : ℕ) :
    Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) n (.inr ()) (.inl false,k)=0 := by
  induction n generalizing k with
  | zero => simp [Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ n ih => simp [branchRetry_point, ih]

theorem branchRetry_halt_recursion (coin : PMF Bool) (good bad k : ℕ)
    (hg : 0 < good) (hb : 0 < bad) :
    Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true k =
      coin false * (if bad ≤ k then Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true (k-bad) else 0) +
      (if good=k then coin true else 0) := by
  have hp :=
      Qatlib.Concepts.FairRandomBits.GeometricRetry.branchRetry_positive coin good bad hg hb
  cases k with
  | zero =>
    simp [Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint, Qatlib.Concepts.StoppingCore.BranchCostCore.branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply,
      show ¬ bad ≤ 0 by omega, show good ≠ 0 by omega]
  | succ k =>
    unfold Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint
    rw [branchRetry_point]
    simp only [true_and]
    by_cases hfit : bad ≤ k+1
    · rw [if_pos hfit, if_pos hfit, branchCostRun_stable _ hp (.inr ()) true (k+1-bad) k (by omega)]
      rfl
    · rw [if_neg hfit, if_neg hfit]

theorem branch_cost_geometric_retry_exact_receipt :
    ∀ (coin : PMF Bool) (good bad : ℕ), 0 < good → 0 < bad → ∀ n : ℕ,
      Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true (n*bad+good) =
        (coin false)^n*coin true := by
  intro coin good bad hg hb n
  induction n with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add, branchRetry_halt_recursion coin good bad good hg hb]
    have hz : Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true (good-bad)=0 :=
      branchRetry_below_good coin good bad (good-bad) (good-bad) (by omega)
    simp [hz]
  | succ n ih =>
    rw [branchRetry_halt_recursion coin good bad ((n+1)*bad+good) hg hb]
    have hfit : bad ≤ (n+1)*bad+good := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hne : good ≠ (n+1)*bad+good := by nlinarith
    have he : (n+1)*bad+good-bad=n*bad+good := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [if_pos hfit, if_neg hne, he, ih, add_zero, pow_succ']
    ring

theorem branchRetry_support (coin : PMF Bool) (good bad : ℕ) (hg : 0 < good) (hb : 0 < bad)
    (k : ℕ) (hm : Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true k ≠ 0) :
    ∃ n : ℕ, k=n*bad+good := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases he : good=k
    · exact ⟨0, by omega⟩
    · rw [branchRetry_halt_recursion coin good bad k hg hb, if_neg he, add_zero] at hm
      have hfit : bad ≤ k := by by_contra h; simp [h] at hm
      rw [if_pos hfit] at hm
      have hr : Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true (k-bad) ≠ 0 :=
        right_ne_zero_of_mul hm
      obtain ⟨n, hn⟩ := ih (k-bad) (by omega) hr
      exact ⟨n+1, by rw [Nat.add_mul, Nat.one_mul]; omega⟩

theorem branchRetry_tsum_receipts (coin : PMF Bool) (good bad : ℕ) (hg : 0 < good) (hb : 0 < bad)
    (w : ℕ → ℝ≥0∞) :
    (∑' k : ℕ, w k * Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true k) =
      ∑' n : ℕ, w (n*bad+good) * (coin false)^n * coin true := by
  have hi : Function.Injective (fun n : ℕ => n*bad+good) := by
    intro n m he
    nlinarith
  have hs : Function.support (fun k => w k * Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint
      (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true k) ⊆ Set.range (fun n : ℕ => n*bad+good) := by
    intro k hk
    obtain ⟨n,hn⟩ := branchRetry_support coin good bad hg hb k (right_ne_zero_of_mul hk)
    exact ⟨n,hn.symm⟩
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro n
  rw [branch_cost_geometric_retry_exact_receipt coin good bad hg hb, mul_assoc]

private theorem branchRetry_geom_succ_moment (q : ℝ≥0∞) :
    (∑' t : ℕ, q^t * (t+1 : ℝ≥0∞)) = (1-q)⁻¹ * (1-q)⁻¹ := by
  calc
    _ = ∑' t : ℕ, ∑ p ∈ Finset.antidiagonal t, q^p.1 * q^p.2 := by
      apply tsum_congr
      intro n
      rw [Finset.sum_congr rfl (fun p hp => by
        rw [← pow_add, Finset.mem_antidiagonal.mp hp]), Finset.sum_const,
        Finset.Nat.card_antidiagonal]
      simp [nsmul_eq_mul, mul_comm]
    _ = ∑' p : ℕ × ℕ, q^p.1 * q^p.2 := by
      rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
      apply tsum_congr
      intro t
      change (∑ p ∈ Finset.antidiagonal t, q^p.1 * q^p.2) =
        ∑' p : ↥(Finset.antidiagonal t), q^p.val.1 * q^p.val.2
      rw [tsum_fintype]
      exact (Finset.sum_finset_coe (fun p : ℕ × ℕ => q^p.1 * q^p.2)
        (Finset.antidiagonal t)).symm
    _ = _ := by
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.tsum_prod_type']
      simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

private theorem branchRetry_geom_nat_moment (q : ℝ≥0∞) :
    (∑' t : ℕ, q^t * (t : ℝ≥0∞)) = q * ((1-q)⁻¹ * (1-q)⁻¹) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_succ', Nat.cast_add, Nat.cast_one]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left, branchRetry_geom_succ_moment]

theorem branch_cost_geometric_retry_expected_paid_cost :
    ∀ (coin : PMF Bool) (good bad : ℕ), 0 < good → 0 < bad → 0 < coin true →
      Qatlib.Concepts.StoppingCore.BranchCostCore.generalNeverMass (branchClockNext (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad)) (branchClockEmbed (.inr ()))=0 ∧
      Qatlib.Concepts.StoppingCore.BranchCostCore.generalUnboundedTime (branchClockNext (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad)) (branchClockEmbed (.inr ()))=
        (good:ℝ≥0∞)+(bad:ℝ≥0∞)*coin false/coin true := by
  intro coin good bad hg hb hp
  have hsum : coin false+coin true=1 := by simpa only [tsum_bool] using coin.tsum_coe
  have hc : 1-coin false=coin true :=
    (ENNReal.eq_sub_of_add_eq (coin.apply_ne_top false) (by simpa only [add_comm] using hsum)).symm
  have ht : (∑' k : ℕ, Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) true k)=1 := by
    have h := branchRetry_tsum_receipts coin good bad hg hb (fun _ => 1)
    simp only [one_mul, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, hc,
      ENNReal.inv_mul_cancel hp.ne' (coin.apply_ne_top true)] at h
    exact h
  have hf (k : ℕ) : Qatlib.Concepts.StoppingCore.BranchCostCore.branchHaltJoint (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (.inr ()) false k=0 :=
    branchRetry_false coin good bad k k
  have hn := (Qatlib.Concepts.StoppingCore.BranchCostCore.branch_cost_output_pending_never_conservation Unit Bool
    (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad) (Qatlib.Concepts.FairRandomBits.GeometricRetry.branchRetry_positive coin good bad hg hb) (.inr ())).1
  rw [tsum_bool] at hn
  simp only [hf, tsum_zero, zero_add, ht] at hn
  have hz : Qatlib.Concepts.StoppingCore.BranchCostCore.generalNeverMass (branchClockNext (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad)) (branchClockEmbed (.inr ()))=0 := by
    exact WithTop.add_left_cancel ENNReal.one_ne_top (hn.trans (add_zero 1).symm)
  refine ⟨hz, ?_⟩
  have he := (general_unbounded_actual_expected_time (BranchClock Unit Bool) Bool
    (branchClockNext (Qatlib.Concepts.StoppingCore.BranchCostCore.branchRetryNext coin good bad)) (branchClockEmbed (.inr ()))).1
  simp_rw [branchClock_bridge _ (Qatlib.Concepts.FairRandomBits.GeometricRetry.branchRetry_positive coin good bad hg hb)] at he
  rw [hz, mul_zero, add_zero, tsum_bool] at he
  simp only [hf, mul_zero, tsum_zero, zero_add] at he
  rw [he, branchRetry_tsum_receipts coin good bad hg hb]
  simp only [Nat.cast_add, Nat.cast_mul]
  have hsplit (n : ℕ) : ((n:ℝ≥0∞)*(bad:ℝ≥0∞)+(good:ℝ≥0∞))*(coin false)^n*coin true =
      (good:ℝ≥0∞)*((coin false)^n*coin true) +
      (bad:ℝ≥0∞)*((coin false)^n*(n:ℝ≥0∞))*coin true := by ring
  simp_rw [hsplit]
  rw [ENNReal.tsum_add]
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    branchRetry_geom_nat_moment, hc]
  rw [ENNReal.inv_mul_cancel hp.ne' (coin.apply_ne_top true), mul_one]
  simp only [div_eq_mul_inv]
  congr 1
  calc
    _ = (bad:ℝ≥0∞)*coin false*(coin true)⁻¹*((coin true)⁻¹*coin true) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hp.ne' (coin.apply_ne_top true), mul_one]
end Qatlib.Concepts.FairRandomBits.GeometricRetry
