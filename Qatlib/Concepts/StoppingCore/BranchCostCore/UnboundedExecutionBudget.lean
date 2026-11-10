/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedFiniteExecution
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

section SumHelpers

variable {α : Type}

theorem sum_range_const_ennreal (m : ℕ) (c : ℝ≥0∞) :
    ∑ _i ∈ Finset.range m, c = (m : ℝ≥0∞) * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      ring

theorem sum_tsum_swap_ennreal (s : Finset α) (g : α → ℕ → ℝ≥0∞) :
    ∑ i ∈ s, ∑' j, g i j = ∑' j, ∑ i ∈ s, g i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, ih, ← ENNReal.tsum_add]
      exact tsum_congr fun j => by rw [Finset.sum_insert hi]

end SumHelpers

section GeomHelpers

theorem geom_partial_ennreal (q : ℝ≥0∞) (hq : q ≤ 1) :
    ∀ N : ℕ, (∑ i ∈ Finset.range N, q ^ i * (1 - q)) + q ^ N = 1 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hcancel : (1 : ℝ≥0∞) - q + q = 1 := tsub_add_cancel_of_le hq
      have hstep : q ^ N * (1 - q) + q ^ (N + 1) = q ^ N := by
        rw [pow_succ q N, ← mul_add, hcancel, mul_one]
      calc (∑ i ∈ Finset.range (N + 1), q ^ i * (1 - q)) + q ^ (N + 1)
          = ((∑ i ∈ Finset.range N, q ^ i * (1 - q)) + q ^ N * (1 - q)) + q ^ (N + 1) := by
              rw [Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range N, q ^ i * (1 - q)) + q ^ N := by
              rw [add_assoc, hstep]
        _ = 1 := ih

theorem pow_le_one_ennreal (q : ℝ≥0∞) (hq : q ≤ 1) (N : ℕ) : q ^ N ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc q ^ (N + 1) = q ^ N * q := pow_succ q N
        _ ≤ 1 * 1 := mul_le_mul' ih hq
        _ = 1 := by simp

theorem iInf_pow_eq_zero_ennreal (q : ℝ≥0∞) (hq : q < 1) : ⨅ n : ℕ, q ^ n = 0 := by
  have hq1 : q ≤ 1 := hq.le
  by_contra hcon
  have hd : (1 : ℝ≥0∞) - q ≠ 0 := by
    intro h
    rw [tsub_eq_zero_iff_le] at h
    exact absurd (le_antisymm hq1 h) (fun hqeq => absurd hqeq hq.ne)
  have hle : ∀ i : ℕ, (⨅ n : ℕ, q ^ n) ≤ q ^ i :=
    fun i => iInf_le (fun n : ℕ => q ^ n) i
  have hbound : ∀ N : ℕ, N * ((⨅ n : ℕ, q ^ n) * (1 - q)) ≤ 1 := by
    intro N
    have h1 : (∑ i ∈ Finset.range N, q ^ i * (1 - q)) + q ^ N = 1 :=
      geom_partial_ennreal q hq1 N
    have h2 : ∑ i ∈ Finset.range N, ((⨅ n : ℕ, q ^ n) * (1 - q))
        ≤ ∑ i ∈ Finset.range N, q ^ i * (1 - q) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_left (hle i) _
    rw [← sum_range_const_ennreal N _]
    refine le_trans h2 ?_
    have hsum1 : (∑ i ∈ Finset.range N, q ^ i * (1 - q)) = 1 - q ^ N :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (pow_le_one_ennreal q hq1 N)) h1
    rw [hsum1]
    exact tsub_le_self
  have hc1 : (⨅ n : ℕ, q ^ n) ≤ 1 := by
    have h0 : (⨅ n : ℕ, q ^ n) ≤ q ^ 0 := hle 0
    rwa [pow_zero] at h0
  have hdne : (⨅ n : ℕ, q ^ n) * (1 - q) ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h | h
    · exact hcon h
    · exact hd h
  have hdn1 : (⨅ n : ℕ, q ^ n) * (1 - q) ≠ ⊤ := by
    have hle1 : (⨅ n : ℕ, q ^ n) * (1 - q) ≤ 1 := by
      calc (⨅ n : ℕ, q ^ n) * (1 - q) ≤ 1 * 1 := mul_le_mul' hc1 tsub_le_self
        _ = 1 := one_mul 1
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ≥0∞) < n * ((⨅ n : ℕ, q ^ n) * (1 - q)) := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt
      (r := ((⨅ n : ℕ, q ^ n) * (1 - q))⁻¹)
      ((ENNReal.inv_ne_top).mpr hdne)
    refine ⟨n, ?_⟩
    have hunit : ((⨅ n : ℕ, q ^ n) * (1 - q))⁻¹ * ((⨅ n : ℕ, q ^ n) * (1 - q)) = 1 :=
      ENNReal.inv_mul_cancel hdne hdn1
    calc (1 : ℝ≥0∞)
        = ((⨅ n : ℕ, q ^ n) * (1 - q))⁻¹ * ((⨅ n : ℕ, q ^ n) * (1 - q)) := hunit.symm
      _ < ↑n * ((⨅ n : ℕ, q ^ n) * (1 - q)) := ENNReal.mul_lt_mul_left hdne hdn1 hn
  exact absurd (hbound n) (not_le_of_gt hn)

theorem geom_tsum_ennreal (q : ℝ≥0∞) (hq : q < 1) : ∑' n : ℕ, q ^ n = (1 - q)⁻¹ := by
  have hq1 : q ≤ 1 := hq.le
  have hq0 : (0 : ℝ≥0∞) < 1 - q := by
    have hne : (1 : ℝ≥0∞) - q ≠ 0 := by
      intro h
      rw [tsub_eq_zero_iff_le] at h
      exact absurd (le_antisymm hq1 h) (fun hqeq => absurd hqeq hq.ne)
    exact lt_of_le_of_ne zero_le (Ne.symm hne)
  have hpow1 : ∀ N : ℕ, q ^ N ≤ 1 := pow_le_one_ennreal q hq1
  have hc : ⨅ n : ℕ, q ^ n = 0 := iInf_pow_eq_zero_ennreal q hq

  have hterm : ∀ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i) = 1 - q ^ N := by
    intro N
    have hcomm : (∑ i ∈ Finset.range N, (1 - q) * q ^ i)
        = ∑ i ∈ Finset.range N, q ^ i * (1 - q) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hpart' : (∑ i ∈ Finset.range N, (1 - q) * q ^ i) + q ^ N = 1 := by
      rw [hcomm]; exact geom_partial_ennreal q hq1 N
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hpow1 N)) hpart'

  have hsup : (1 - q) * ∑' n : ℕ, q ^ n
      = ⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i) := by
    rw [ENNReal.tsum_eq_iSup_sum' (s := fun N => Finset.range N)
      (fun t => Finset.exists_nat_subset_range t), ENNReal.mul_iSup]
    exact iSup_congr fun N => Finset.mul_sum ..
  have hsup2 : (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i)) ≤ 1 :=
    iSup_le fun N => (hterm N).le.trans tsub_le_self
  have hsup1 : (1 : ℝ≥0∞) ≤ ⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i) := by
    by_contra hcon
    have hx : (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i)) < 1 :=
      lt_of_not_ge hcon
    have hxne : (1 : ℝ≥0∞) - (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i)) ≠ 0 := by
      intro h0
      rw [tsub_eq_zero_iff_le] at h0
      exact not_le.mpr hx h0
    have hx0 : (0 : ℝ≥0∞) < 1 - (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i)) :=
      lt_of_le_of_ne zero_le (Ne.symm hxne)
    have hge : ∀ M : ℕ,
        (1 - (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i))) ≤ q ^ M := by
      intro M
      have h1M' : (1 - q ^ M) ≤ ⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i) := by
        rw [← hterm M]
        exact le_iSup (fun N : ℕ => ∑ i ∈ Finset.range N, (1 - q) * q ^ i) M
      calc (1 : ℝ≥0∞) - (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i))
          ≤ 1 - (1 - q ^ M) := tsub_le_tsub_left h1M' 1
        _ = q ^ M := ENNReal.sub_sub_cancel (by simp) (hpow1 M)
    have hcle : (1 - (⨆ N : ℕ, (∑ i ∈ Finset.range N, (1 - q) * q ^ i)))
        ≤ ⨅ n : ℕ, q ^ n := le_iInf hge
    have hlt : (0 : ℝ≥0∞) < ⨅ n : ℕ, q ^ n := lt_of_lt_of_le hx0 hcle
    exact absurd hc.symm (ne_of_lt hlt)
  have hdmul : (1 - q) * ∑' n : ℕ, q ^ n = 1 := by
    rw [hsup]
    exact le_antisymm hsup2 hsup1
  have hSne : ∑' n : ℕ, q ^ n ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hq0.ne'] at hdmul
    exact absurd hdmul (by simp)
  calc ∑' n : ℕ, q ^ n
      = (1 - q)⁻¹ * ((1 - q) * ∑' n : ℕ, q ^ n) :=
        (ENNReal.inv_mul_cancel_left hq0.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)).symm
    _ = (1 - q)⁻¹ * 1 := by rw [hdmul]
    _ = (1 - q)⁻¹ := mul_one _

end GeomHelpers

section TailBridge

theorem haltJoint_tsum_split (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
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

theorem pendingMass_eq_tail_add_nontermination (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (n : ℕ) :
    pendingMass next cfg n
      = (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
        + nonterminationMass next cfg := by
  have hpart := (unbounded_finite_halt_pending_partition next cfg n).2.1
  have hlimit := haltJoint_tsum_add_nonterminationMass next cfg
  have hsplit : (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)
      = (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0) := by
    calc (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k)
        = ∑' o : O, ((∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0)) :=
          tsum_congr fun o => haltJoint_tsum_split next cfg o n
      _ = (∑' o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_add
      _ = (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0) := by
          rw [tsum_fintype (L := SummationFilter.unconditional O)]
  have hHn : (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k) ≠ ⊤ := by
    have hle : (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        ≤ ∑ o : O, ∑ k ∈ Finset.range (n + 1), (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun k _ => PMF.coe_le_one _ _
    have hval : (∑ o : O, ∑ k ∈ Finset.range (n + 1), (1 : ℝ≥0∞))
        = (Fintype.card O : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞) := by
      simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact ne_top_of_le_ne_top (hval ▸
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)) hle
  have hsum : (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + pendingMass next cfg n
      = (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
        + ((∑' o : O, ∑' k : ℕ, haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
          + nonterminationMass next cfg) := by
    calc (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
          + pendingMass next cfg n
        = 1 := hpart
      _ = (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + nonterminationMass next cfg :=
          hlimit.symm
      _ = ((∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
            + ∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0))
          + nonterminationMass next cfg := by rw [hsplit]
      _ = (∑ o : O, ∑ k ∈ Finset.range (n + 1), haltJoint next cfg o k)
          + ((∑' o : O, ∑' k : ℕ, haltJoint next cfg o k
              * (if n < k then (1 : ℝ≥0∞) else 0))
            + nonterminationMass next cfg) := add_assoc _ _ _
  exact WithTop.add_left_cancel hHn hsum

end TailBridge

theorem tsum_indicator_lt_ennreal (k : ℕ) :
    ∑' n : ℕ, (if n < k then (1 : ℝ≥0∞) else 0) = (k : ℝ≥0∞) := by
  refine (tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range k)
    (f := fun n => if n < k then (1 : ℝ≥0∞) else 0)
    (fun n hn => if_neg (Finset.mem_range.not.mp hn))).trans ?_
  rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn) :
      ∀ n ∈ Finset.range k, (if n < k then (1 : ℝ≥0∞) else 0) = 1),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem tsum_const_nat_ennreal (c : ℝ≥0∞) : ∑' _n : ℕ, c = ⊤ * c := by
  rw [ENNReal.tsum_const]
  simp

theorem tsum_tail_eq_cost_weighted_haltJoint (next : S → PMF (Configuration S O))
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
        tsum_congr fun o => tsum_congr fun k => by rw [tsum_indicator_lt_ennreal]
    _ = ∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k :=
        tsum_congr fun o => tsum_congr fun k => mul_comm _ _

noncomputable def unboundedTime (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : ℝ≥0∞ :=
  ∑' n : ℕ, pendingMass next cfg n

theorem unbounded_expected_time_tail_sum (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) :
    unboundedTime next cfg = ∑' n : ℕ, pendingMass next cfg n ∧
      unboundedTime next cfg = (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k) +
        (⊤ : ℝ≥0∞) * nonterminationMass next cfg ∧
      (unboundedTime next cfg < ⊤ → nonterminationMass next cfg = 0) := by
  have h2 : unboundedTime next cfg
      = (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k)
        + (⊤ : ℝ≥0∞) * nonterminationMass next cfg := by
    show (∑' n : ℕ, pendingMass next cfg n) = _
    calc (∑' n : ℕ, pendingMass next cfg n)
        = ∑' n : ℕ, ((∑' o : O, ∑' k : ℕ,
              haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
            + nonterminationMass next cfg) :=
          tsum_congr fun n => pendingMass_eq_tail_add_nontermination next cfg n
      _ = (∑' n : ℕ, ∑' o : O, ∑' k : ℕ,
              haltJoint next cfg o k * (if n < k then (1 : ℝ≥0∞) else 0))
            + ∑' n : ℕ, nonterminationMass next cfg := ENNReal.tsum_add
      _ = (∑' o : O, ∑' k : ℕ, (k : ℝ≥0∞) * haltJoint next cfg o k)
            + (⊤ : ℝ≥0∞) * nonterminationMass next cfg := by
          rw [tsum_tail_eq_cost_weighted_haltJoint, tsum_const_nat_ennreal]
  refine ⟨rfl, h2, fun hlt => ?_⟩
  by_contra hN
  rw [h2, ENNReal.top_mul hN, add_top] at hlt
  exact absurd hlt (lt_irrefl _)

theorem unbounded_online_cutoff_markov (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    (fuel+1 : ℝ≥0∞) * pendingMass next cfg fuel ≤ unboundedTime next cfg ∧
      pendingMass next cfg fuel ≤ unboundedTime next cfg / (fuel+1 : ℝ≥0∞) := by
  have h1 : (fuel+1 : ℝ≥0∞) * pendingMass next cfg fuel ≤ unboundedTime next cfg := by
    calc (fuel+1 : ℝ≥0∞) * pendingMass next cfg fuel
        = ∑ _n ∈ Finset.range (fuel + 1), pendingMass next cfg fuel := by
          rw [← Nat.cast_add_one]
          exact (sum_range_const_ennreal (fuel + 1) _).symm
      _ ≤ ∑ n ∈ Finset.range (fuel + 1), pendingMass next cfg n :=
          Finset.sum_le_sum fun n hn =>
            pendingMass_antitone next cfg (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      _ ≤ ∑' n : ℕ, pendingMass next cfg n := ENNReal.sum_le_tsum _
      _ = unboundedTime next cfg := rfl
  refine ⟨h1, ?_⟩
  have hne : (fuel+1 : ℝ≥0∞) ≠ 0 := by
    rw [← Nat.cast_add_one]
    simp
  have htop : (fuel+1 : ℝ≥0∞) ≠ ⊤ := by
    rw [← Nat.cast_add_one]
    exact ENNReal.natCast_ne_top _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl htop), mul_comm]
  exact h1

theorem unbounded_output_event_cutoff_gap (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) (E : Finset O) :
    (∑ o ∈ E, ∑ k ∈ Finset.range (fuel+1), haltJoint next cfg o k) ≤
        ∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k ∧
      (∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k) ≤
        (∑ o ∈ E, ∑ k ∈ Finset.range (fuel+1), haltJoint next cfg o k)
          + pendingMass next cfg fuel := by
  refine ⟨Finset.sum_le_sum fun o _ => ENNReal.sum_le_tsum _, ?_⟩
  calc (∑ o ∈ E, ∑' k : ℕ, haltJoint next cfg o k)
      = ∑ o ∈ E, ((∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + ∑' k : ℕ, haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0)) :=
        Finset.sum_congr rfl fun o _ => haltJoint_tsum_split next cfg o fuel
    _ = (∑ o ∈ E, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + ∑ o ∈ E, ∑' k : ℕ,
            haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (∑ o ∈ E, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)
          + pendingMass next cfg fuel := by
        have htail : (∑ o ∈ E, ∑' k : ℕ,
              haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0))
            ≤ pendingMass next cfg fuel := by
          calc (∑ o ∈ E, ∑' k : ℕ,
                  haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0))
              ≤ ∑' o : O, ∑' k : ℕ,
                  haltJoint next cfg o k * (if fuel < k then (1 : ℝ≥0∞) else 0) :=
                ENNReal.sum_le_tsum E
            _ ≤ pendingMass next cfg fuel := by
                rw [pendingMass_eq_tail_add_nontermination]
                exact le_self_add
        exact add_le_add (le_refl _) htail

theorem unbounded_geometric_kernel_runtime (next : S → PMF (Configuration S O))
    (s : S) (q : ℝ≥0∞) (hq : q < 1)
    (hstep : ∀ x : S, ∑ y : S, next x (Sum.inr y) ≤ q) :
    (∀ n : ℕ, pendingMass next (Sum.inr s) n ≤ q ^ n) ∧
      nonterminationMass next (Sum.inr s) = 0 ∧
      unboundedTime next (Sum.inr s) ≤ (1 - q)⁻¹ := by
  have hev : ∀ x : S, CostedLaw.event (next x) (fun cfg => ∃ u : S, cfg = Sum.inr u) ≤ q := by
    intro x
    have heq : CostedLaw.event (next x) (fun cfg => ∃ u : S, cfg = Sum.inr u)
        = ∑ y : S, next x (Sum.inr y) := by
      have hsplit : (∑' c : O ⊕ S, next x c
            * (if (∃ u : S, c = Sum.inr u) then (1 : ℝ≥0∞) else 0))
          = (∑' o : O, next x (Sum.inl o)
              * (if (∃ u : S, Sum.inl o = Sum.inr u) then (1 : ℝ≥0∞) else 0))
            + ∑' t : S, next x (Sum.inr t)
              * (if (∃ u : S, Sum.inr t = Sum.inr u) then (1 : ℝ≥0∞) else 0) :=
        tsum_sum_type' (F := fun c : O ⊕ S => next x c
          * (if (∃ u : S, c = Sum.inr u) then (1 : ℝ≥0∞) else 0))
      have hinl : (∑' o : O, next x (Sum.inl o)
            * (if (∃ u : S, Sum.inl o = Sum.inr u) then (1 : ℝ≥0∞) else 0)) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun o => ?_
        rw [if_neg (fun h : (∃ u : S, Sum.inl o = Sum.inr u) => Sum.inl_ne_inr h.choose_spec),
          mul_zero]
      have hinr : (∑' t : S, next x (Sum.inr t)
            * (if (∃ u : S, Sum.inr t = Sum.inr u) then (1 : ℝ≥0∞) else 0))
          = ∑' t : S, next x (Sum.inr t) :=
        tsum_congr fun t => by
          rw [if_pos (⟨t, rfl⟩ : ∃ u : S, (Sum.inr t : O ⊕ S) = Sum.inr u), mul_one]
      have hev : CostedLaw.event (next x) (fun cfg => ∃ u : S, cfg = Sum.inr u)
          = ∑' c : O ⊕ S, next x c
            * (if (∃ u : S, c = Sum.inr u) then (1 : ℝ≥0∞) else 0) := by
        rw [CostedLaw.event_eq, show (∑' c : O ⊕ S, next x c
              * (if (∃ u : S, c = Sum.inr u) then (1 : ℝ≥0∞) else 0))
            = CostedLaw.expectation (next x)
              (fun c => if (∃ u : S, c = Sum.inr u) then (1 : ℝ≥0∞) else 0) from rfl]
        refine CostedLaw.expectation_congr fun c => ?_
        by_cases h : (∃ u : S, c = Sum.inr u)
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
      rw [hev, hsplit, hinl, hinr, zero_add,
        tsum_fintype (L := SummationFilter.unconditional S)]
    rw [heq]; exact hstep x
  have hpow : ∀ n : ℕ, pendingMass next (Sum.inr s) n ≤ q ^ n := fun n => by
    rw [pendingMass_eq_finiteSurvival]
    exact (finite_survival_geometric_bound next s q n hq.le hev).1
  refine ⟨hpow, ?_, ?_⟩
  · have hle : ⨅ n : ℕ, pendingMass next (Sum.inr s) n ≤ 0 :=
      calc ⨅ n : ℕ, pendingMass next (Sum.inr s) n
          ≤ ⨅ n : ℕ, q ^ n := iInf_mono hpow
        _ = 0 := iInf_pow_eq_zero_ennreal q hq
    exact le_antisymm hle zero_le
  · calc unboundedTime next (Sum.inr s)
        = ∑' n : ℕ, pendingMass next (Sum.inr s) n := rfl
      _ ≤ ∑' n : ℕ, q ^ n := ENNReal.tsum_le_tsum hpow
      _ = (1 - q)⁻¹ := geom_tsum_ennreal q hq

end Qatlib.Concepts.StoppingCore.BranchCostCore
