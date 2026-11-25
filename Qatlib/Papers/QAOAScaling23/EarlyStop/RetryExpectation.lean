/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Composition
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Paid time under feed-forward rejection

Equations (S21)–(S22) of arXiv:2308.02342v2 use equal-duration stages and
neglect the time of parity checks. Implement each attempt as a finite tree:
pay for a stage if reached, and stop at the first rejection. Retry with
fresh draws. The expectation is the limit of the capped executions.
-/

set_option autoImplicit false

noncomputable section

open Filter
open Qatlib.Foundations.ProbabilityCore
open scoped Topology BigOperators ENNReal

namespace Qatlib.Papers.QAOAScaling23.EarlyStop

/-- Stage outcomes are rejection at index zero and passage at index one. -/
def checkCoin (q : unitInterval) : PMF (Fin 2) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i = 0 then 1 - (q : ℝ) else q)) (by
    rw [Fin.sum_univ_two]
    change ENNReal.ofReal (1 - (q : ℝ)) + ENNReal.ofReal (q : ℝ) = 1
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr q.2.2) q.2.1]
    simp)

/-- Choose the rejection or passage continuation using the conditional stage probability. -/
def stageCheck {α : Type} (q : unitInterval) (reject pass : FiniteBranch.Tree α) : FiniteBranch.Tree α :=
  .sample 2 (checkCoin q) (fun i => if i = 0 then reject else pass)

/-- The mean of a stage check is the two branch means with their actual weights. -/
private theorem stageCheck_mean {α : Type} (q : unitInterval) (r s : FiniteBranch.Tree α) (f : α → ℝ) :
    (stageCheck q r s).mean f = (1 - (q : ℝ)) * r.mean f + (q : ℝ) * s.mean f := by
  rw [stageCheck, FiniteBranch.Tree.mean, Fin.sum_univ_two]
  simp [checkCoin, ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2), ENNReal.toReal_ofReal q.2.1]

/-- A single attempt reports passage and the number of stages actually paid. -/
def checkAttempt : {m : ℕ} → (Fin m → unitInterval) → FiniteBranch.Tree (Bool × ℕ)
  | 0, _ => .pure (true, 0)
  | m + 1, p =>
      stageCheck (p 0) (.pure (false, 1))
        ((checkAttempt (m := m) (fun i => p i.succ)).map (fun z => (z.1, z.2 + 1)))

/-- The probability of reaching each stage is the product of the preceding conditional passes. -/
def prefixPaidStages {m : ℕ} (p : Fin m → unitInterval) : ℝ :=
  ∑ i : Fin m, ∏ j ∈ Finset.Iio i, (p j : ℝ)

/-- Inserting an initial stage puts its pass probability in every later prefix. -/
private theorem prefixPaidStages_succ {m : ℕ} (p : Fin (m + 1) → unitInterval) :
    prefixPaidStages p = 1 + (p 0 : ℝ) * prefixPaidStages (fun i : Fin m => p i.succ) := by
  rw [prefixPaidStages, Fin.sum_univ_succ, prefixPaidStages]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hsplit : Finset.Iio i.succ = insert 0 (Finset.Ioo 0 i.succ) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_Ioo, Fin.lt_def,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ]
    omega
  rw [hsplit, Finset.prod_insert (by simp), ← Fin.map_succEmb_Iio, Finset.prod_map]
  rfl

/-- The actual attempt passes precisely along the branch that passes every stage. -/
theorem checkAttempt_pass {m : ℕ} (p : Fin m → unitInterval) :
    (checkAttempt p).probability (fun x => x.1 = true) = ∏ i, (p i : ℝ) := by
  induction m with
  | zero => simp [checkAttempt, FiniteBranch.Tree.probability, FiniteBranch.Tree.mean]
  | succ m ih =>
      rw [checkAttempt, FiniteBranch.Tree.probability, stageCheck_mean]
      simp only [FiniteBranch.Tree.mean, Bool.false_eq_true, ite_false, mul_zero, zero_add, FiniteBranch.Tree.mean_map]
      change (p 0 : ℝ) * (checkAttempt (fun i : Fin m => p i.succ)).probability
        (fun x => x.1 = true) = _
      rw [ih, Fin.prod_univ_succ]

/-- The expected paid length of an actual attempt is its sum of prefix probabilities. -/
theorem checkAttempt_paid {m : ℕ} (p : Fin m → unitInterval) :
    (checkAttempt p).mean (fun x => (x.2 : ℝ)) = prefixPaidStages p := by
  induction m with
  | zero => simp [checkAttempt, FiniteBranch.Tree.mean, prefixPaidStages]
  | succ m ih =>
    rw [checkAttempt, stageCheck_mean, FiniteBranch.Tree.mean_map]
    simp only [FiniteBranch.Tree.mean, Nat.cast_one, Nat.cast_add, FiniteBranch.Tree.mean_add, FiniteBranch.Tree.mean_const, mul_one]
    rw [ih, prefixPaidStages_succ]
    ring

/-- The rejection indicator mean equals the probability of the rejection event. -/
private theorem rejectedMean_eq_probability (tree : FiniteBranch.Tree (Bool × ℕ)) :
    (tree.mean (fun x => if ¬x.1 = true then 1 else 0)) =
      tree.probability (fun x => ¬x.1 = true) := by
  unfold FiniteBranch.Tree.probability
  apply FiniteBranch.Tree.mean_congr _ (FiniteBranch.Tree.all_of_forall _ ?_)
  intro x
  cases hb : x.1 <;> simp [hb]

/-- The failed-attempt mass is the complement of the all-pass product. -/
private theorem attempt_rejectedMean {m : ℕ} (p : Fin m → unitInterval) :
    (checkAttempt p).mean (fun x => if ¬x.1 = true then 1 else 0) =
      1 - ∏ i, (p i : ℝ) := by
  rw [rejectedMean_eq_probability]
  have hrej := (checkAttempt p).probability_compl (fun x => x.1 = true)
  rw [checkAttempt_pass] at hrej
  linarith

/-- Retry independently after rejection, stopping on success or when the attempt cap is exhausted. -/
def cappedRetries {m : ℕ} (p : Fin m → unitInterval) : ℕ → FiniteBranch.Tree (Bool × ℕ)
  | 0 => .pure (false, 0)
  | cap + 1 =>
      (checkAttempt p).bind (fun x => if x.1 then .pure x else
        (cappedRetries p cap).map (fun y => (y.1, x.2 + y.2)))

/-- A capped retry pays for its first attempt, and pays its continuation only on rejection. -/
theorem cappedRetries_paid_succ {m : ℕ} (p : Fin m → unitInterval) (cap : ℕ) :
    (cappedRetries p (cap + 1)).mean (fun x => (x.2 : ℝ)) =
      prefixPaidStages p + (1 - ∏ i, (p i : ℝ)) * (cappedRetries p cap).mean (fun x => (x.2 : ℝ)) := by
  let f : Bool × ℕ → ℝ := fun x => (x.2 : ℝ)
  let e := (cappedRetries p cap).mean f
  rw [cappedRetries, FiniteBranch.Tree.mean_bind]
  have hleaf (x : Bool × ℕ) :
      (if x.1 then FiniteBranch.Tree.pure x else
        (cappedRetries p cap).map (fun y => (y.1, x.2 + y.2))).mean f =
      f x + e * (if ¬x.1 = true then 1 else 0) := by
    rcases x with ⟨b, k⟩
    cases b <;> simp [f, e, FiniteBranch.Tree.mean, FiniteBranch.Tree.mean_map, Nat.cast_add, FiniteBranch.Tree.mean_add, FiniteBranch.Tree.mean_const]
  calc
    _ = (checkAttempt p).mean (fun x => f x + e * (if ¬x.1 = true then 1 else 0)) :=
      FiniteBranch.Tree.mean_congr _ (FiniteBranch.Tree.all_of_forall _ hleaf)
    _ = prefixPaidStages p + e * (1 - ∏ i, (p i : ℝ)) := by
      rw [FiniteBranch.Tree.mean_add, FiniteBranch.Tree.mean_mul]
      dsimp only [f]
      rw [checkAttempt_paid, attempt_rejectedMean]
    _ = _ := by rw [mul_comm e]

/-- The actual finite capped mean is a geometric sum of the cost of one attempt. -/
theorem cappedRetries_paid {m : ℕ} (p : Fin m → unitInterval) (cap : ℕ) :
    (cappedRetries p cap).mean (fun x => (x.2 : ℝ)) =
      prefixPaidStages p * ∑ k ∈ Finset.range cap, (1 - ∏ i, (p i : ℝ)) ^ k := by
  induction cap with
  | zero => simp [cappedRetries, FiniteBranch.Tree.mean]
  | succ cap ih =>
    let r := 1 - ∏ i, (p i : ℝ)
    rw [cappedRetries_paid_succ, ih, Finset.sum_range_succ']
    change _ + r * (_ * ∑ k ∈ Finset.range cap, r ^ k) =
      _ * ((∑ k ∈ Finset.range cap, r ^ (k + 1)) + r ^ 0)
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    ring

/-- The actual capped run has a geometric probability of exhausting all its attempts. -/
theorem cappedRetries_no_success {m : ℕ} (p : Fin m → unitInterval) (cap : ℕ) :
    (cappedRetries p cap).probability (fun x => ¬x.1 = true) =
      (1 - ∏ i, (p i : ℝ)) ^ cap := by
  rw [← rejectedMean_eq_probability]
  induction cap with
  | zero => simp [cappedRetries, FiniteBranch.Tree.mean]
  | succ cap ih =>
      let f : Bool × ℕ → ℝ := fun x => if ¬x.1 = true then 1 else 0
      let e := (cappedRetries p cap).mean f
      change (cappedRetries p (cap + 1)).mean f = _
      rw [cappedRetries, FiniteBranch.Tree.mean_bind]
      have hleaf (x : Bool × ℕ) :
          (if x.1 then FiniteBranch.Tree.pure x else
            (cappedRetries p cap).map (fun y => (y.1, x.2 + y.2))).mean f = e * f x := by
        rcases x with ⟨b, k⟩
        cases b <;> simp [f, e, FiniteBranch.Tree.mean, FiniteBranch.Tree.mean_map]
      rw [FiniteBranch.Tree.mean_congr _ (FiniteBranch.Tree.all_of_forall _ hleaf),
        FiniteBranch.Tree.mean_mul]
      dsimp only [e, f]
      rw [ih, attempt_rejectedMean, pow_succ]

/-- Positive all-pass probability makes exhausting the cap vanish in the infinite cap limit. -/
theorem cappedRetries_no_success_tendsto_zero {m : ℕ} (p : Fin m → unitInterval)
    (hp : 0 < ∏ i, (p i : ℝ)) :
    Tendsto (fun cap => (cappedRetries p cap).probability (fun x => ¬x.1 = true))
      atTop (𝓝 0) := by
  simp_rw [cappedRetries_no_success]
  have hP1 : (∏ i, (p i : ℝ)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (p i).2.1) (fun i _ => (p i).2.2)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hP1) (by linarith)

/-- Eq. (S22) for equal-duration stages as the limit of actual capped retry programs.
The prefix sum is at most the number of stages, giving the comparison with Eq. (S21). -/
theorem early_stop_expectation {m : ℕ} (hm : 0 < m) (p : Fin m → unitInterval)
    (hp : 0 < ∏ i, (p i : ℝ)) (t₀ : ℝ) (ht : 0 ≤ t₀) :
    let P := ∏ i, (p i : ℝ)
    let μ := (t₀ / m) * prefixPaidStages p / P
    Tendsto (fun cap => (t₀ / m) * (cappedRetries p cap).mean (fun x => (x.2 : ℝ)))
      atTop (𝓝 μ) ∧ μ ≤ t₀ / P := by
  let P := ∏ i, (p i : ℝ)
  have hP1 : P ≤ 1 := Finset.prod_le_one₀ (fun i _ => (p i).2.1) (fun i _ => (p i).2.2)
  have hg := (hasSum_geometric_of_lt_one (r := 1 - P) (sub_nonneg.mpr hP1) (by linarith)).tendsto_sum_nat
  have hprefix : prefixPaidStages p ≤ (m : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ =>
          Finset.prod_le_one₀ (fun j _ => (p j).2.1) (fun j _ => (p j).2.2)
      _ = _ := by simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_⟩
  · simp_rw [cappedRetries_paid]
    simpa only [← mul_assoc, sub_sub_cancel, div_eq_mul_inv] using
      hg.const_mul ((t₀ / m) * prefixPaidStages p)
  · apply div_le_div_of_nonneg_right _ hp.le
    calc
      _ ≤ (t₀ / m) * m := mul_le_mul_of_nonneg_left hprefix (div_nonneg ht hmR.le)
      _ = t₀ := div_mul_cancel₀ t₀ hmR.ne'

end Qatlib.Papers.QAOAScaling23.EarlyStop
