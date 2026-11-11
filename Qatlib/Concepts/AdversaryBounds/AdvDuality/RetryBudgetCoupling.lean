/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Couplings for planned retries at different budgets

This module compares two executions of a `PlannedRetry` kernel with ordered budgets.
`coupledRetry` shares plan choices and trial outcomes while both budgets can pay for the next
trial. `retry_common_prefix_marginals` identifies the two marginal laws, and
`retry_coupled_success_and_spending` relates successful outputs, remaining budgets, and spent
costs. Repeated trials in quantum search provide a motivating setting; see [BrassardEtAl2002]
for amplitude amplification and estimation.

`retry_output_event_budget_mono` proves monotonicity of successful output events as the budget
increases. `retry_success_law_same_spent_prefix` gives the stronger pointwise equality for a
fixed successful output and an affordable spent cost. The intervening natural-number identities
support the conversion between remaining and spent budgets.

## Main statements

* `retry_common_prefix_marginals`: marginal retry laws at ordered budgets.
* `retry_coupled_success_and_spending`: shared successful outputs and spent costs.
* `retry_success_law_same_spent_prefix`: equality of successful masses at fixed affordable
  spending.

## References

* [Brassard, Hoyer, Mosca, and Tapp, 2002][BrassardEtAl2002], *Quantum amplitude amplification
  and estimation*.
-/

set_option warningAsError false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped ENNReal BigOperators Classical

set_option autoImplicit false

universe u v w

variable {State : Type u} {Output : Type v}

/-- A sum of extended nonnegative real numbers equals its value at `a` if every other summand
vanishes. -/
theorem tsum_eq_single_of {α : Type*} (f : α → ℝ≥0∞) (a : α)
    (h : ∀ b, b ≠ a → f b = 0) : ∑' b, f b = f a :=
  tsum_eq_single a h

/-- A joint retry law sharing plan choices and outcomes while both budgets can pay for a trial.
When only the right budget can pay, the left result is fixed and the right run continues. -/
noncomputable def coupledRetry (K : PlannedRetry State Output) (B C : ℕ) (s : State) :
    PMF ((Option Output × ℕ) × (Option Output × ℕ)) :=
  (K.choose s).bind fun p =>
    if _hB : (K.cost s p : ℕ) ≤ B then
      if _hC : (K.cost s p : ℕ) ≤ C then
        (K.perform s p).bind fun o =>
          match o with
          | some a => PMF.pure ((some a, B - (K.cost s p : ℕ)), (some a, C - (K.cost s p : ℕ)))
          | none => coupledRetry K (B - (K.cost s p : ℕ)) (C - (K.cost s p : ℕ)) (K.retry s p)
      else PMF.pure ((none, B), (none, C))
    else
      if _hC : (K.cost s p : ℕ) ≤ C then
        (K.perform s p).bind fun o =>
          match o with
          | some a => PMF.pure ((none, B), (some a, C - (K.cost s p : ℕ)))
          | none => (K.run (C - (K.cost s p : ℕ)) (K.retry s p)).map (fun r => ((none, B), r))
      else PMF.pure ((none, B), (none, C))
termination_by C
decreasing_by
  exact Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos ‹_›) (K.cost s p).pos

/-- Pairing a retry run with the fixed left result `(none, b)` preserves the retry law as the
right marginal. -/
theorem coupledRetry_frozen_right (K : PlannedRetry State Output) (b c : ℕ) (s : State) :
    (((K.run c s).map (fun r : Option Output × ℕ => ((none, b), r)))
      : PMF ((Option Output × ℕ) × (Option Output × ℕ))).map Prod.snd
      = K.run c s := by
  rw [PMF.map_comp, Function.comp_def]
  exact PMF.map_id (K.run c s)

/-- Pairing a retry run with the fixed left result `(none, b)` gives the point mass at that
result as the left marginal. -/
theorem coupledRetry_frozen_left (K : PlannedRetry State Output) (b c : ℕ) (s : State) :
    (((K.run c s).map (fun r : Option Output × ℕ => ((none, b), r)))
      : PMF ((Option Output × ℕ) × (Option Output × ℕ))).map Prod.fst
      = (PMF.pure (none, b) : PMF (Option Output × ℕ)) := by
  rw [PMF.map_comp, Function.comp_def]
  exact PMF.map_const (K.run c s) (none, b)

/-- Subtracting the same natural number preserves a non-strict inequality. -/
theorem nat_sub_mono_le {B C k : ℕ} (h : B ≤ C) : B - k ≤ C - k := by omega

/-- Subtracting a positive affordable cost strictly decreases a natural-number budget. -/
theorem nat_sub_lt_budget {C k : ℕ} (hk : 0 < k) (hCk : k ≤ C) : C - k < C := by omega

/-- A cost bounded by `B` is also bounded by any budget `C` with `B ≤ C`. -/
theorem le_trans_of_le {B C k : ℕ} (hB : k ≤ B) (hBC : B ≤ C) : k ≤ C :=
  Nat.le_trans hB hBC

/-- Evaluate a mapped probability mass function as the sum of the original masses weighted by
point masses at their images. -/
theorem pmf_map_apply_eq {α β : Type*} (p : PMF α) (g : α → β) (a : β) :
    (p.map g) a = ∑' b, p b * (PMF.pure (g b)) a := by
  have h : p.map g = p.bind (fun b => PMF.pure (g b)) := by
    refine PMF.ext fun a => ?_
    rw [PMF.map_apply, PMF.bind_apply]
    refine tsum_congr fun b => ?_
    by_cases hab : a = g b
    · rw [if_pos hab, PMF.pure_apply, if_pos hab, mul_one]
    · rw [if_neg hab, PMF.pure_apply, if_neg hab, mul_zero]
  rw [h, PMF.bind_apply]

/-- For `q ≤ C`, subtracting `C - q` from `C` recovers `q`. -/
theorem nat_sub_sub_of_le {C q : ℕ} (h : q ≤ C) : C - (C - q) = q := by omega

/-- If `r` and `q` lie below `C` and `C - r = q`, then `r = C - q`. -/
theorem nat_sub_eq_of_le {C r q : ℕ} (hr : r ≤ C) (hq : q ≤ C) (h : C - r = q) :
    r = C - q := by
  have h1 : q + r = C := by
    rw [← h, Nat.sub_add_cancel hr]
  omega

/-- For an affordable spent cost `q`, the successful mass in `costedRun` equals the mass in
`run` at remaining budget `budget - q`. -/
theorem costedRun_apply (K : PlannedRetry State Output) (budget : ℕ) (s : State) (o : Output)
    (q : ℕ) (hq : q ≤ budget) :
    (K.costedRun budget s) (some o, q) = K.run budget s (some o, budget - q) := by
  rw [PlannedRetry.costedRun, pmf_map_apply_eq]
  have hstep : (fun b : Option Output × ℕ =>
        K.run budget s b * (PMF.pure (b.1, budget - b.2)) (some o, q))
      = (fun b : Option Output × ℕ =>
          if b = (some o, budget - q) then K.run budget s (some o, budget - q) else 0) := by
    funext b
    by_cases hr : b.2 ≤ budget
    · by_cases hx : b.1 = some o
      · by_cases hy : budget - b.2 = q
        · have hc : (some o, q) = (some o, budget - b.2) := Prod.ext rfl hy.symm
          have hbeq : b = (some o, budget - q) := Prod.ext hx (nat_sub_eq_of_le hr hq hy)
          rw [hx, PMF.pure_apply, if_pos hc, mul_one, if_pos hbeq, hbeq]
        · have hne : b ≠ (some o, budget - q) := by
            intro hh
            exact hy (by rw [hh, nat_sub_sub_of_le hq])
          rw [PMF.pure_apply, if_neg (fun hh => hy (congrArg Prod.snd hh).symm), mul_zero,
            if_neg hne]
      · have hne : b ≠ (some o, budget - q) := by
          intro hh
          exact hx (congrArg Prod.fst hh)
        rw [PMF.pure_apply, if_neg (fun hh => hx (congrArg Prod.fst hh).symm), mul_zero,
          if_neg hne]
    · have hb0 : K.run budget s b = 0 := by
        refine (PMF.apply_eq_zero_iff (K.run budget s) b).mpr ?_
        intro hb
        exact hr ((K.run_remaining budget s b hb).1)
      have hne : b ≠ (some o, budget - q) := by
        intro hh
        exact hr (by rw [hh]; exact Nat.sub_le _ _)
      rw [hb0, zero_mul, if_neg hne]
  rw [hstep]
  have hcol : ∑' (b : Option Output × ℕ),
      (if b = (some o, budget - q) then K.run budget s (some o, budget - q) else 0)
      = K.run budget s (some o, budget - q) := by
    have h := tsum_eq_single_of
      (fun b : Option Output × ℕ =>
        if b = (some o, budget - q) then K.run budget s (some o, budget - q) else 0)
      (some o, budget - q) (fun b hb => by
        show (if b = (some o, budget - q) then K.run budget s (some o, budget - q) else 0) = 0
        rw [if_neg hb])
    simpa only [if_pos rfl] using! h
  rw [hcol]

/-- For `B ≤ C`, the left and right marginals of `coupledRetry K B C s` are the retry laws with
budgets `B` and `C`, respectively. -/
theorem retry_common_prefix_marginals (K : PlannedRetry State Output) (B C : ℕ) (s : State)
    (hBC : B ≤ C) :
    (coupledRetry K B C s).map Prod.fst = K.run B s ∧
    (coupledRetry K B C s).map Prod.snd = K.run C s := by
  have hleft : ∀ (c : ℕ) (b : ℕ) (st : State), b ≤ c →
      (coupledRetry K b c st).map Prod.fst = K.run b st := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro b st hbc
      rw [PlannedRetry.run, coupledRetry, PMF.map_bind]
      apply congrArg (fun (f : K.Plan st → PMF (Option Output × ℕ)) => (K.choose st).bind f)
      funext p
      by_cases hB : (K.cost st p : ℕ) ≤ b
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · simp only [dif_pos hB, dif_pos hC, PMF.map_bind]
          apply congrArg
            (fun (g : Option Output → PMF (Option Output × ℕ)) => (K.perform st p).bind g)
          funext o
          cases o with
          | some a => rw [PMF.pure_map]
          | none =>
            exact ih (c - (K.cost st p : ℕ))
              (nat_sub_lt_budget (K.cost st p).pos hC)
              (b - (K.cost st p : ℕ)) (K.retry st p) (nat_sub_mono_le hbc)
        · exact absurd (le_trans_of_le hB hbc) hC
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · simp only [dif_neg hB, dif_pos hC, PMF.map_bind]
          have hfrz := coupledRetry_frozen_left K b (c - (K.cost st p : ℕ)) (K.retry st p)
          have hinner : (fun o : Option Output => PMF.map Prod.fst
                (match o with
                | some a => (PMF.pure ((none, b), some a, c - (K.cost st p : ℕ))
                    : PMF ((Option Output × ℕ) × (Option Output × ℕ)))
                | none => (K.run (c - (K.cost st p : ℕ)) (K.retry st p)).map
                    (fun r : Option Output × ℕ => ((none, b), r))) :
                Option Output → PMF (Option Output × ℕ))
              = fun _ => PMF.pure (none, b) := by
            funext o
            cases o with
            | some a => rw [PMF.pure_map]
            | none => exact hfrz
          rw [hinner, PMF.bind_const]
        · simp only [dif_neg hB, dif_neg hC, PMF.pure_map]
  refine ⟨hleft C B s hBC, ?_⟩
  have hright : ∀ (c : ℕ) (b : ℕ) (st : State), b ≤ c →
      (coupledRetry K b c st).map Prod.snd = K.run c st := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro b st hbc
      rw [PlannedRetry.run, coupledRetry, PMF.map_bind]
      apply congrArg (fun (f : K.Plan st → PMF (Option Output × ℕ)) => (K.choose st).bind f)
      funext p
      by_cases hB : (K.cost st p : ℕ) ≤ b
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · simp only [dif_pos hB, dif_pos hC, PMF.map_bind]
          apply congrArg
            (fun (g : Option Output → PMF (Option Output × ℕ)) => (K.perform st p).bind g)
          funext o
          cases o with
          | some a => rw [PMF.pure_map]
          | none =>
            exact ih (c - (K.cost st p : ℕ))
              (nat_sub_lt_budget (K.cost st p).pos hC)
              (b - (K.cost st p : ℕ)) (K.retry st p) (nat_sub_mono_le hbc)
        · exact absurd (le_trans_of_le hB hbc) hC
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · simp only [dif_neg hB, dif_pos hC, PMF.map_bind]
          have hfrz := coupledRetry_frozen_right K b (c - (K.cost st p : ℕ)) (K.retry st p)
          have hinner : (fun o : Option Output => PMF.map Prod.snd
                (match o with
                | some a => (PMF.pure ((none, b), some a, c - (K.cost st p : ℕ))
                    : PMF ((Option Output × ℕ) × (Option Output × ℕ)))
                | none => (K.run (c - (K.cost st p : ℕ)) (K.retry st p)).map
                    (fun r : Option Output × ℕ => ((none, b), r))) :
                Option Output → PMF (Option Output × ℕ))
              = fun o => match o with
                | some a => PMF.pure (some a, c - (K.cost st p : ℕ))
                | none => K.run (c - (K.cost st p : ℕ)) (K.retry st p) := by
            funext o
            cases o with
            | some a => rw [PMF.pure_map]
            | none => exact hfrz
          rw [hinner]
          rfl
        · simp only [dif_neg hB, dif_neg hC, PMF.pure_map]
  exact hright C B s hBC

/-- The total spend `b - r` is the subsequent spend after paying `cost`, plus that initial cost,
provided both subtractions stay within the budget. -/
theorem nat_sub_spend_left {b cost r : ℕ} (hcB : cost ≤ b) (hr : r ≤ b - cost) :
    b - r = (b - cost) - r + cost := by omega

/-- The total spend `c - r` is the subsequent spend after paying `cost`, plus that initial cost,
provided both subtractions stay within the budget. -/
theorem nat_sub_spend_right {c cost r : ℕ} (hcC : cost ≤ c) (hr : r ≤ c - cost) :
    c - r = (c - cost) - r + cost := by omega

/-- Paying the same cost from ordered budgets preserves their difference when the cost is
affordable for the smaller budget. -/
theorem nat_sub_budget_diff {b c cost : ℕ} (hcB : cost ≤ b) (hbc : b ≤ c) :
    (c - cost) - (b - cost) = c - b := by omega

/-- After paying a cost affordable for `b ≤ c`, the remainder of `c` is the remainder of `b`
plus the original budget difference. -/
theorem nat_sub_add_diff {b c cost : ℕ} (hcB : cost ≤ b) (hbc : b ≤ c) :
    c - cost = (b - cost) + (c - b) := by omega

/-- Subtraction from a fixed natural number is injective on numbers bounded by that number. -/
theorem nat_sub_eq_of_eq {C r q : ℕ} (hr : r ≤ C) (hq : q ≤ C) (h : C - q = C - r) : q = r := by
  have h1 : C - q + q = C := Nat.sub_add_cancel hq
  have h2 : C - r + r = C := Nat.sub_add_cancel hr
  rw [h] at h1
  exact Nat.add_left_cancel (h1.trans h2.symm)

/-- The difference `b - b` is bounded by any natural-number difference `c - r`. -/
theorem nat_sub_self_le (b c r : ℕ) : b - b ≤ c - r := by
  rw [Nat.sub_self]
  exact Nat.zero_le _

/-- For `q < r ≤ B`, subtracting `r` from `B` gives a strictly smaller remainder than
subtracting `q`. -/
theorem nat_sub_lt_sub {B r q : ℕ} (hr : r ≤ B) (hqr : q < r) : B - r < B - q := by omega

/-- For `cost ≤ q ≤ B`, paying `cost` from both the budget and the intended spend leaves the
same final remainder. -/
theorem nat_sub_sub_add {B q cost : ℕ} (hq : q ≤ B) (hc : cost ≤ q) :
    B - q = (B - cost) - (q - cost) := by omega

/-- A successful retry result has zero mass if its remaining budget exceeds the initial budget. -/
theorem run_success_eq_zero_of_bgt (K : PlannedRetry State Output) (budget : ℕ) (st : State)
    (o : Output) (r : ℕ) (hr : budget < r) : K.run budget st (some o, r) = 0 :=
  (PMF.apply_eq_zero_iff (K.run budget st) (some o, r)).mpr fun hx =>
    Nat.not_le_of_lt hr ((K.run_remaining budget st (some o, r) hx).1)

/-- On the support of the coupling with `B ≤ C`, the smaller-budget run spends at most as much
as the larger-budget run. If the smaller run succeeds, both outputs agree, both spent costs
agree, and their remaining budgets differ by `C - B`. -/
theorem retry_coupled_success_and_spending (K : PlannedRetry State Output) (B C : ℕ) (s : State)
    (hBC : B ≤ C) (z : (Option Output × ℕ) × (Option Output × ℕ))
    (hz : z ∈ (coupledRetry K B C s).support) :
    B - z.1.2 ≤ C - z.2.2 ∧
      (z.1.1 ≠ none → z.2.1 = z.1.1 ∧ z.2.2 = z.1.2 + (C - B) ∧ C - z.2.2 = B - z.1.2) := by
  have hrem : ∀ (c b : ℕ) (st : State) (w : (Option Output × ℕ) × (Option Output × ℕ)),
      w ∈ (coupledRetry K b c st).support → w.1.2 ≤ b ∧ w.2.2 ≤ c := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro b st w hw
      rw [coupledRetry] at hw
      obtain ⟨p, _, hp⟩ := (PMF.mem_support_bind_iff _ _ w).mp hw
      by_cases hB : (K.cost st p : ℕ) ≤ b
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · rw [dif_pos hB, dif_pos hC] at hp
          obtain ⟨o, _, hw'⟩ := (PMF.mem_support_bind_iff _ _ w).mp hp
          cases o with
          | some a =>
            have heq : w = ((some a, b - (K.cost st p : ℕ)), (some a, c - (K.cost st p : ℕ))) :=
              (PMF.mem_support_pure_iff _ _).mp hw'
            subst w
            exact ⟨Nat.sub_le _ _, Nat.sub_le _ _⟩
          | none =>
            obtain ⟨h1, h2⟩ := ih (c - (K.cost st p : ℕ))
              (nat_sub_lt_budget (K.cost st p).pos hC) (b - (K.cost st p : ℕ)) (K.retry st p) w hw'
            exact ⟨Nat.le_trans h1 (Nat.sub_le _ _), Nat.le_trans h2 (Nat.sub_le _ _)⟩
        · rw [dif_pos hB, dif_neg hC] at hp
          have heq : w = ((none, b), (none, c)) := (PMF.mem_support_pure_iff _ _).mp hp
          subst w
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · rw [dif_neg hB, dif_pos hC] at hp
          obtain ⟨o, _, hw'⟩ := (PMF.mem_support_bind_iff _ _ w).mp hp
          cases o with
          | some a =>
            have heq : w = ((none, b), (some a, c - (K.cost st p : ℕ))) :=
              (PMF.mem_support_pure_iff _ _).mp hw'
            subst w
            exact ⟨Nat.le_refl _, Nat.sub_le _ _⟩
          | none =>
            obtain ⟨r, hr, hw2⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp hw'
            obtain ⟨hr2⟩ := K.run_remaining (c - (K.cost st p : ℕ)) (K.retry st p) r hr
            subst w
            exact ⟨Nat.le_refl _, Nat.le_trans hr2 (Nat.sub_le _ _)⟩
        · rw [dif_neg hB, dif_neg hC] at hp
          have heq : w = ((none, b), (none, c)) := (PMF.mem_support_pure_iff _ _).mp hp
          subst w
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have key : ∀ (c b : ℕ) (st : State), b ≤ c →
      ∀ w ∈ (coupledRetry K b c st).support,
        b - w.1.2 ≤ c - w.2.2 ∧
          (w.1.1 ≠ none → w.2.1 = w.1.1 ∧ w.2.2 = w.1.2 + (c - b) ∧ c - w.2.2 = b - w.1.2) := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro b st hbc w hw
      rw [coupledRetry] at hw
      obtain ⟨p, _, hp⟩ := (PMF.mem_support_bind_iff _ _ w).mp hw
      by_cases hB : (K.cost st p : ℕ) ≤ b
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · rw [dif_pos hB, dif_pos hC] at hp
          obtain ⟨o, _, hw'⟩ := (PMF.mem_support_bind_iff _ _ w).mp hp
          cases o with
          | some a =>
            have heq : w = ((some a, b - (K.cost st p : ℕ)), (some a, c - (K.cost st p : ℕ))) :=
              (PMF.mem_support_pure_iff _ _).mp hw'
            subst w
            have hL : b - (b - (K.cost st p : ℕ)) = (K.cost st p : ℕ) := nat_sub_sub_of_le hB
            have hR : c - (c - (K.cost st p : ℕ)) = (K.cost st p : ℕ) := nat_sub_sub_of_le hC
            refine ⟨(hL.trans hR.symm).le,
              fun _ => ⟨rfl, nat_sub_add_diff hB hbc, hR.trans hL.symm⟩⟩
          | none =>
            obtain ⟨h1, h2⟩ := ih (c - (K.cost st p : ℕ))
              (nat_sub_lt_budget (K.cost st p).pos hC) (b - (K.cost st p : ℕ)) (K.retry st p)
              (nat_sub_mono_le hbc) w hw'
            obtain ⟨hr1, hr2⟩ := hrem (c - (K.cost st p : ℕ)) (b - (K.cost st p : ℕ))
              (K.retry st p) w hw'
            have hML : b - w.1.2 = (b - (K.cost st p : ℕ)) - w.1.2 + (K.cost st p : ℕ) :=
              nat_sub_spend_left hB hr1
            have hMR : c - w.2.2 = (c - (K.cost st p : ℕ)) - w.2.2 + (K.cost st p : ℕ) :=
              nat_sub_spend_right hC hr2
            refine ⟨?_, ?_⟩
            · rw [hML, hMR]
              exact Nat.add_le_add_right h1 (K.cost st p : ℕ)
            · intro hs
              obtain ⟨h21, h22, h23⟩ := h2 hs
              refine ⟨h21, ?_, ?_⟩
              · rw [h22, nat_sub_budget_diff hB hbc]
              · rw [hMR, hML]
                exact congrArg (fun t : ℕ => t + (K.cost st p : ℕ)) h23
        · exact absurd (le_trans_of_le hB hbc) hC
      · by_cases hC : (K.cost st p : ℕ) ≤ c
        · rw [dif_neg hB, dif_pos hC] at hp
          obtain ⟨o, _, hw'⟩ := (PMF.mem_support_bind_iff _ _ w).mp hp
          cases o with
          | some a =>
            have heq : w = ((none, b), (some a, c - (K.cost st p : ℕ))) :=
              (PMF.mem_support_pure_iff _ _).mp hw'
            subst w
            exact ⟨nat_sub_self_le b c (c - (K.cost st p : ℕ)), fun hs => absurd hs (by simp)⟩
          | none =>
            obtain ⟨r, hr, hw2⟩ := (PMF.mem_support_map_iff _ _ _).mp hw'
            obtain ⟨hr2⟩ := K.run_remaining (c - (K.cost st p : ℕ)) (K.retry st p) r hr
            subst w
            exact ⟨nat_sub_self_le b c r.2, fun hs => absurd hs (by simp)⟩
        · rw [dif_neg hB, dif_neg hC] at hp
          have heq : w = ((none, b), (none, c)) := (PMF.mem_support_pure_iff _ _).mp hp
          subst w
          exact ⟨nat_sub_self_le b c c, fun hs => absurd hs (by simp)⟩
  exact key C B s hBC z hz

/-- Increasing the retry budget cannot decrease the probability of producing a successful output
satisfying any fixed predicate `E`. -/
theorem retry_output_event_budget_mono (K : PlannedRetry State Output) (B C : ℕ) (s : State)
    (E : Output → Prop) (hBC : B ≤ C) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (K.run B s) (fun x => ∃ o, x.1 = some o ∧ E o) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (K.run C s) (fun x => ∃ o, x.1 = some o ∧ E o) := by
  obtain ⟨hleft, hright⟩ := retry_common_prefix_marginals K B C s hBC
  rw [← hleft, ← hright, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hsupp : z ∈ (coupledRetry K B C s).support
  · obtain ⟨_, hz2⟩ := retry_coupled_success_and_spending K B C s hBC z hsupp
    by_cases hs : ∃ o, z.1.1 = some o ∧ E o
    · obtain ⟨o, ho, hE⟩ := hs
      have hne : z.1.1 ≠ none := by rintro hz0; rw [hz0] at ho; simp at ho
      obtain ⟨hz21, _, _⟩ := hz2 hne
      have hs1 : ∃ o, z.1.1 = some o ∧ E o := ⟨o, ho, hE⟩
      have hsnd : ∃ o, z.2.1 = some o ∧ E o := by
        refine ⟨o, ?_, hE⟩
        rw [hz21]
        exact ho
      simp only [hs1, hsnd, if_true]
      exact le_rfl
    · simp only [hs, if_false, mul_zero]
      exact zero_le
  · have hz0 : (coupledRetry K B C s) z = 0 := (PMF.apply_eq_zero_iff _ _).mpr hsupp
    simp only [hz0, zero_mul]
    exact zero_le

/-- For `q ≤ B ≤ C`, the mass of success with output `o` after spending exactly `q` is unchanged
when the initial budget increases from `B` to `C`. -/
theorem run_spend_stable (K : PlannedRetry State Output) : ∀ (B : ℕ) (C : ℕ) (s : State)
    (o : Output) (q : ℕ), B ≤ C → q ≤ B →
      K.run B s (some o, B - q) = K.run C s (some o, C - q) := by
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
    intro C s o q hBC hq
    rw [PlannedRetry.run, PlannedRetry.run, PMF.bind_apply, PMF.bind_apply]
    apply tsum_congr
    intro p
    by_cases hB : (K.cost s p : ℕ) ≤ B
    · by_cases hC : (K.cost s p : ℕ) ≤ C
      · simp only [dif_pos hB, dif_pos hC]
        rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        let f : Option Output → ℝ≥0∞ := fun t => (K.choose s) p *
          ((K.perform s p) t * (match t with
            | some a => PMF.pure (some a, B - (K.cost s p : ℕ))
            | none => K.run (B - (K.cost s p : ℕ)) (K.retry s p)) (some o, B - q))
        let g : Option Output → ℝ≥0∞ := fun t => (K.choose s) p *
          ((K.perform s p) t * (match t with
            | some a => PMF.pure (some a, C - (K.cost s p : ℕ))
            | none => K.run (C - (K.cost s p : ℕ)) (K.retry s p)) (some o, C - q))
        refine tsum_congr (f := f) (g := g) fun t => ?_
        simp only [f, g]
        cases t with
        | some a =>
          by_cases ha : a = o
          · subst a
            by_cases hcq : (K.cost s p : ℕ) = q
            · have hb1 : (some o, B - q) = (some o, B - (K.cost s p : ℕ)) :=
                Prod.ext rfl ((congrArg (fun n : ℕ => B - n) hcq).symm)
              have hb2 : (some o, C - q) = (some o, C - (K.cost s p : ℕ)) :=
                Prod.ext rfl ((congrArg (fun n : ℕ => C - n) hcq).symm)
              simp only [PMF.pure_apply]
              simp [hb1, hb2]
            · have hneB : B - q ≠ B - (K.cost s p : ℕ) := fun hh =>
                hcq ((nat_sub_eq_of_eq (C := B) (r := K.cost s p) (q := q) hB hq hh).symm)
              have hneC : C - q ≠ C - (K.cost s p : ℕ) := fun hh =>
                hcq ((nat_sub_eq_of_eq (C := C) (r := K.cost s p) (q := q)
                  (le_trans hB hBC) (le_trans hq hBC) hh).symm)
              have hb1 : ¬ ((some o, B - q) = (some o, B - (K.cost s p : ℕ))) := by
                intro hh
                exact hneB (congrArg Prod.snd hh)
              have hb2 : ¬ ((some o, C - q) = (some o, C - (K.cost s p : ℕ))) := by
                intro hh
                exact hneC (congrArg Prod.snd hh)
              simp only [PMF.pure_apply]
              simp [hb1, hb2]
          · have hb1 : ¬ ((some o, B - q) = (some a, B - (K.cost s p : ℕ))) := by
              intro hh
              exact ha (Option.some.inj (congrArg Prod.fst hh).symm)
            have hb2 : ¬ ((some o, C - q) = (some a, C - (K.cost s p : ℕ))) := by
              intro hh
              exact ha (Option.some.inj (congrArg Prod.fst hh).symm)
            simp only [PMF.pure_apply]
            simp [hb1, hb2]
        | none =>
          by_cases hqc : (K.cost s p : ℕ) ≤ q
          · have hqsub : q - (K.cost s p : ℕ) ≤ B - (K.cost s p : ℕ) :=
              nat_sub_mono_le (B := q) (C := B) (k := K.cost s p) hq
            have hBq : B - q = (B - (K.cost s p : ℕ)) - (q - (K.cost s p : ℕ)) :=
              nat_sub_sub_add hq hqc
            have hCq : C - q = (C - (K.cost s p : ℕ)) - (q - (K.cost s p : ℕ)) :=
              nat_sub_sub_add (le_trans hq hBC) hqc
            show (K.choose s) p *
                ((K.perform s p) none *
                  (K.run (B - (K.cost s p : ℕ)) (K.retry s p) (some o, B - q))) = _
            rw [hBq, hCq]
            exact congrArg (fun t : ℝ≥0∞ => (K.choose s) p * ((K.perform s p) none * t))
              (ih (B - (K.cost s p : ℕ)) (nat_sub_lt_budget (K.cost s p).pos hB)
                (C - (K.cost s p : ℕ)) (K.retry s p) o (q - (K.cost s p : ℕ))
                (nat_sub_mono_le hBC) hqsub)
          · have hcost : q < (K.cost s p : ℕ) := Nat.lt_of_not_ge hqc
            have hltB : B - (K.cost s p : ℕ) < B - q := nat_sub_lt_sub hB hcost
            have hltC : C - (K.cost s p : ℕ) < C - q := nat_sub_lt_sub hC hcost
            simp only [run_success_eq_zero_of_bgt _ _ _ o _ hltB,
              run_success_eq_zero_of_bgt _ _ _ o _ hltC, mul_zero]
      · exact absurd (le_trans_of_le hB hBC) hC
    · have hcostq : q < (K.cost s p : ℕ) := by
        by_contra hcon
        exact hB (Nat.le_trans (Nat.not_lt.mp hcon) hq)
      simp only [dif_neg hB]
      have hne : ¬ ((some o, B - q) = (none, B)) := by simp
      rw [PMF.pure_apply, if_neg hne, mul_zero]
      by_cases hC : (K.cost s p : ℕ) ≤ C
      · simp only [dif_pos hC, PMF.bind_apply]
        rw [← ENNReal.tsum_mul_left]
        symm
        rw [ENNReal.tsum_eq_zero]
        intro t
        cases t with
        | some a =>
          by_cases ha : a = o
          · subst a
            have hneC : ¬ ((some o, C - q) = (some o, C - (K.cost s p : ℕ))) := by
              intro hh
              exact hB (((nat_sub_eq_of_eq (C := C) (r := K.cost s p) (q := q) hC
                (le_trans hq hBC) (congrArg Prod.snd hh)) ▸ hq))
            have hneC : ¬ ((some o, C - q) = (some o, C - (K.cost s p : ℕ))) := by
              intro hh
              exact hB (((nat_sub_eq_of_eq (C := C) (r := K.cost s p) (q := q) hC
                (le_trans hq hBC) (congrArg Prod.snd hh)) ▸ hq))
            rw [PMF.pure_apply, if_neg hneC, mul_zero, mul_zero]
          · have hneB : ¬ ((some o, C - q) = (some a, C - (K.cost s p : ℕ))) := by
              intro hh
              exact ha (Option.some.inj (congrArg Prod.fst hh).symm)
            rw [PMF.pure_apply, if_neg hneB, mul_zero, mul_zero]
        | none =>
          have hltC : C - (K.cost s p : ℕ) < C - q := nat_sub_lt_sub hC hcostq
          simp only [run_success_eq_zero_of_bgt _ _ _ o _ hltC, mul_zero, mul_zero]
      · simp only [dif_neg hC]
        have hneC : ¬ ((some o, C - q) = (none, C)) := by simp
        rw [PMF.pure_apply, if_neg hneC, mul_zero]

/-- For `q ≤ B ≤ C`, the costed retry laws at budgets `B` and `C` assign the same mass to the
successful result `(some o, q)`. -/
theorem retry_success_law_same_spent_prefix (K : PlannedRetry State Output) (B C : ℕ) (s : State)
    (o : Output) (q : ℕ) (hBC : B ≤ C) (hq : q ≤ B) :
    (K.costedRun B s) (some o, q) = (K.costedRun C s) (some o, q) :=
  (costedRun_apply K B s o q hq).trans
    ((run_spend_stable K B C s o q hBC hq).trans
      (costedRun_apply K C s o q (le_trans hq hBC)).symm)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
