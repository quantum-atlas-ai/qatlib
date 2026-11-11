/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.Execution
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Composition

/-!
# Failure laws for fresh repeated trials

`freshBatch` repeats a trial using fresh probabilistic branches, stores all traces, and retains
the smallest output rank. The batch failure indicator factors under combination, yielding an
exact power law for failure probability and its dyadic bound.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `actual_failure_power`: The probability that `k` fresh trials fail to produce best output zero
  is the `k`th power of the single-trial failure probability.
* `actual_failure_le_half_power`: If a trial fails with probability at most `1/2`, then `k`
  fresh trials fail with probability at most `(1/2)^k`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.FreshRepeat
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess

/-- A batch of trial traces with an optional best output rank and accumulated paid charge. -/
structure Batch where
  best : Option ℕ
  totalPaid : ℕ
  runs : List Trace

/-- Adds a trace to a batch, sums its charge, and retains the minimum of its output and the
existing best rank. -/
def combine (tr : Trace) (b : Batch) : Batch :=
  ⟨match b.best with | none => some tr.output | some j => some (min tr.output j),
    paid tr+b.totalPaid,tr::b.runs⟩

/-- Runs `k` fresh copies of a trial and combines their outputs, charges, and traces into a
batch. -/
def freshBatch (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace) :
    ℕ → Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Batch
  | 0 => .pure ⟨none,0,[]⟩
  | k+1 => trial.bind (fun tr => (freshBatch trial k).map (combine tr))

/-- The indicator that a trial output is not rank zero. -/
def trialFailure (tr : Trace) : ℝ := if tr.output=0 then 0 else 1

/-- The indicator that the batch best output is not `some 0`. -/
def batchFailure (b : Batch) : ℝ := if b.best=some 0 then 0 else 1

/-- The failure indicator after combining a trace and a batch is the product of their failure
indicators. -/
theorem combine_failure_indicator (tr : Trace) (b : Batch) :
    batchFailure (combine tr b)=trialFailure tr*batchFailure b := by
  cases hb : b.best with
  | none => simp [combine,batchFailure,trialFailure,hb]
  | some j =>
    by_cases ht : tr.output=0 <;> by_cases hj : j=0 <;>
      simp [combine,batchFailure,trialFailure,hb,ht,hj]

/-- The mean failure indicator of `k` fresh trials is the `k`th power of the single-trial mean
failure indicator. -/
theorem failure_moment_power (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace)
    (k : ℕ) :
    (freshBatch trial k).mean batchFailure=(trial.mean trialFailure)^k := by
  induction k with
  | zero => simp [freshBatch,Tree.mean,batchFailure]
  | succ k ih =>
    rw [freshBatch,Tree.mean_bind]
    simp_rw [Tree.mean_map,combine_failure_indicator,Tree.mean_mul,ih]
    have h : (fun tr => trialFailure tr*(trial.mean trialFailure)^k) =
        (fun tr => (trial.mean trialFailure)^k*trialFailure tr) := by funext tr; ring
    rw [h,Tree.mean_mul]
    exact (pow_succ _ k).symm

/-- The probability of a nonzero trial output equals the mean trial failure indicator. -/
theorem trial_failure_probability (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace) :
    trial.probability (fun tr => tr.output≠0)=trial.mean trialFailure := by
  apply Tree.mean_congr
  apply Tree.all_of_forall
  intro tr
  by_cases h : tr.output=0 <;> simp [trialFailure,h]

/-- The probability that a batch lacks best output `some 0` equals the mean batch failure
indicator. -/
theorem batch_failure_probability (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Batch) :
    t.probability (fun b => b.best≠some 0)=t.mean batchFailure := by
  apply Tree.mean_congr
  apply Tree.all_of_forall
  intro b
  by_cases h : b.best=some 0 <;> simp [batchFailure,h]

/-- The probability that `k` fresh trials fail to produce best output zero is the `k`th power of
the single-trial failure probability. -/
theorem actual_failure_power (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace)
    (k : ℕ) :
    (freshBatch trial k).probability (fun b => b.best≠some 0)=
      (trial.probability (fun tr => tr.output≠0))^k := by
  rw [batch_failure_probability,trial_failure_probability,failure_moment_power]

/-- If a trial fails with probability at most `1/2`, then `k` fresh trials fail with probability
at most `(1/2)^k`. -/
theorem actual_failure_le_half_power
    (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace)
    (htrial : trial.probability (fun tr => tr.output≠0)≤1/2) (k : ℕ) :
    (freshBatch trial k).probability (fun b => b.best≠some 0)≤(1/2:ℝ)^k := by
  rw [actual_failure_power]
  apply pow_le_pow_left₀ _ htrial
  apply Tree.mean_nonneg
  apply Tree.all_of_forall
  intro tr
  split_ifs <;> norm_num
end Qatlib.Papers.QAOAScaling23.FreshRepeat
