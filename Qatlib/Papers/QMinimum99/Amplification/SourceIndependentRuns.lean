/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockMinimumExecutor
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua

set_option backward.isDefEq.respectTransparency false

/-!
# Independent runs at the original source deadline

Each run is the actual source-clock executor at its printed timeout. The
accumulator starts with the first returned index, not a fixed index zero.
The recursive argument counts extra runs: zero means one genuine run.
Strict comparison then selects the best of exactly c+1 independent outputs.
This proves the first amplification guarantee in quant-ph/9607014v2, p.2.
It does not assert that one longer run dominates independent repetitions.
-/

set_option autoImplicit false
open scoped Classical ENNReal BigOperators
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification

namespace Qatlib.Papers.QMinimum99.Amplification

/-- One actual finite source execution, with the original printed deadline. -/
noncomputable def sourceSingleRun {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) : PMF (Fin N) :=
  Qatlib.Concepts.AmplitudeSearch.InterruptMin.sourceInitialPMF T hN (sourceTimeout N)

/-- Select the better of two independent genuine output laws, with no extra seed. -/
noncomputable def sourceCombineRuns {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (p q : PMF (Fin N)) : PMF (Fin N) :=
  p.bind fun a => q.bind fun b => PMF.pure (amplifiedCombine T a b)

/-- The literal best of c+1 actual independent executions at the source timeout. -/
noncomputable def sourceRepeatedRuns {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) : ℕ → PMF (Fin N)
  | 0 => sourceSingleRun T hN
  | c+1 => sourceCombineRuns T (sourceRepeatedRuns T hN c) (sourceSingleRun T hN)

/-- Any predicate and its complement partition a normalized probability law. -/
theorem source_event_total {β : Type*} (p : PMF β) (E : β → Prop) :
    event p E + event p (fun x => ¬ E x) = 1 := by
  unfold event
  rw [← expectation_add]
  calc
    _ = expectation p (fun _ => 1) := by
      congr 1
      funext x
      by_cases hx : E x <;> simp [hx]
    _ = 1 := expectation_const p 1

/-- Event masses are finite and bounded by one. -/
theorem source_event_le_one {β : Type*} (p : PMF β) (E : β → Prop) :
    event p E ≤ 1 := by
  calc
    _ ≤ event p E + event p (fun x => ¬ E x) := le_self_add
    _ = 1 := source_event_total p E

/-- Two independent runs both have to fail for their actual minimum-fold to fail. -/
theorem sourceCombine_failure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (p q : PMF (Fin N)) :
    event (sourceCombineRuns T p q) (fun i => ¬ ∀ j, T i ≤ T j) =
      event p (fun i => ¬ ∀ j, T i ≤ T j) *
      event q (fun i => ¬ ∀ j, T i ≤ T j) := by
  unfold sourceCombineRuns event
  rw [expectation_bind]
  simp only [expectation_bind, expectation_pure, amplifiedCombine_minimum_iff, not_or]
  have he (a : Fin N) :
      expectation q (fun b => if (¬ ∀ j, T a ≤ T j) ∧ (¬ ∀ j, T b ≤ T j) then 1 else 0) =
      (if (¬ ∀ j, T a ≤ T j) then (1 : ℝ≥0∞) else 0) *
        expectation q (fun b => if (¬ ∀ j, T b ≤ T j) then 1 else 0) := by
    by_cases ha : ∀ j, T a ≤ T j <;> simp [ha]
  simp_rw [he]
  unfold expectation
  rw [← ENNReal.tsum_mul_right]
  congr 1
  funext a
  by_cases ha : ∀ j, T a ≤ T j <;> simp [ha]

/-- The original source half-success theorem bounds the same actual run's failure. -/
theorem sourceSingle_failure_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    event (sourceSingleRun T hN) (fun i => ¬ ∀ j, T i ≤ T j) ≤ (1/2 : ℝ≥0∞) := by
  let p := sourceSingleRun T hN
  let E : Fin N → Prop := fun i => ∀ j, T i ≤ T j
  have hsne : event p E ≠ ∞ := ne_of_lt ((source_event_le_one p E).trans_lt (by simp))
  have hfne : event p (fun i => ¬ E i) ≠ ∞ :=
    ne_of_lt ((source_event_le_one p (fun i => ¬ E i)).trans_lt (by simp))
  have htotal := congrArg ENNReal.toReal (source_event_total p E)
  rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at htotal
  have heq : (event p E).toReal = Qatlib.Concepts.AmplitudeSearch.InterruptMin.sourceSuccess
      T hN (sourceTimeout N) := by
    unfold Qatlib.Concepts.AmplitudeSearch.InterruptMin.sourceSuccess
    rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.sourceInitialEval_eq_expectation]
    congr 1
    unfold event expectation Qatlib.Concepts.AmplitudeSearch.InterruptMin.expectation
    apply tsum_congr
    intro i
    by_cases hi : ∀ j, T i ≤ T j <;> simp [p, E, sourceSingleRun, hi]
  have hhalf : (1/2 : ℝ) ≤ (event p E).toReal := by
    rw [heq]
    exact Qatlib.Concepts.AmplitudeSearch.InterruptMin.source_timeout_half T hN

  apply (ENNReal.toReal_le_toReal hfne (by norm_num)).mp
  norm_num
  linarith

/-- The literal c+1 independent source runs have geometric failure mass. -/
theorem sourceRepeated_failure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    event (sourceRepeatedRuns T hN c) (fun i => ¬ ∀ j, T i ≤ T j) ≤
      (1/2 : ℝ≥0∞)^(c+1) := by
  induction c with
  | zero => simpa [sourceRepeatedRuns] using sourceSingle_failure_half T hN
  | succ c ih =>
    rw [sourceRepeatedRuns, sourceCombine_failure, pow_succ]
    exact mul_le_mul' ih (sourceSingle_failure_half T hN)

/-- Exactly c+1 fresh source-timeout runs return a minimum with mass at least
1-2^(-(c+1)); no fixed unobserved candidate is added to those outputs. -/
theorem sourceRepeated_success {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    ENNReal.ofReal (1-(1/2 : ℝ)^(c+1)) ≤
      event (sourceRepeatedRuns T hN c) (fun i => ∀ j, T i ≤ T j) := by
  let p := sourceRepeatedRuns T hN c
  let E : Fin N → Prop := fun i => ∀ j, T i ≤ T j
  have hsne : event p E ≠ ∞ := ne_of_lt ((source_event_le_one p E).trans_lt (by simp))
  have hfne : event p (fun i => ¬ E i) ≠ ∞ :=
    ne_of_lt ((source_event_le_one p (fun i => ¬ E i)).trans_lt (by simp))
  have htotal := congrArg ENNReal.toReal (source_event_total p E)
  rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at htotal
  have hfailure := (ENNReal.toReal_le_toReal hfne (by finiteness)).mpr
    (sourceRepeated_failure T hN c)
  rw [ENNReal.toReal_pow] at hfailure
  norm_num at hfailure
  have hs : 1-(1/2 : ℝ)^(c+1) ≤ (event p E).toReal := by linarith
  have h := ENNReal.ofReal_le_ofReal hs
  rwa [ENNReal.ofReal_toReal hsne] at h

/-- The source's positive number c of repetitions, starting from a genuine
first output and selecting only among the c returned indices. -/
noncomputable def sourceIndependentRuns {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (_hc : 0 < c) : PMF (Fin N) :=
  sourceRepeatedRuns T hN (c-1)

/-- At the exact printed timeout per run, the literal c-fold strategy has
success at least 1-2^(-c), including tables with repeated values. -/
theorem sourceIndependent_success {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    ENNReal.ofReal (1-(1/2 : ℝ)^c) ≤
      event (sourceIndependentRuns T hN c hc) (fun i => ∀ j, T i ≤ T j) := by
  have h := sourceRepeated_success T hN (c-1)
  simpa only [sourceIndependentRuns, Nat.sub_add_cancel hc] using h

end Qatlib.Papers.QMinimum99.Amplification
