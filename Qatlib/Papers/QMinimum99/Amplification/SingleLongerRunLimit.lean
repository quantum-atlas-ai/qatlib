/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMinimum99.Amplification.InfiniteAlgorithmLimit
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds

set_option backward.isDefEq.respectTransparency false

/-!
# QMinimum99 — the single longer run at the source's own `c · 2 m₀` timeout

Source: arXiv quant-ph/9607014v2, §3 "Final remarks", p. 2 col. 1:

> "The probability of success can be improved by running the algorithm `c`
> times. [...] Clearly, the probability of success is even better if we run
> the algorithm only once with time-out `c 2 m₀`, because then we use the
> information provided by the previous steps."

The frozen layer proves the `c`-fold bound only for the **charged** clock
(`charged_initial_success_amplified`, budget `c · chargedBudget N`), where the
deadline is four times the source's and the constants are the corrected ones.
The paper's own sentence is about the **source's** clock and the source's
printed timeout `2 m₀`, and it is about *one* uninterrupted execution.

This module supplies a single-run lower bound and within-run monotonicity on the source clock:

* `single_longer_run_attainment_amplified` / `single_longer_run_success_amplified`
  — one uninterrupted source-clock execution with timeout `c · (2 m₀)` returns
  a minimum with probability at least `1 - 1/(2c)`, directly from Lemma 2's
  mean and the same-path Markov step of
  `InfiniteAlgorithmLimit.attainmentDefect_le`;
* `single_longer_run_keeps_shorter_attainment` /
  `single_longer_run_covers_every_shorter_deadline` — the second half of the
  source's reason: because the threshold is only ever replaced by a strictly
  smaller value, a longer timeout keeps every attainment the shorter one had
  already reached.  This within-run property does not compare with a minimum-fold over independent
  repetitions, whose accumulator also retains its best observed output.

The *comparison* between this bound and the `1 - 2^{-c}` bound of `c`
independent repetitions is not decided by the two bounds for `c ≥ 3`; the
frozen `MinimumRuntimeNext` module records that obstruction.  What is added
here is the missing source-clock side of the comparison and the monotone
mechanism the paper names.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QMinimum99.Amplification

open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped BigOperators ENNReal

variable {N : ℕ} {α : Type} [LinearOrder α]

/-- The source's own single-longer-run deadline: `c` times the printed timeout
`2 m₀`, i.e. the `c 2 m₀` of the final remarks. -/
noncomputable def sourceLongerRunTimeout (N c : ℕ) : ℝ := (c : ℝ) * sourceTimeout N

/-- At the `c`-fold printed timeout the source's mean budget is a `1/(2c)`
fraction of the deadline: `m₀ / (c · 2 m₀) = 1/(2c)`. -/
theorem sourceLongerRun_ratio (N c : ℕ) (hN : 0 < N) (hc : 0 < c) :
    sourceMeanBudget N / sourceLongerRunTimeout N c = 1 / ((2 * c : ℕ) : ℝ) := by
  have hm0 : 0 < sourceMeanBudget N := sourceMeanBudget_pos N hN
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hcast : ((2 * c : ℕ) : ℝ) = 2 * (c : ℝ) := by push_cast; ring
  rw [hcast, sourceLongerRunTimeout, sourceTimeout_eq_twice]
  field_simp

/-- **The single longer run on the source clock.**  One uninterrupted
source-clock execution with timeout `c · 2 m₀` attains a minimum within that
deadline with probability at least `1 - 1/(2c)`.  This is Lemma 2's mean turned
into a probability by the same-path Markov step, exactly as in the paper's
`2 m₀` case (`c = 1`). -/
theorem single_longer_run_attainment_amplified (T : Fin N → α) (hN : 0 < N)
    (c : ℕ) (hc : 0 < c) :
    1 - 1 / ((2 * c : ℕ) : ℝ) ≤ clause40AttainmentMass T hN (sourceLongerRunTimeout N c) := by
  have hm0 : 0 < sourceMeanBudget N := sourceMeanBudget_pos N hN
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hT : 0 < sourceTimeout N := by
    rw [sourceTimeout_eq_twice]
    positivity
  have ht : 0 < sourceLongerRunTimeout N c := by
    unfold sourceLongerRunTimeout
    positivity
  have hdef := attainmentDefect_le T hN ht
  have hratio := sourceLongerRun_ratio N c hN hc
  unfold attainmentDefect at hdef
  linarith

/-- **The single longer run, on the actual executor.**  The frozen source-clock
executor run with the `c`-fold printed timeout returns a true minimum with
probability at least `1 - 1/(2c)`: the attainment mass is dominated by the
executor's return event. -/
theorem single_longer_run_success_amplified (T : Fin N → α) (hN : 0 < N)
    (c : ℕ) (hc : 0 < c) :
    1 - 1 / ((2 * c : ℕ) : ℝ) ≤ sourceSuccess T hN (sourceLongerRunTimeout N c) :=
  (single_longer_run_attainment_amplified T hN c hc).trans
    (source_attainment_le_success T hN (sourceLongerRunTimeout N c))

/-- **Information reuse: the longer single run keeps every earlier attainment.**
For any shorter deadline `d` the attainment mass is no larger than the
attainment at the `c`-fold printed timeout: extending the timeout of the same
run never discards progress, because the threshold is replaced only by a
strictly smaller value. -/
theorem single_longer_run_keeps_shorter_attainment (T : Fin N → α) (hN : 0 < N)
    (c : ℕ) {d : ℝ} (hd : d ≤ sourceLongerRunTimeout N c) :
    clause40AttainmentMass T hN d ≤ clause40AttainmentMass T hN (sourceLongerRunTimeout N c) :=
  attainmentMass_monotone T hN hd

/-- **The longer single run covers every shorter deadline at the executor.**
The actual source-clock executor with the `c`-fold printed timeout returns a
minimum with probability at least the attainment mass any shorter deadline had
already reached: the longer run dominates all its prefixes. -/
theorem single_longer_run_covers_every_shorter_deadline (T : Fin N → α) (hN : 0 < N)
    (c : ℕ) {d : ℝ} (hd : d ≤ sourceLongerRunTimeout N c) :
    clause40AttainmentMass T hN d ≤ sourceSuccess T hN (sourceLongerRunTimeout N c) :=
  (single_longer_run_keeps_shorter_attainment T hN c hd).trans
    (source_attainment_le_success T hN (sourceLongerRunTimeout N c))

/-- At the printed (unmultiplied) timeout the `c = 1` case recovers the paper's
`2 m₀` deadline. -/
theorem sourceLongerRunTimeout_one (N : ℕ) :
    sourceLongerRunTimeout N 1 = sourceTimeout N := by
  unfold sourceLongerRunTimeout
  push_cast
  ring

/-- The `c = 1` case of the amplified bound is the source's own Theorem 1
deadline statement: one run at `2 m₀` attains with probability at least `1/2`. -/
theorem single_run_at_printed_timeout_attainment_half (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ clause40AttainmentMass T hN (sourceTimeout N) := by
  have h := single_longer_run_attainment_amplified T hN 1 (by norm_num)
  rw [sourceLongerRunTimeout_one] at h
  norm_num at h
  exact h

end Qatlib.Papers.QMinimum99.Amplification
