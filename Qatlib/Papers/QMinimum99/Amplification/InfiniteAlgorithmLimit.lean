/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockMinimumExecutor
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Archimedean

set_option backward.isDefEq.respectTransparency false

/-!
# QMinimum99 — the paper's infinite algorithm as the limit of finite executions

Source: arXiv quant-ph/9607014v2 (watermark 7 January 1999, body July 1996),
§2 "The algorithm", p. 1 col. 2: *"For the analysis of the probability of
success, assume that there is no time-out, that is, the algorithm runs long
enough to find the minimum. We refer to this as the **infinite algorithm**."*
The paper then analyses this infinite algorithm (Lemma 1, Lemma 2) and only at
the very end passes to the finite run of Theorem 1 by the Markov step
*"after at most `2 m₀` iterations, `T[y]` holds the minimum value with
probability at least `1/2`"*.

The frozen layer already proves the source-clock finite executor's half-success
bound, as well as the actual BBHT run law and source-clock moment. This module
makes the monotone finite-deadline attainment limit and truncated-mean relation
explicit. It does not construct a different physical infinite wallclock machine.

The finite level is `clause40AttainmentMass T hN d`: the source-clock mass of the
complete runs that already hold a genuine minimum of the table within the real
deadline `d`.  Its complement `attainmentDefect T hN d` is the mass of the runs
the infinite algorithm has **not** finished by time `d`, i.e. the
never-yet-attained mass of the paper's abstraction.  The results below show

* the deadline is monotone — a longer single run keeps every attainment the
  shorter run already had (the source's "information provided by the previous
  steps");
* the never-yet-attained mass at `d` is at most `m₀ / d` (Lemma 2's mean plus
  the same-path Markov step), hence tends to `0`: the infinite algorithm
  attains a minimum almost surely;
* the finite source-clock executors (`sourceSuccess`) therefore achieve success
  arbitrarily close to `1`, at a truncated expected clock never exceeding
  `m₀ = (45/4)√N + (7/10)lg²N`.

Nothing here is an extra axiom: every ingredient is the frozen Lemma 2 moment,
the frozen normalized run law, and the frozen domination of attainment by the
executor's return event.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QMinimum99.Amplification

open Filter
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped BigOperators ENNReal

variable {N : ℕ} {α : Type} [LinearOrder α]

/-- The mass the paper's **infinite algorithm** has not yet finished by time
`d`: one minus the finite source-clock attainment mass of the frozen layer. -/
noncomputable def attainmentDefect (T : Fin N → α) (hN : 0 < N) (d : ℝ) : ℝ :=
  1 - clause40AttainmentMass T hN d

/-- The cutoff sub-mass of the source run law at deadline `d` is summable: it is
pointwise dominated by the normalized initial-threshold mass. -/
theorem attainmentCutoff_summable (T : Fin N → α) (hN : 0 < N) (d : ℝ) :
    Summable (fun x : Fin N × List (SearchTrace N) =>
      if (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).runClock x.2 ≤ d then
        (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).initialMass
          (SortedRankedTable.ofTable T).skip x else 0) := by
  set ranked := SortedRankedTable.ofTable T with hranked
  set law := sourceBBHTLaw ranked.indexOfRank hN with hlaw
  have hm := (law.initialMass_normalized ranked.skip hN).1
  have hnn := (law.initialMass_normalized ranked.skip hN).2
  have h0 : ∀ x : Fin N × List (SearchTrace N),
      0 ≤ (if law.runClock x.2 ≤ d then law.initialMass ranked.skip x else 0) := by
    intro x
    classical
    split_ifs with h
    · exact hnn x
    · exact le_rfl
  have hle : ∀ x : Fin N × List (SearchTrace N),
      (if law.runClock x.2 ≤ d then law.initialMass ranked.skip x else 0) ≤
        law.initialMass ranked.skip x := by
    intro x
    classical
    split_ifs with h
    · exact le_rfl
    · exact hnn x
  exact Summable.of_nonneg_of_le h0 hle hm.summable

/-- **Deadline monotonicity (the source's information reuse).**  For the same
single run, enlarging the deadline never loses attainment mass: every run that
had already reached a minimum within the shorter deadline is still counted.
This is the formal content of the source's remark that a longer run "uses the
information provided by the previous steps", whereas independent repetitions
restart from the uniform threshold. -/
theorem attainmentMass_monotone (T : Fin N → α) (hN : 0 < N) :
    Monotone (fun d : ℝ => clause40AttainmentMass T hN d) := by
  intro d₁ d₂ hd
  set ranked := SortedRankedTable.ofTable T with hranked
  set law := sourceBBHTLaw ranked.indexOfRank hN with hlaw
  have hnn := (law.initialMass_normalized ranked.skip hN).2
  have hs₁ := attainmentCutoff_summable T hN d₁
  have hs₂ := attainmentCutoff_summable T hN d₂
  change (∑' x : Fin N × List (SearchTrace N),
      if law.runClock x.2 ≤ d₁ then law.initialMass ranked.skip x else 0) ≤
    (∑' x : Fin N × List (SearchTrace N),
      if law.runClock x.2 ≤ d₂ then law.initialMass ranked.skip x else 0)
  refine Summable.tsum_le_tsum (fun x => ?_) hs₁ hs₂
  by_cases h1 : law.runClock x.2 ≤ d₁
  · rw [if_pos h1, if_pos (h1.trans hd)]
  · rw [if_neg h1]
    by_cases h2 : law.runClock x.2 ≤ d₂
    · rw [if_pos h2]
      exact hnn x
    · rw [if_neg h2]

/-- The finite attainment mass never exceeds one: it is a sub-mass of the
normalized initial-threshold law. -/
theorem attainmentMass_le_one (T : Fin N → α) (hN : 0 < N) (d : ℝ) :
    clause40AttainmentMass T hN d ≤ 1 := by
  set ranked := SortedRankedTable.ofTable T with hranked
  set law := sourceBBHTLaw ranked.indexOfRank hN with hlaw
  have hm := (law.initialMass_normalized ranked.skip hN).1
  have hnn := (law.initialMass_normalized ranked.skip hN).2
  have hs := attainmentCutoff_summable T hN d
  change (∑' x : Fin N × List (SearchTrace N),
      if law.runClock x.2 ≤ d then law.initialMass ranked.skip x else 0) ≤ 1
  calc (∑' x : Fin N × List (SearchTrace N),
      if law.runClock x.2 ≤ d then law.initialMass ranked.skip x else 0)
      ≤ ∑' x : Fin N × List (SearchTrace N), law.initialMass ranked.skip x := by
        refine Summable.tsum_le_tsum (fun x => ?_) hs hm.summable
        split_ifs with h
        · exact le_rfl
        · exact hnn x
    _ = 1 := hm.tsum_eq

/-- **The Markov step on the source's own clock (Lemma 2's mean).**  The mass
of the runs the infinite algorithm has not finished by time `t` is at most
`m₀ / t`: by the frozen Lemma 2 moment, the mean source-clock time to hold a
minimum is at most `m₀ = (45/4)√N + (7/10)lg²N`, and the frozen cutoff contract
turns a mean into a same-path cutoff. -/
theorem attainmentDefect_le (T : Fin N → α) (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    attainmentDefect T hN t ≤ sourceMeanBudget N / t := by
  set ranked := SortedRankedTable.ofTable T with hranked
  set law := sourceBBHTLaw ranked.indexOfRank hN with hlaw
  have hm := (law.initialMass_normalized ranked.skip hN).1
  have hnn := (law.initialMass_normalized ranked.skip hN).2
  obtain ⟨q, hq, hq0, hqb⟩ := bbht_source_attainment_moment ranked hN
  obtain ⟨p, hp, hgood, _⟩ := amplification_clock_mass (law.initialMass ranked.skip)
    (fun x : Fin N × List (SearchTrace N) => law.runClock x.2) hm hnn
    (fun x => law.runClock_nonneg x.2) q t hq ht
  have hpmass : p = clause40AttainmentMass T hN t := by
    rw [← hp.tsum_eq]
    simp only [clause40AttainmentMass, clause40AttainmentMassOn, clause40SourceLaw, clause40SourceSkip,
      ← hranked, ← hlaw]
  have hle : q / t ≤ sourceMeanBudget N / t :=
    div_le_div_of_nonneg_right hqb ht.le
  unfold attainmentDefect
  rw [hpmass] at hgood
  linarith

/-- The attainment defect at integer deadlines is nonnegative: the finite
attainment mass is at most one. -/
theorem attainmentDefect_nonneg (T : Fin N → α) (hN : 0 < N) (d : ℕ) :
    0 ≤ attainmentDefect T hN ((d : ℝ) + 1) :=
  sub_nonneg.mpr (attainmentMass_le_one T hN _)

/-- The mean budget divided by the shifting integer deadline tends to zero. -/
theorem sourceMeanBudget_div_add_one_tendsto_zero (N : ℕ) :
    Tendsto (fun d : ℕ => sourceMeanBudget N / ((d : ℝ) + 1)) atTop (nhds 0) := by
  have hden : Tendsto (fun d : ℕ => ((d : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun d => by linarith)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_const_nhds.div_atTop hden

/-- **The infinite algorithm attains a minimum almost surely.**  Its
never-yet-attained mass at deadline `d + 1` is at most `m₀ / (d + 1)`, so for
every `ε > 0` some finite deadline leaves less than `ε` mass unattained. -/
theorem infinite_attains_almost_surely (T : Fin N → α) (hN : 0 < N) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 1 - ε ≤ clause40AttainmentMass T hN ((D : ℝ) + 1) := by
  intro ε hε
  have hlim := sourceMeanBudget_div_add_one_tendsto_zero N
  have hm0 : 0 ≤ sourceMeanBudget N := (sourceMeanBudget_pos N hN).le
  obtain ⟨D, hD⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨D, ?_⟩
  have hlt : sourceMeanBudget N / ((D : ℝ) + 1) < ε := by
    have h := hD D le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hm0 (by positivity))] at h
    exact h
  have hbound := attainmentDefect_le T hN (by positivity : (0:ℝ) < (D:ℝ) + 1)
  unfold attainmentDefect at hbound
  linarith

/-- **The infinite algorithm's never-mass is zero.**  Stated as a limit of the
finite defects: the mass the infinite algorithm has not yet finished vanishes
along the deadlines. -/
theorem attainmentDefect_tendsto_zero (T : Fin N → α) (hN : 0 < N) :
    Tendsto (fun d : ℕ => attainmentDefect T hN ((d : ℝ) + 1)) atTop (nhds 0) :=
  squeeze_zero (fun d => attainmentDefect_nonneg T hN d)
    (fun d => attainmentDefect_le T hN (by positivity))
    (sourceMeanBudget_div_add_one_tendsto_zero N)

/-- **The finite attainment masses converge to the infinite algorithm.**  The
finite-level attainment mass tends to `1` along the deadlines. -/
theorem attainmentMass_tendsto_one (T : Fin N → α) (hN : 0 < N) :
    Tendsto (fun d : ℕ => clause40AttainmentMass T hN ((d : ℝ) + 1)) atTop (nhds 1) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub (attainmentDefect_tendsto_zero T hN)
  have h' : Tendsto (fun d : ℕ => 1 - attainmentDefect T hN ((d : ℝ) + 1)) atTop
      (nhds (1 - 0)) := h
  simpa [attainmentDefect] using h'

/-- **The finite source-clock executors approach the infinite algorithm.**  The
actual executor of the frozen layer returns a minimum with probability
arbitrarily close to one once the source-clock deadline is long enough: the
attainment mass is dominated by the executor's return event, and it tends to
one. -/
theorem executor_success_approaches_one (T : Fin N → α) (hN : 0 < N) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 1 - ε ≤ sourceSuccess T hN ((D : ℝ) + 1) := by
  intro ε hε
  obtain ⟨D, hD⟩ := infinite_attains_almost_surely T hN ε hε
  exact ⟨D, hD.trans (source_attainment_le_success T hN _)⟩

/-- The expected source clock of the finite executions up to `d`: the mean of
the attainment time truncated at the deadline. -/
noncomputable def truncatedAttainmentMean (T : Fin N → α) (hN : 0 < N) (d : ℕ) : ℝ :=
  ∑' x : Fin N × List (SearchTrace N),
    (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).initialMass
        (SortedRankedTable.ofTable T).skip x *
      min ((sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).runClock x.2) (d : ℝ)

/-- Every truncated attainment mean is nonnegative. -/
theorem truncatedAttainmentMean_nonneg (T : Fin N → α) (hN : 0 < N) (d : ℕ) :
    0 ≤ truncatedAttainmentMean T hN d := by
  unfold truncatedAttainmentMean
  refine tsum_nonneg (fun x => ?_)
  exact mul_nonneg (((sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).initialMass_normalized
    (SortedRankedTable.ofTable T).skip hN).2 x)
    (le_min ((sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).runClock_nonneg x.2)
      (Nat.cast_nonneg d))

/-- **Truncating the clock cannot increase the expected time.**  The finite
executions cut at any deadline keep an expected truncated clock bounded by
Lemma 2's `m₀`, so replacing the paper's infinite algorithm by finite
executions costs no expected time. -/
theorem truncatedAttainmentMean_le_sourceMeanBudget (T : Fin N → α) (hN : 0 < N) (d : ℕ) :
    truncatedAttainmentMean T hN d ≤ sourceMeanBudget N := by
  set ranked := SortedRankedTable.ofTable T with hranked
  set law := sourceBBHTLaw ranked.indexOfRank hN with hlaw
  obtain ⟨q, hq, hq0, hqb⟩ := bbht_source_attainment_moment ranked hN
  have hnn := (law.initialMass_normalized ranked.skip hN).2
  have hclock := fun x : Fin N × List (SearchTrace N) => law.runClock_nonneg x.2
  have hle : (fun x : Fin N × List (SearchTrace N) =>
      law.initialMass ranked.skip x * min (law.runClock x.2) (d : ℝ)) ≤
      (fun x : Fin N × List (SearchTrace N) => law.initialMass ranked.skip x * law.runClock x.2) :=
    fun x => mul_le_mul_of_nonneg_left (min_le_left _ _) (hnn x)
  have hs : Summable (fun x : Fin N × List (SearchTrace N) =>
      law.initialMass ranked.skip x * min (law.runClock x.2) (d : ℝ)) :=
    Summable.of_nonneg_of_le
      (f := fun x : Fin N × List (SearchTrace N) => law.initialMass ranked.skip x * law.runClock x.2)
      (g := fun x : Fin N × List (SearchTrace N) =>
        law.initialMass ranked.skip x * min (law.runClock x.2) (d : ℝ))
      (fun x => mul_nonneg (hnn x) (le_min (hclock x) (Nat.cast_nonneg d)))
      hle hq.summable
  have hbound := Summable.tsum_le_tsum hle hs hq.summable
  have heq : (∑' x : Fin N × List (SearchTrace N), law.initialMass ranked.skip x * law.runClock x.2) = q :=
    hq.tsum_eq
  rw [heq] at hbound
  exact hbound.trans hqb

/-- **The finite executions are a sound replacement for the abstraction.**  For
every `ε > 0` there is a finite source-clock deadline that (i) lets the actual
executor return a minimum with probability at least `1 - ε`, and (ii) keeps the
truncated expected clock within Lemma 2's `m₀`.  This is the bridge between the
paper's infinite algorithm and the frozen finite charged executions. -/
theorem finite_execution_approximates_infinite (T : Fin N → α) (hN : 0 < N) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ,
      1 - ε ≤ sourceSuccess T hN ((D : ℝ) + 1) ∧
        truncatedAttainmentMean T hN D ≤ sourceMeanBudget N := by
  intro ε hε
  obtain ⟨D, hD⟩ := executor_success_approaches_one T hN ε hε
  exact ⟨D, hD, truncatedAttainmentMean_le_sourceMeanBudget T hN D⟩

/-- **The infinite algorithm's expected attainment time.**  The truncated means of
the finite executions converge to a mean that Lemma 2 bounds by `m₀`: the
paper's infinite algorithm has a finite expected time to hold the minimum, and
that time is the limit of the truncated ones. -/
theorem truncatedAttainmentMean_tendsto (T : Fin N → α) (hN : 0 < N) :
    ∃ q : ℝ, HasSum (fun x : Fin N × List (SearchTrace N) =>
      (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).initialMass
        (SortedRankedTable.ofTable T).skip x *
      (sourceBBHTLaw (SortedRankedTable.ofTable T).indexOfRank hN).runClock x.2) q ∧
      0 ≤ q ∧ q ≤ sourceMeanBudget N ∧
      Tendsto (fun d : ℕ => truncatedAttainmentMean T hN d) atTop (nhds q) := by
  set ranked := SortedRankedTable.ofTable T with hranked
  set law := sourceBBHTLaw ranked.indexOfRank hN with hlaw
  obtain ⟨q, hq, hq0, hqb⟩ := bbht_source_attainment_moment ranked hN
  have hnn := (law.initialMass_normalized ranked.skip hN).2
  have hclock := fun x : Fin N × List (SearchTrace N) => law.runClock_nonneg x.2
  have hlim : ∀ x : Fin N × List (SearchTrace N),
      Tendsto (fun d : ℕ => law.initialMass ranked.skip x * min (law.runClock x.2) (d : ℝ))
        atTop (nhds (law.initialMass ranked.skip x * law.runClock x.2)) := by
    intro x
    have hev : (fun _ : ℕ => law.runClock x.2) =ᶠ[atTop]
        (fun d : ℕ => min (law.runClock x.2) (d : ℝ)) := by
      filter_upwards [eventually_ge_atTop (Nat.ceil (law.runClock x.2))] with d hd
      exact (min_eq_left (Nat.ceil_le.mp hd)).symm
    have hmin : Tendsto (fun d : ℕ => min (law.runClock x.2) (d : ℝ)) atTop
        (nhds (law.runClock x.2)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => law.runClock x.2) atTop
        (nhds (law.runClock x.2))).congr' hev
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => law.initialMass ranked.skip x)
      atTop (nhds (law.initialMass ranked.skip x))).mul hmin
  have hbound : ∀ᶠ _d : ℕ in atTop, ∀ x : Fin N × List (SearchTrace N),
      ‖law.initialMass ranked.skip x * min (law.runClock x.2) (_d : ℝ)‖ ≤
        law.initialMass ranked.skip x * law.runClock x.2 := by
    filter_upwards with d x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hnn x) (le_min (hclock x) (Nat.cast_nonneg d)))]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hnn x)
  have htend := tendsto_tsum_of_dominated_convergence
    (f := fun d : ℕ => fun x : Fin N × List (SearchTrace N) =>
      law.initialMass ranked.skip x * min (law.runClock x.2) (d : ℝ))
    (g := fun x : Fin N × List (SearchTrace N) =>
      law.initialMass ranked.skip x * law.runClock x.2)
    hq.summable hlim hbound
  have hqeq : (∑' x : Fin N × List (SearchTrace N),
      law.initialMass ranked.skip x * law.runClock x.2) = q := hq.tsum_eq
  rw [hqeq] at htend
  refine ⟨q, ?_, hq0, hqb, ?_⟩
  · simpa only [hranked] using hq
  · simpa only [truncatedAttainmentMean, hranked, hlaw] using htend

end Qatlib.Papers.QMinimum99.Amplification
