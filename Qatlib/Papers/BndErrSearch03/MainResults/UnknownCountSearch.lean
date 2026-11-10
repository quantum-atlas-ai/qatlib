/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoalTigh
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3CorrectedTigh
import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.NeedleSearch
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BndErrSearch03.MainResults.UnknownCountSearch

open Qatlib.Concepts.SearchStopping.RestartLaw

theorem restarts_cost_le (c p : ℝ) (hc : 0 ≤ c)
    (hp : (1 / 576 : ℝ) ≤ p) (hp1 : p ≤ 1) :
    (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * c * ((1 - p) ^ r * p)) ≤ 576 * c := by
  have hp0 : 0 < p := by linarith
  rw [geometric_restart_expectation p c hp0 hp1]
  rw [div_le_iff₀ hp0]
  nlinarith [hc, hp]

open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.UnknownCount

theorem unknown_count_expected_iterations {I : Type} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum
      (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
        TerminalMass A (ExponentialSizes (Fintype.card I)) x *
          (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have h := Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected
    (I := I) hI
  dsimp only at h
  exact (h.1 A hA).2.2.2.1

theorem unknown_count_expected_cost_le {I : Type} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum
      (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
        TerminalMass A (ExponentialSizes (Fintype.card I)) x *
          (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) ∧
      ∀ p : ℝ, (1 / 576 : ℝ) ≤ p → p ≤ 1 →
        (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * q * ((1 - p) ^ r * p))
          ≤ 576 * ((9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card)) := by
  obtain ⟨q, hsum, hq0, hqle⟩ := unknown_count_expected_iterations hI A hA
  refine ⟨q, hsum, hq0, hqle, ?_⟩
  intro p hp hp1
  have h1 : (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * q * ((1 - p) ^ r * p)) ≤ 576 * q :=
    restarts_cost_le q p hq0 hp hp1
  have h2 : 576 * q ≤ 576 * ((9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card)) :=
    mul_le_mul_of_nonneg_left hqle (by norm_num)
  linarith

theorem restarts_failure_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Filter.Tendsto (fun r : ℕ => (1 - p) ^ r) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

theorem sqrt_ratio_le_ratio (N t : ℝ) (ht : 0 < t) (htN : t ≤ N) :
    Real.sqrt (N / t) ≤ N / t := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le ht htN
  have hx0 : (0 : ℝ) ≤ N / t := le_of_lt (div_pos hNpos ht)
  rw [Real.sqrt_le_left hx0]
  have hx1 : 1 ≤ N / t := (one_le_div ht).mpr htN
  simpa [one_mul, pow_two] using mul_le_mul_of_nonneg_left hx1 hx0

open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

theorem classical_half_success_requires_linear_queries {I S : Type} [Fintype I]
    [DecidableEq I] [Fintype S] (weight : S → ℝ) (tree : S → QueryTree I Bool I)
    (M : ℕ) (hI : 0 < Fintype.card I) (hw : ∀ s, 0 ≤ weight s)
    (hmass : ∑ s, weight s = 1)
    (hcost : ∀ s y, (run (needleOracle y) (tree s)).2 ≤ M)
    (hsucc : (1 / 2 : ℝ) ≤ ∑ s, weight s * needleSuccess (tree s)) :
    (Fintype.card I : ℝ) / 2 ≤ (M : ℝ) + 1 := by
  have h := randomized_needle_success_upper weight tree M hw hmass hcost
  have hN : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hI
  have hge : (1 / 2 : ℝ) ≤ ((M : ℝ) + 1) / Fintype.card I := le_trans hsucc h
  rw [le_div_iff₀ hN] at hge
  linarith

theorem quantum_cost_below_classical (N : ℕ) (hN : 81 ≤ N) :
    (9 / 2 : ℝ) * Real.sqrt N ≤ (N : ℝ) / 2 := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hN81 : (81 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) / 9 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hN81)]
  nlinarith

end Qatlib.Papers.BndErrSearch03.MainResults.UnknownCountSearch
