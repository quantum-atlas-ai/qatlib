/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRiskWoerner18.PayoffMean.SourcePayoffVariance

@[expose] public section

/-!
# Query and macro counts for the two variance payoffs

Section II uses the normalized level and its square in separate amplitude-estimation
runs. The counts add across the two runs with fresh initialization.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QRiskWoerner18.PayoffMean

open Qatlib.Papers.QRiskWoerner18.PayoffMean
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian

/-- The two repeated payoff runs have twice the query and matrix-macro counts of one run. -/
theorem variance_fees (n M r : ℕ) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    QueryCount (RepeatCircuit (countedAECircuit M (payoffPreparation A (sourceLevel n))
      (sourceZero n, false)) (2 * r + 1)) +
    QueryCount (RepeatCircuit (countedAECircuit M
      (payoffPreparation A (fun i => (sourceLevel n i) ^ 2))
      (sourceZero n, false)) (2 * r + 1)) = 2 * (2 * r + 1) * (M - 1) ∧
    GateCount (RepeatCircuit (countedAECircuit M (payoffPreparation A (sourceLevel n))
      (sourceZero n, false)) (2 * r + 1)) +
    GateCount (RepeatCircuit (countedAECircuit M
      (payoffPreparation A (fun i => (sourceLevel n i) ^ 2))
      (sourceZero n, false)) (2 * r + 1)) = 2 * (2 * r + 1) * (5 * (M - 1) + 3) := by
  have hlevel := sourceLevel_mem_Icc n hn
  have hsq (i : Fin (2 ^ n)) : (sourceLevel n i) ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, pow_le_one₀ (hlevel i).1 (hlevel i).2⟩
  obtain ⟨_, hq₁, hg₁, _, _⟩ := source_payoff_accesses n M r hM A (sourceLevel n) hA hlevel
  obtain ⟨_, hq₂, hg₂, _, _⟩ :=
    source_payoff_accesses n M r hM A (fun i => (sourceLevel n i) ^ 2) hA hsq
  constructor
  · rw [hq₁, hq₂]
    ring
  · rw [hg₁, hg₂]
    ring

end Qatlib.Papers.QRiskWoerner18.PayoffMean
