/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A model counterinstance for the legacy sparse-simulation lower bound.
An output matrix and a resource field do not define an oracle algorithm.
-/
set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.SpectralAmp17.MainResults
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

/-- The legacy simulator predicate admits exact evolution with a zero query report. -/
theorem zero_query_report {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (t : ℝ) :
    ∃ alg : BlackBoxSimulator n,
      ApproximatesTimeEvolution alg H t (1 / 2) ∧ alg.queries = 0 := by
  exact ⟨⟨0, timeEvolution H t, False⟩, by norm_num [ApproximatesTimeEvolution], rfl⟩

/-- For any positive claimed cost, the exact zero-query report violates that lower bound. -/
theorem simulation_lower_false {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (t c : ℝ) (hc : 0 < c) :
    ¬ ∀ alg : BlackBoxSimulator n,
      ApproximatesTimeEvolution alg H t (1 / 2) → c ≤ alg.queries := by
  obtain ⟨alg, happrox, hzero⟩ := zero_query_report H t
  intro h
  have hbound := h alg happrox
  rw [hzero] at hbound
  exact (not_le.mpr hc) hbound

end Qatlib.Papers.SpectralAmp17.MainResults
