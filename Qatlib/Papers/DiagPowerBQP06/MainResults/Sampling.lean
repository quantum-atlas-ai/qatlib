/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Finset

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.Sampling

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem sampling_error_bound
    (p : FinDist Ω) (Z : Ω → ℝ) (m k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε)
    (hZ : ∀ ω, |Z ω| ≤ 1) :
    eventMass (independent (fun _ : Fin k => p))
      (fun ω => ε / 3 ≤ |weightedSum (fun _ => (1 : ℝ) / k)
          (fun _ x => (Z x) ^ m) ω - p.expect (fun x => (Z x) ^ m)|) ≤
      2 * Real.exp (-(ε ^ 2 * (k : ℝ)) / 18) := by
  classical
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'

  have hexp : (independent (fun _ : Fin k => p)).expect
      (weightedSum (fun _ : Fin k => (1 : ℝ) / k) (fun _ x => (Z x) ^ m))
      = p.expect (fun x => (Z x) ^ m) := by
    rw [ProbabilityInterfaces.independent_weighted_expectation]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

  have hSval : ∑ _i : Fin k, ((1 : ℝ) / k) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 = 4 / (k : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h4 : ((1 : ℝ) - (-1)) ^ 2 = 4 := by norm_num
    rw [h4]
    field_simp
  have hSpos : 0 < ∑ _i : Fin k, ((1 : ℝ) / k) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [hSval]
    positivity

  have hrange : ∀ (_i : Fin k) (x : Ω), (Z x) ^ m ∈ Set.Icc (-1 : ℝ) 1 := by
    intro _ x
    refine Set.mem_Icc.mpr (abs_le.mp ?_)
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hZ x)
  have hmain := ProbabilityInterfaces.independent_weighted_hoeffding
    (p := fun _ : Fin k => p)
    (w := fun _ : Fin k => (1 : ℝ) / k)
    (f := fun _ x => (Z x) ^ m)
    (a := fun _ : Fin k => (-1 : ℝ)) (b := fun _ : Fin k => 1)
    (u := ε / 3) (fun _ => by norm_num) hrange (by positivity) hSpos
  rw [hexp, hSval] at hmain
  have hexp_eq : -2 * (ε / 3) ^ 2 / (4 / (k : ℝ)) = -(ε ^ 2 * (k : ℝ)) / 18 := by
    field_simp
    ring
  rwa [hexp_eq] at hmain

theorem sampled_mean_to_diagonal_error {mean moment diag ε : ℝ}
    (h1 : |mean - moment| ≤ ε / 3) (h2 : |moment - diag| ≤ ε / 3) (hε : 0 ≤ ε) :
    |mean - diag| ≤ 2 * ε / 3 := by
  calc |mean - diag| = |(mean - moment) + (moment - diag)| := by ring_nf
    _ ≤ |mean - moment| + |moment - diag| := abs_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add h1 h2
    _ = 2 * ε / 3 := by ring

end Qatlib.Papers.DiagPowerBQP06.MainResults.Sampling
