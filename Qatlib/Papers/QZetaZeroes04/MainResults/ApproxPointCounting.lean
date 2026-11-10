/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.ApproxPointCounting

open Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
open scoped BigOperators

variable (H : ZetaHypersurface)

theorem point_count_deviation :
    H.firstPointCount - H.planeCountOf 1 =
      -(-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ) * H.traceMean := by
  unfold ZetaHypersurface.firstPointCount
  ring

theorem point_count_estimate_error (ε est : ℝ) (hε : 0 ≤ ε)
    (hest : |est - H.traceMean| ≤ ε) :
    |H.firstPointCount - H.pointCountEstimate est| ≤
      Real.sqrt ((H.q : ℝ) ^ (H.n - 1)) * (H.m : ℝ) ^ H.n * ε := by
  have hR : 0 < rootRadius H.q H.n := rootRadius_pos H.q_ge_two
  have hdim : (H.rootCount : ℝ) ≤ (H.m : ℝ) ^ H.n := by
    have h := H.rootCount_le
    have h' : (H.rootCount : ℝ) ≤ ((H.m ^ H.n : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hdiff : H.firstPointCount - H.pointCountEstimate est
      = (-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ)
          * (est - H.traceMean) := by
    unfold ZetaHypersurface.firstPointCount ZetaHypersurface.pointCountEstimate
    ring
  have hc : |(-1 : ℝ) ^ H.n| = 1 := by
    rw [abs_pow]; norm_num
  have hRnn : (0 : ℝ) ≤ rootRadius H.q H.n := le_of_lt hR
  have hdnn : (0 : ℝ) ≤ (H.rootCount : ℝ) := by positivity
  calc |H.firstPointCount - H.pointCountEstimate est|
      = |(-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ)
          * (est - H.traceMean)| := by rw [hdiff]
    _ = |(-1 : ℝ) ^ H.n| * |rootRadius H.q H.n| * |(H.rootCount : ℝ)|
          * |est - H.traceMean| := by rw [abs_mul, abs_mul, abs_mul]
    _ = rootRadius H.q H.n * (H.rootCount : ℝ) * |est - H.traceMean| := by
          rw [hc, abs_of_nonneg hRnn, abs_of_nonneg hdnn]; ring
    _ ≤ rootRadius H.q H.n * (H.rootCount : ℝ) * ε := by
          exact mul_le_mul_of_nonneg_left hest (mul_nonneg hRnn hdnn)
    _ ≤ rootRadius H.q H.n * (H.m : ℝ) ^ H.n * ε := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdim hRnn) hε
    _ = Real.sqrt ((H.q : ℝ) ^ (H.n - 1)) * (H.m : ℝ) ^ H.n * ε := by
          unfold rootRadius
          ring

theorem repetition_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, 1 / ε ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1 / ε + 1 := by
  refine ⟨Nat.ceil (1 / ε), ?_, ?_⟩
  · exact Nat.le_ceil _
  · have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / ε by positivity)
    linarith

theorem main_approximate_point_counting (ε est : ℝ) (hε : 0 < ε)
    (_hEff : HasPolynomialCostAnnotation H H.zetaCircuit)
    (hest : |est - H.traceMean| ≤ ε) :
    |H.firstPointCount - H.pointCountEstimate est| ≤
        Real.sqrt ((H.q : ℝ) ^ (H.n - 1)) * (H.m : ℝ) ^ H.n * ε ∧
      (∃ s : ℕ, 1 / ε ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1 / ε + 1) :=
  ⟨point_count_estimate_error H ε est (le_of_lt hε) hest, repetition_budget ε hε⟩

end Qatlib.Papers.QZetaZeroes04.MainResults.ApproxPointCounting
