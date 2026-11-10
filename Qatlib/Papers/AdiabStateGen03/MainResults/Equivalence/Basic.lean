/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence

open Qatlib.Papers.AdiabStateGen03.MainResults

lemma gate_sqrt_overlap_real (x : ℝ) (hx : |x| ≤ 1) :
    1 / Real.sqrt 2 ≤
      ‖(((1 : ℂ) + Complex.I) / 2) + ((1 - Complex.I) / 2) * (x : ℂ)‖ := by
  have hz : (((1 : ℂ) + Complex.I) / 2) + ((1 - Complex.I) / 2) * (x : ℂ)
      = ((1 + x) / 2 : ℝ) + ((1 - x) / 2 : ℝ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hz, Complex.norm_add_mul_I]
  have hx2 : x ^ 2 ≤ 1 := by
    have := abs_le.mp hx
    nlinarith
  have hsq : (((1 + x) / 2) ^ 2 + ((1 - x) / 2) ^ 2) = (1 + x ^ 2) / 2 := by ring
  have hge : (1 : ℝ) / 2 ≤ (1 + x ^ 2) / 2 := by nlinarith
  have hsqrt : 1 / Real.sqrt 2 = Real.sqrt (1 / 2) := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, one_div]
  rw [hsqrt, hsq]
  exact Real.sqrt_le_sqrt hge

theorem norm_inner_le_one {n : ℕ} (α β : State n) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) :
    ‖⟪α, β⟫_ℂ‖ ≤ 1 := by
  calc ‖⟪α, β⟫_ℂ‖ ≤ ‖α‖ * ‖β‖ := norm_inner_le_norm α β
    _ = 1 := by rw [hα, hβ, one_mul]

theorem norm_inner_comm {n : ℕ} (α β : State n) :
    ‖⟪α, β⟫_ℂ‖ = ‖⟪β, α⟫_ℂ‖ := by
  rw [← inner_conj_symm α β, Complex.norm_conj]

end Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence
