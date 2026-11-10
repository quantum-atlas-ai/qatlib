/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.StochasticCalc.LognormalPay

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}

theorem terminalLevel_expectation
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 α σ T : ℝ} (hT : 0 ≤ T)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    ∫ ω, terminalLevel S0 α σ (W ω) T ∂Q = S0 * Real.exp (α * T) := by

  have hmgf : mgf W Q σ = Real.exp (T * σ ^ 2 / 2) := by
    rw [← mgf_id_map hWm, hW, mgf_id_gaussianReal]
    simp only [zero_mul, zero_add]
    congr 1

  have hsplit : ∀ ω, terminalLevel S0 α σ (W ω) T
      = (S0 * Real.exp ((α - σ ^ 2 / 2) * T)) * Real.exp (σ * W ω) := by
    intro ω
    unfold terminalLevel
    rw [Real.exp_add]
    ring
  calc ∫ ω, terminalLevel S0 α σ (W ω) T ∂Q
      = ∫ ω, (S0 * Real.exp ((α - σ ^ 2 / 2) * T)) * Real.exp (σ * W ω) ∂Q := by
          simp_rw [hsplit]
    _ = (S0 * Real.exp ((α - σ ^ 2 / 2) * T)) * ∫ ω, Real.exp (σ * W ω) ∂Q := by
          rw [integral_const_mul]
    _ = (S0 * Real.exp ((α - σ ^ 2 / 2) * T)) * mgf W Q σ := by rfl
    _ = (S0 * Real.exp ((α - σ ^ 2 / 2) * T)) * Real.exp (T * σ ^ 2 / 2) := by rw [hmgf]
    _ = S0 * (Real.exp ((α - σ ^ 2 / 2) * T) * Real.exp (T * σ ^ 2 / 2)) := by ring
    _ = S0 * Real.exp (α * T) := by
          rw [← Real.exp_add]
          congr 1
          ring

end

end Qatlib.Foundations.StochasticCalc.LognormalPay
