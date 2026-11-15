/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentWeight
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix

variable {D : ℕ}

noncomputable def phaseKernel (β ν : ℝ) : ℝ := 1 / (2 * Real.cosh (β * ν / 4))

/-- The phase kernel at zero frequency is one half. -/
theorem phaseKernel_self (β : ℝ) : phaseKernel β 0 = 1 / 2 := by
  simp [phaseKernel, Real.cosh_zero]

/-- The phase kernel is strictly positive for all real parameters. -/
theorem phaseKernel_pos (β ν : ℝ) : 0 < phaseKernel β ν := by
  have h : 0 < 2 * Real.cosh (β * ν / 4) := by
    have := Real.cosh_pos (β * ν / 4)
    linarith
  exact one_div_pos.mpr h

/-- The real hyperbolic cosine is at least one. -/
theorem one_le_cosh (x : ℝ) : 1 ≤ Real.cosh x := by
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq : (0 : ℝ) ≤ (Real.exp x - Real.exp (-x)) ^ 2 := sq_nonneg _
  rw [Real.cosh_eq]
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- The phase kernel is at most one half. -/
theorem phaseKernel_le_half (β ν : ℝ) : phaseKernel β ν ≤ 1 / 2 := by
  rw [phaseKernel,
    one_div_le_one_div (by positivity : (0 : ℝ) < 2 * Real.cosh (β * ν / 4))
      (by norm_num : (0 : ℝ) < 2)]
  have hc : 1 ≤ Real.cosh (β * ν / 4) := one_le_cosh _
  linarith

/-- The phase kernel is even in its frequency argument. -/
theorem phaseKernel_neg (β ν : ℝ) : phaseKernel β (-ν) = phaseKernel β ν := by
  have h : β * (-ν) / 4 = -(β * ν / 4) := by ring
  rw [phaseKernel, phaseKernel, h, Real.cosh_neg]

/-- The phase kernel is strictly less than one half when the product of its parameters is
nonzero. -/
theorem phaseKernel_lt_half {β ν : ℝ} (h : β * ν ≠ 0) : phaseKernel β ν < 1 / 2 := by
  have hx : β * ν / 4 ≠ 0 := by
    intro h0
    exact h (by nlinarith)
  have hc : 1 < Real.cosh (β * ν / 4) := Real.one_lt_cosh.mpr hx
  have hp : 0 < 2 * Real.cosh (β * ν / 4) := by
    have := Real.cosh_pos (β * ν / 4)
    linarith
  rw [phaseKernel, one_div_lt_one_div hp (by norm_num : (0 : ℝ) < 2)]
  linarith

noncomputable def bohrJump {ι : Type*} [Fintype ι] (ν : ι → ℝ) (A : ι → Operator D)
    (t : ℝ) : Operator D :=
  ∑ i, (Complex.exp ((↑(ν i * t) : ℂ) * Complex.I)) • A i

/-- The Bohr jump is the sum of the jump operators weighted by their frequency-dependent complex
phases. -/
theorem bohrJump_apply {ι : Type*} [Fintype ι] (ν : ι → ℝ) (A : ι → Operator D) (t : ℝ) :
    bohrJump ν A t = ∑ i, (Complex.exp ((↑(ν i * t) : ℂ) * Complex.I)) • A i := rfl

/-- At time zero, the Bohr jump is the sum of all jump operators. -/
theorem bohrJump_zero {ι : Type*} [Fintype ι] (ν : ι → ℝ) (A : ι → Operator D) :
    bohrJump ν A 0 = ∑ i, A i := by
  simp [bohrJump]

/-- When every frequency is zero, the Bohr jump is the sum of the jump operators at every time. -/
theorem bohrJump_of_freq_zero {ι : Type*} [Fintype ι] {ν : ι → ℝ} (hν : ∀ i, ν i = 0)
    (A : ι → Operator D) (t : ℝ) : bohrJump ν A t = ∑ i, A i := by
  simp [bohrJump, hν]

/-- The parent factor of the time-zero Bohr jump equals the parent factor of the sum of jumps. -/
theorem parentFactor_bohrJump_zero {ι : Type*} [Fintype ι] (ρ : Operator D) (ν : ι → ℝ)
    (A : ι → Operator D) (X : Operator D) :
    parentFactor ρ (bohrJump ν A 0) X = parentFactor ρ (∑ i, A i) X := by
  rw [bohrJump_zero]

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
