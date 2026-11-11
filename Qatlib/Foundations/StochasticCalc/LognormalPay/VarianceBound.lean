/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.TerminalMean

/-!
# A strike-independent call payoff variance bound

This module defines `bsVarianceBound` from the first two lognormal moments and proves that it
bounds the call payoff variance. The theorem `callPayoff_variance_le` allows nonnegative
maturity, initial level, and strike and assumes the prescribed centered Gaussian input law.

The mathematical background is discussed in [RebentrostGuptBromley2018].

## Main statements

* `bsVarianceBound`: twice the terminal second moment plus twice the squared terminal mean.
* `callPayoff_variance_le`: bounds the payoff variance independently of the strike.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.StochasticCalc.LognormalPay

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}

/-- The bound `2 * S0 ^ 2 * exp ((2 * r + σ ^ 2) * T) + 2 * S0 ^ 2 * exp (2 * r * T)` for
lognormal call payoff variance. -/
def bsVarianceBound (S0 r σ T : ℝ) : ℝ :=
  2 * (S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T)) + 2 * (S0 ^ 2 * Real.exp (2 * r * T))

/-- For nonnegative maturity, initial level, and strike and the stated centered Gaussian input
law, the call payoff variance is at most `bsVarianceBound S0 r σ T`. -/
theorem callPayoff_variance_le
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 K r σ T : ℝ}
    (hT : 0 ≤ T) (hS0 : 0 ≤ S0) (hK : 0 ≤ K)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    variance (fun ω => callPayoff K (terminalLevel S0 r σ (W ω) T)) Q ≤
      bsVarianceBound S0 r σ T := by
  set X : Ω → ℝ := fun ω => terminalLevel S0 r σ (W ω) T with hXdef
  have hXm : AEMeasurable X Q := by
    rw [hXdef]
    unfold terminalLevel
    fun_prop
  have hX_nonneg : ∀ ω, 0 ≤ X ω := by
    intro ω
    rw [hXdef]
    unfold terminalLevel
    exact mul_nonneg hS0 (Real.exp_pos _).le

  have hmgf1 : mgf W Q σ = Real.exp (T * σ ^ 2 / 2) := by
    rw [← mgf_id_map hWm, hW, mgf_id_gaussianReal]
    simp only [zero_mul, zero_add]
    congr 1
  have hmgf2 : mgf W Q (2 * σ) = Real.exp (T * (2 * σ) ^ 2 / 2) := by
    rw [← mgf_id_map hWm, hW, mgf_id_gaussianReal]
    simp only [zero_mul, zero_add]
    congr 1
  have hIntExp : Integrable (fun ω => Real.exp (σ * W ω)) Q :=
    mgf_pos_iff.mp (by rw [hmgf1]; positivity)
  have hIntExp2 : Integrable (fun ω => Real.exp ((2 * σ) * W ω)) Q :=
    mgf_pos_iff.mp (by rw [hmgf2]; positivity)

  have hXeq : X = fun ω => (S0 * Real.exp ((r - σ ^ 2 / 2) * T)) * Real.exp (σ * W ω) := by
    funext ω
    simp only [hXdef]
    unfold terminalLevel
    rw [Real.exp_add]
    ring
  have hIntX : Integrable X Q := by
    rw [hXeq]
    exact hIntExp.const_mul _

  have hsq : ∀ ω, (X ω) ^ 2
      = (S0 ^ 2 * Real.exp ((2 * r - σ ^ 2) * T)) * Real.exp ((2 * σ) * W ω) := by
    intro ω
    rw [hXdef]
    unfold terminalLevel
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (σ * W ω + (r - σ ^ 2 / 2) * T)
          = (2 * r - σ ^ 2) * T + (2 * σ) * W ω by push_cast; ring]
    rw [Real.exp_add]
    ring
  have hIntSq : Integrable (fun ω => (X ω) ^ 2) Q := by
    have heq : (fun ω => (X ω) ^ 2)
        = fun ω => (S0 ^ 2 * Real.exp ((2 * r - σ ^ 2) * T)) * Real.exp ((2 * σ) * W ω) := by
      funext ω
      exact hsq ω
    rw [heq]
    exact hIntExp2.const_mul _
  have hIntSqVal : ∫ ω, (X ω) ^ 2 ∂Q = S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T) := by
    simp_rw [hsq]
    rw [integral_const_mul]
    rw [show ∫ ω, Real.exp ((2 * σ) * W ω) ∂Q = Real.exp (T * (2 * σ) ^ 2 / 2) by
      simpa [mgf] using hmgf2]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring

  have hm : ∫ ω, X ω ∂Q = S0 * Real.exp (r * T) := by
    show ∫ ω, terminalLevel S0 r σ (W ω) T ∂Q = S0 * Real.exp (r * T)
    exact terminalLevel_expectation hT hW hWm
  set m : ℝ := ∫ ω, callPayoff K (X ω) ∂Q with hmdef
  have hc_meas : AEMeasurable (fun ω => callPayoff K (X ω)) Q := by
    unfold callPayoff
    fun_prop
  have hc_nonneg : ∀ ω, 0 ≤ callPayoff K (X ω) := fun ω => le_max_right _ _
  have hc_le : ∀ ω, callPayoff K (X ω) ≤ X ω := by
    intro ω
    unfold callPayoff
    exact max_le (by linarith) (hX_nonneg ω)
  have hm_nonneg : 0 ≤ m := by
    rw [hmdef]
    exact integral_nonneg hc_nonneg
  have hm_le : m ≤ S0 * Real.exp (r * T) := by
    rw [hmdef]
    calc ∫ ω, callPayoff K (X ω) ∂Q
        ≤ ∫ ω, X ω ∂Q := by
          refine integral_mono_of_nonneg (ae_of_all _ hc_nonneg) hIntX
            (ae_of_all _ fun ω => hc_le ω)
      _ = S0 * Real.exp (r * T) := hm
  have hm_sq_le : m ^ 2 ≤ (S0 * Real.exp (r * T)) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hm_nonneg hm_le
  have hmsq_eq : (S0 * Real.exp (r * T)) ^ 2 = S0 ^ 2 * Real.exp (2 * r * T) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring

  have hg_int : Integrable (fun ω => 2 * (X ω) ^ 2 + 2 * m ^ 2) Q :=
    (hIntSq.const_mul 2).add (integrable_const (2 * m ^ 2))
  have hmono : ∫ ω, (callPayoff K (X ω) - m) ^ 2 ∂Q
      ≤ ∫ ω, 2 * (X ω) ^ 2 + 2 * m ^ 2 ∂Q := by
    refine integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) hg_int ?_
    refine ae_of_all _ fun ω => ?_
    have hcl : (callPayoff K (X ω)) ^ 2 ≤ (X ω) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (hc_nonneg ω) (hc_le ω)
    nlinarith [sq_nonneg (callPayoff K (X ω) + m), hcl]
  have hval : ∫ ω, 2 * (X ω) ^ 2 + 2 * m ^ 2 ∂Q
      = 2 * (S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T)) + 2 * m ^ 2 := by
    rw [integral_add (hIntSq.const_mul 2) (integrable_const (2 * m ^ 2)),
      integral_const_mul, integral_const]
    rw [hIntSqVal]
    simp
  have hvar : variance (fun ω => callPayoff K (terminalLevel S0 r σ (W ω) T)) Q
      = ∫ ω, (callPayoff K (X ω) - m) ^ 2 ∂Q := by
    rw [variance_eq_integral hc_meas]
  rw [hvar]
  calc ∫ ω, (callPayoff K (X ω) - m) ^ 2 ∂Q
      ≤ ∫ ω, 2 * (X ω) ^ 2 + 2 * m ^ 2 ∂Q := hmono
    _ = 2 * (S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T)) + 2 * m ^ 2 := hval
    _ ≤ bsVarianceBound S0 r σ T := by
        unfold bsVarianceBound
        nlinarith [hm_sq_le, hmsq_eq]

end

end Qatlib.Foundations.StochasticCalc.LognormalPay
