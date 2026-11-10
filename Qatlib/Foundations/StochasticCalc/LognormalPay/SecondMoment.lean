/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.CallPrice
import Qatlib.Foundations.StochasticCalc.LognormalPay.VarianceBound
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.StochasticCalc.LognormalPay
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

lemma terminalLevel_pow (S0 r σ T w : ℝ) (n : ℕ) :
    terminalLevel S0 r σ w T ^ n =
      (S0 ^ n * Real.exp ((n : ℝ) * (r - σ ^ 2 / 2) * T)) *
        Real.exp (((n : ℝ) * σ) * w) := by
  unfold terminalLevel
  rw [mul_pow, ← Real.exp_nat_mul, show (n : ℝ) * (σ * w + (r - σ ^ 2 / 2) * T) =
    (n : ℝ) * (r - σ ^ 2 / 2) * T + ((n : ℝ) * σ) * w by ring, Real.exp_add]
  ring

lemma integrable_density_power {T : ℝ} (hT : 0 < T) (S0 r σ : ℝ) (n : ℕ) :
    Integrable (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T ^ n) := by
  simp_rw [terminalLevel_pow]
  have heq : (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w *
      ((S0 ^ n * Real.exp ((n : ℝ) * (r - σ ^ 2 / 2) * T)) *
        Real.exp (((n : ℝ) * σ) * w))) =
      fun w => (S0 ^ n * Real.exp ((n : ℝ) * (r - σ ^ 2 / 2) * T)) *
        (gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (((n : ℝ) * σ) * w)) := by
    funext w; ring
  rw [heq]
  exact (integrable_gaussianPDFReal_exp hT _).const_mul _

lemma truncated_power {T : ℝ} (hT : 0 < T) (S0 r σ a : ℝ) (n : ℕ) :
    (∫ w in Set.Ioi a, gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T ^ n) =
      S0 ^ n * Real.exp ((n : ℝ) * (r - σ ^ 2 / 2) * T + ((n : ℝ) * σ) ^ 2 * T / 2) *
        normalCDF (((n : ℝ) * σ) * Real.sqrt T - a / Real.sqrt T) := by
  simp_rw [terminalLevel_pow]
  have heq : (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w *
      ((S0 ^ n * Real.exp ((n : ℝ) * (r - σ ^ 2 / 2) * T)) *
        Real.exp (((n : ℝ) * σ) * w))) =
      fun w => (S0 ^ n * Real.exp ((n : ℝ) * (r - σ ^ 2 / 2) * T)) *
        (gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (((n : ℝ) * σ) * w)) := by
    funext w; ring
  rw [heq, integral_const_mul, integral_Ioi_gaussianPDFReal_exp hT]
  rw [Real.exp_add]
  ring

lemma d3_eq_tilt_threshold {S0 K r σ T : ℝ} (hT : 0 < T) :
    d3 S0 K r σ T = (2 * σ) * Real.sqrt T - bsThreshold S0 K r σ T / Real.sqrt T := by
  have hd1 := d1_eq_tilt_threshold (S0 := S0) (K := K) (r := r) (σ := σ) hT
  have h : d3 S0 K r σ T = d1 S0 K r σ T + σ * Real.sqrt T := by
    unfold d3 d1
    field_simp
    rw [Real.sq_sqrt hT.le]
    ring
  rw [h, hd1]
  ring

theorem call_second_moment_gaussian {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ) :
    (∫ w, callPayoff K (terminalLevel S0 r σ w T) ^ 2 ∂gaussianReal 0 ⟨T, hT.le⟩) =
      S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T) * normalCDF (d3 S0 K r σ T)
        - 2 * K * S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T)
        + K ^ 2 * normalCDF (d2 S0 K r σ T) := by
  have hv : (⟨T, hT.le⟩ : NNReal) ≠ 0 := by
    intro hz
    exact hT.ne' (congrArg (fun x : NNReal => (x : ℝ)) hz)
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := ⟨T, hT.le⟩) hv]
  simp only [smul_eq_mul]
  let a := bsThreshold S0 K r σ T
  have hsplit : (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w *
      callPayoff K (terminalLevel S0 r σ w T) ^ 2) = Set.indicator (Set.Ici a)
      (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K) ^ 2) := by
    funext w
    by_cases h : a ≤ w
    · have hh := (terminalLevel_ge_iff_threshold hS0 hK hσ).2 h
      simp [Set.indicator, Set.mem_Ici, h, callPayoff, max_eq_left (sub_nonneg.2 hh)]
    · have hh : terminalLevel S0 r σ w T ≤ K := by
        by_contra hn
        exact h ((terminalLevel_ge_iff_threshold hS0 hK hσ).1 (le_of_not_ge hn))
      simp [Set.indicator, Set.mem_Ici, h, callPayoff, max_eq_right (sub_nonpos.2 hh)]
  rw [hsplit, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hpoly : (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K) ^ 2) =
      fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T ^ 2 -
        (2 * K) * (gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T ^ 1) +
        K ^ 2 * (gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T ^ 0) := by
    funext w; ring
  have hi2 := (integrable_density_power hT S0 r σ 2).integrableOn (s := Set.Ioi a)
  have hi1 := ((integrable_density_power hT S0 r σ 1).const_mul (2*K)).integrableOn (s := Set.Ioi a)
  have hi0 := ((integrable_density_power hT S0 r σ 0).const_mul (K^2)).integrableOn (s := Set.Ioi a)
  rw [hpoly, integral_add (by exact hi2.sub hi1) hi0,
    integral_sub hi2 hi1, integral_const_mul, integral_const_mul,
    truncated_power hT S0 r σ a 2, truncated_power hT S0 r σ a 1, truncated_power hT S0 r σ a 0]
  norm_num only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_mul, zero_add, zero_sub,
    zero_pow, one_pow, pow_zero, pow_one, div_one, Real.exp_zero, mul_one, one_mul]
  rw [show 2 * (r - σ ^ 2 / 2) * T + (2 * σ) ^ 2 * T / 2 = (2 * r + σ ^ 2) * T by ring,
    show (r - σ ^ 2 / 2) * T + σ ^ 2 * T / 2 = r * T by ring,
    ← d3_eq_tilt_threshold hT, ← d1_eq_tilt_threshold hT, ← d2_eq_neg_threshold hT]
  ring

theorem call_memLp_two {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 K r σ T : ℝ}
    (hT : 0 ≤ T) (hS0 : 0 ≤ S0) (hK : 0 ≤ K)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    MemLp (fun ω => callPayoff K (terminalLevel S0 r σ (W ω) T)) 2 Q := by
  have hmgf : mgf W Q (2 * σ) = Real.exp (T * (2 * σ) ^ 2 / 2) := by
    rw [← mgf_id_map hWm, hW, mgf_id_gaussianReal]
    simp only [zero_mul, zero_add]
    rfl
  have hexp : Integrable (fun ω => Real.exp ((2 * σ) * W ω)) Q :=
    mgf_pos_iff.mp (by rw [hmgf]; positivity)
  have hsq : Integrable (fun ω => terminalLevel S0 r σ (W ω) T ^ 2) Q := by
    simp_rw [terminalLevel_pow]
    norm_num only [Nat.cast_ofNat]
    exact hexp.const_mul _
  have hm : AEStronglyMeasurable (fun ω => callPayoff K (terminalLevel S0 r σ (W ω) T)) Q := by
    unfold callPayoff terminalLevel
    fun_prop
  refine (memLp_two_iff_integrable_sq hm).2 (hsq.mono' (hm.pow 2) ?_)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs : 0 ≤ terminalLevel S0 r σ (W ω) T := mul_nonneg hS0 (Real.exp_pos _).le
  have hc : 0 ≤ callPayoff K (terminalLevel S0 r σ (W ω) T) := le_max_right _ _
  have hle : callPayoff K (terminalLevel S0 r σ (W ω) T) ≤ terminalLevel S0 r σ (W ω) T :=
    max_le (by linarith) hs
  nlinarith

theorem call_second_moment {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT.le⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    (∫ ω, callPayoff K (terminalLevel S0 r σ (W ω) T) ^ 2 ∂Q) =
      S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T) * normalCDF (d3 S0 K r σ T)
        - 2 * K * S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T)
        + K ^ 2 * normalCDF (d2 S0 K r σ T) := by
  have hm : AEStronglyMeasurable (fun w => callPayoff K (terminalLevel S0 r σ w T) ^ 2) (Q.map W) := by
    exact (by unfold callPayoff terminalLevel; fun_prop :
      Continuous (fun w => callPayoff K (terminalLevel S0 r σ w T) ^ 2)).aestronglyMeasurable
  rw [← integral_map hWm hm, hW]
  exact call_second_moment_gaussian hT hS0 hK hσ

theorem call_variance_exact {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT.le⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    variance (fun ω => callPayoff K (terminalLevel S0 r σ (W ω) T)) Q =
      S0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * T) * normalCDF (d3 S0 K r σ T)
        - 2 * K * S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T)
        + K ^ 2 * normalCDF (d2 S0 K r σ T)
        - (S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T) -
            K * normalCDF (d2 S0 K r σ T)) ^ 2 := by
  rw [variance_eq_sub (call_memLp_two hT.le hS0.le hK.le hW hWm)]
  simp only [Pi.pow_apply]
  rw [call_second_moment hT hS0 hK hσ hW hWm]
  have hm : AEStronglyMeasurable (fun w => callPayoff K (terminalLevel S0 r σ w T)) (Q.map W) := by
    exact (by unfold callPayoff terminalLevel; fun_prop :
      Continuous (fun w => callPayoff K (terminalLevel S0 r σ w T))).aestronglyMeasurable
  rw [← integral_map hWm hm, hW, call_expectation_gaussian hT hS0 hK hσ]

end
end Qatlib.Foundations.StochasticCalc.LognormalPay
