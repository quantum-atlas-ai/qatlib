/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeStat
import Qatlib.Concepts.SpectralReadout.NoiseStatistics.NoiseSequenceSecondMomentAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.SpectralReadout.NoiseStatistics
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

def ExpectedNoiseEnvelopeBridgeOriginal : Prop :=
  ∀ (M N : ℕ), 1 ≤ M → 0 < N →
    let MinL : ℝ := if M = 1 then -(1 : ℝ)
      else -(M:ℝ)^2 +
        Real.sqrt ((M:ℝ)*((M:ℝ)-1)*((M:ℝ)*((M:ℝ)-1)+(N:ℝ)))
    let bound : ℝ → ℝ := fun L =>
      (L+(M:ℝ)^2)/(((N:ℝ)-L-(M:ℝ))*(L+(M:ℝ)))
    (-(M:ℝ) < MinL ∧ MinL < (N:ℝ)-(M:ℝ)) ∧
    (∀ L : ℝ, -(M:ℝ) < L → L < (N:ℝ)-(M:ℝ) → bound MinL ≤ bound L) ∧
    (1 < M → 0 < bound MinL) ∧
    (∃ k : ℕ, 1 ≤ k ∧ (k:ℝ) * bound MinL ≤ 1)

theorem expectedNoiseEnvelopeBridge_false : ¬ ExpectedNoiseEnvelopeBridgeOriginal := by
  intro h
  have hb := (h 1 1 (by decide) (by decide)).1.1
  norm_num at hb

theorem expectedNoiseEnvelope_actual_average (N M L : ℕ) [NeZero N]
    (y : ZMod N) (c : ℂ) (hy : y ≠ 0) (hM : 1 ≤ M)
    (hsize : M + L < N) (hc : ‖c‖ ≤ (M : ℝ)) :
    (((N : ℝ) ^ L)⁻¹ * (∑ ω : Fin L → ZMod N,
      ‖c + ∑ i, ZMod.stdAddChar (ω i * y)‖ ^ 2)) /
      ((M : ℝ) + L) ^ 2 *
      (((M : ℝ) + L) / ((N : ℝ) - L - M)) * aqGain N (M + L) ≤
      ((L : ℝ) + (M : ℝ) ^ 2) /
        (((N : ℝ) - L - M) * ((L : ℝ) + M)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ht : (0 : ℝ) < (M : ℝ) + L := by positivity
  have hnt : (0 : ℝ) < (N : ℝ) - L - M := by
    have hnR : (M : ℝ) + L < N := by exact_mod_cast hsize
    linarith
  have hmoment := (noiseSequenceSecondMoment N L y c 1 hy).2
  simp only [one_pow, one_mul, Complex.ofReal_one, one_mul] at hmoment
  rw [hmoment]
  have hgain : aqGain N (M + L) ≤ 1 := Real.sin_sq_le_one _
  have hnonneg : 0 ≤ (‖c‖ ^ 2 + (L : ℝ)) /
      ((M : ℝ) + L) ^ 2 * (((M : ℝ) + L) / ((N : ℝ) - L - M)) := by
    positivity
  calc
    _ ≤ (‖c‖ ^ 2 + (L : ℝ)) / ((M : ℝ) + L) ^ 2 *
        (((M : ℝ) + L) / ((N : ℝ) - L - M)) := by
      exact mul_le_of_le_one_right hnonneg hgain
    _ = (‖c‖ ^ 2 + (L : ℝ)) /
        (((N : ℝ) - L - M) * ((L : ℝ) + M)) := by
      field_simp
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [norm_nonneg c]

theorem expectedNoiseEnvelope_one_physical_minimum (N : ℕ) (hN : 1 < N)
    (L : ℝ) (hL : 0 ≤ L) (hLN : L < (N : ℝ) - 1) :
    (L + 1) / (((N : ℝ) - L - 1) * (L + 1)) =
      1 / ((N : ℝ) - L - 1) ∧
    1 / ((N : ℝ) - 1) ≤ (L + 1) / (((N : ℝ) - L - 1) * (L + 1)) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have he : (L + 1) / (((N : ℝ) - L - 1) * (L + 1)) =
      1 / ((N : ℝ) - L - 1) := by field_simp
  refine ⟨he, ?_⟩
  rw [he]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem expectedNoiseEnvelope_tan_density (N T : ℕ) (hN : 0 < N) (hTN : T < N) :
    (Real.tan (aqAngle N T)) ^ 2 = (T : ℝ) / ((N : ℝ) - T) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (T : ℝ) < N := by exact_mod_cast hTN
  have hx : 0 ≤ (T : ℝ) / N := by positivity
  have hx1 : (T : ℝ) / N ≤ 1 := (div_le_one hn).mpr ht.le
  have hs : (Real.sin (aqAngle N T)) ^ 2 = (T : ℝ) / N := by
    rw [aqAngle, Real.sin_arcsin
      (by linarith [Real.sqrt_nonneg ((T : ℝ) / N)]) (Real.sqrt_le_one.mpr hx1)]
    exact Real.sq_sqrt hx
  have hc : (Real.cos (aqAngle N T)) ^ 2 = 1 - (T : ℝ) / N := by
    nlinarith [Real.sin_sq_add_cos_sq (aqAngle N T)]
  rw [Real.tan_eq_sin_div_cos, div_pow, hs, hc]
  field_simp

theorem expectedNoiseEnvelope_actual_tan_average (N M L : ℕ) [NeZero N]
    (y : ZMod N) (c : ℂ) (hy : y ≠ 0) (hM : 1 ≤ M)
    (hsize : M + L < N) (hc : ‖c‖ ≤ (M : ℝ)) :
    (((N : ℝ) ^ L)⁻¹ * (∑ ω : Fin L → ZMod N,
      ‖c + ∑ i, ZMod.stdAddChar (ω i * y)‖ ^ 2)) /
      ((M : ℝ) + L) ^ 2 * (Real.tan (aqAngle N (M + L))) ^ 2 * aqGain N (M + L) ≤
      ((L : ℝ) + (M : ℝ) ^ 2) /
        (((N : ℝ) - L - M) * ((L : ℝ) + M)) := by
  rw [expectedNoiseEnvelope_tan_density N (M + L) (NeZero.pos N) hsize]
  have he : (N : ℝ) - ((M + L : ℕ) : ℝ) = (N : ℝ) - L - M := by push_cast; ring
  rw [he]
  simpa only [Nat.cast_add] using expectedNoiseEnvelope_actual_average N M L y c hy hM hsize hc

theorem expectedNoiseEnvelopeBridge_answer : ExpectedNoiseEnvelopeBridge := by
  refine ⟨?_, expectedNoiseEnvelope_one_physical_minimum, expectedNoiseEnvelope_actual_tan_average⟩
  intro M N hM hN
  let m : ℝ := M
  let n : ℝ := N
  let A := m * (m - 1)
  let s := Real.sqrt (A * (A + n))
  let t := -m ^ 2 + s
  have hm : 2 ≤ m := by change 2 ≤ (M : ℝ); exact_mod_cast hM
  have hn : 0 < n := by change 0 < (N : ℝ); exact_mod_cast hN
  have hA : 0 < A := mul_pos (by linarith) (by linarith)
  have hAn : 0 < A + n := add_pos hA hn
  have hd : 0 < A * (A + n) := mul_pos hA hAn
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hlo : A < s := (Real.lt_sqrt hA.le).mpr (by nlinarith [mul_pos hA hn])
  have hhi : s < A + n := (Real.sqrt_lt hd.le hAn.le).mpr
    (by nlinarith [mul_pos hAn hn])
  have htm : 0 < t + m := by dsimp [t, A] at *; nlinarith
  have hnt : 0 < n - t - m := by dsimp [t, A] at *; nlinarith
  (try dsimp only)
  refine ⟨⟨?_, ?_⟩, errorExpectationMinimizedAtMinL M N hM hN, ?_⟩
  · change -m < t
    linarith
  · change t < n - m
    linarith
  · change 0 < (t + m ^ 2) / ((n - t - m) * (t + m))
    apply div_pos _ (mul_pos hnt htm)
    change 0 < -m ^ 2 + s + m ^ 2
    linarith

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
