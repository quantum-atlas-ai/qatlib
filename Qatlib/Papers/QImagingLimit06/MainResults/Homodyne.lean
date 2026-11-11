/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagingLimit06.MainResults.FisherCore

/-!
# Homodyne signal and resolution formulas

The functions `homodyneSignal`, `homodyneShotNoise`, and `homodyneSqueezedNoise` describe the
scalar signal and noise model. The module computes the ordinary and squeezed signal-to-noise
ratios and their positive unit-ratio resolutions. See [DelaubertEtAl2008] for the paper context.

## Main statements

* `homodyne_snr`: For positive `N`, `NLO`, and `b`, the homodyne squared signal divided by shot
  noise equals `4N p²/b²`.
* `homodyne_pmin`: The positive unit signal-to-noise resolution for ordinary homodyne detection
  is `b/(2√N)`.
* `squeezed_homodyne_pmin`: The positive unit signal-to-noise resolution for squeezed homodyne
  detection is `bσ/(2√N)`.

## References

* [Delaubert et al., 2008][DelaubertEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QImagingLimit06.MainResults

/-- The homodyne signal `2 * sqrt(N * NLO) * p / b`. -/
def homodyneSignal (N NLO p b : ℝ) : ℝ :=
  2 * Real.sqrt (N * NLO) * (p / b)

/-- The shot noise power equal to the local oscillator parameter `NLO`. -/
def homodyneShotNoise (NLO : ℝ) : ℝ := NLO

/-- The squeezed noise power `NLO * σ²`. -/
def homodyneSqueezedNoise (NLO σ : ℝ) : ℝ := NLO * σ ^ 2

/-- For positive `N`, `NLO`, and `b`, the homodyne squared signal divided by shot noise equals
`4N p²/b²`. See [DelaubertEtAl2008]. -/
theorem homodyne_snr {N NLO p b : ℝ} (hN : 0 < N) (hNLO : 0 < NLO)
    (hb : 0 < b) :
    (homodyneSignal N NLO p b) ^ 2 / homodyneShotNoise NLO = 4 * N * p ^ 2 / b ^ 2 := by
  unfold homodyneSignal homodyneShotNoise
  have hsq : Real.sqrt (N * NLO) ^ 2 = N * NLO := Real.sq_sqrt (by positivity)
  have hnum : (2 * Real.sqrt (N * NLO) * (p / b)) ^ 2 =
      4 * (N * NLO) * (p / b) ^ 2 := by
    rw [mul_pow, mul_pow, hsq]
    ring
  rw [hnum]
  have hb0 : b ≠ 0 := hb.ne'
  have hNLO0 : NLO ≠ 0 := hNLO.ne'
  field_simp

/-- The positive unit signal-to-noise resolution for ordinary homodyne detection is `b/(2√N)`.
See [DelaubertEtAl2008]. -/
theorem homodyne_pmin {N b p : ℝ} (hN : 0 < N) (hb : 0 < b) (hp : 0 < p)
    (hSNR : 4 * N * p ^ 2 / b ^ 2 = 1) : p = b / (2 * Real.sqrt N) :=
  pmin_of_snr_one hN hb hp hSNR

/-- For positive parameters, the squared homodyne signal divided by squeezed noise equals `4N
p²/(b²σ²)`. See [DelaubertEtAl2008]. -/
theorem squeezed_homodyne_snr {N NLO p b σ : ℝ} (hN : 0 < N)
    (hNLO : 0 < NLO) (hb : 0 < b) (hσ : 0 < σ) :
    (homodyneSignal N NLO p b) ^ 2 / homodyneSqueezedNoise NLO σ =
      4 * N * p ^ 2 / (b ^ 2 * σ ^ 2) := by
  unfold homodyneSignal homodyneSqueezedNoise
  have hsq : Real.sqrt (N * NLO) ^ 2 = N * NLO := Real.sq_sqrt (by positivity)
  have hnum : (2 * Real.sqrt (N * NLO) * (p / b)) ^ 2 =
      4 * (N * NLO) * (p / b) ^ 2 := by
    rw [mul_pow, mul_pow, hsq]
    ring
  rw [hnum]
  have hb0 : b ≠ 0 := hb.ne'
  have hNLO0 : NLO ≠ 0 := hNLO.ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  field_simp

/-- The positive unit signal-to-noise resolution for squeezed homodyne detection is `bσ/(2√N)`.
See [DelaubertEtAl2008]. -/
theorem squeezed_homodyne_pmin {N b σ p : ℝ} (hN : 0 < N) (hb : 0 < b)
    (hσ : 0 < σ) (hp : 0 < p) (hSNR : 4 * N * p ^ 2 / (b ^ 2 * σ ^ 2) = 1) :
    p = b * σ / (2 * Real.sqrt N) := by
  have hc : 0 < b * σ := mul_pos hb hσ
  have hSNR' : 4 * N * p ^ 2 / (b * σ) ^ 2 = 1 := by
    rwa [mul_pow]
  exact pmin_of_snr_one hN hc hp hSNR'

end Qatlib.Papers.QImagingLimit06.MainResults
