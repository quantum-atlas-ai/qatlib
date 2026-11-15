/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCayleyTransport
public import Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.LaurentPolys.ProfileFftBound.PositiveLaurentOuterFactor

open Polynomial Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- A Laurent profile with a strictly positive unit circle lower bound has a polynomial factor
of degree at most `m`, positive real at zero and without closed disk zeros, whose squared
modulus equals the profile on the unit circle. -/
theorem positive_laurent_outer_factor_exists :
    ∀ (m : ℕ) (c : Fin (m + 1) → ℝ) (κ : ℝ), 0 < κ →
      (∀ z : ℂ, ‖z‖ = 1 → κ ≤ (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z).re) →
      ∃ R : Polynomial ℂ, R.natDegree ≤ m ∧
        0 < (R.eval 0).re ∧ (R.eval 0).im = 0 ∧
        (∀ z : ℂ, ‖z‖ ≤ 1 → R.eval z ≠ 0) ∧
        (∀ z : ℂ, ‖z‖ = 1 → Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z = ((‖R.eval z‖ ^ 2 : ℝ) : ℂ)) := by
  intro m c κ hκ hc
  have hnonnegative : Qatlib.Concepts.OrderedOracle.TiSdpBridge.complexLaurentNonnegative (fun i => (c i : ℂ)) := by
    constructor
    · simp [Qatlib.Concepts.OrderedOracle.TiSdpBridge.complexLaurentCoefficient]
    · intro z hz
      rw [Qatlib.Concepts.OrderedOracle.TiSdpBridge.complexLaurentEval_ofReal]
      exact hκ.le.trans (hc z hz)
  obtain ⟨A, hAd, hAc, _⟩ :=
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.complex_laurent_circle_factor_polynomial (fun i => (c i : ℂ)) hnonnegative
  have hcircleA : ∀ z : ℂ, ‖z‖ = 1 →
      Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z = ((‖A.eval z‖ ^ 2 : ℝ) : ℂ) := by
    intro z hz
    simpa only [Qatlib.Concepts.OrderedOracle.TiSdpBridge.complexLaurentEval_ofReal] using
        hAc z hz
  have hAn : ∀ z : ℂ, ‖z‖ = 1 → A.eval z ≠ 0 := by
    intro z hz hzero
    have hzeroProfile : (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z).re = 0 := by
      simpa [hzero] using congrArg Complex.re (hcircleA z hz)
    have hbound := hc z hz
    linarith
  obtain ⟨B, hBd, hBn, hBc⟩ :=
      Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT.polynomial_outer_circle_factor A hAn
  have hB0 : B.eval 0 ≠ 0 := hBn 0 (by simp)
  let q : ℂ := (‖B.eval 0‖ : ℂ) / B.eval 0
  have hqnorm : ‖q‖ = 1 := by
    simp only [q, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hB0)
  have hqne : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hqnorm]; norm_num)
  have hq0 : q * B.eval 0 = (‖B.eval 0‖ : ℂ) := div_mul_cancel₀ _ hB0
  refine ⟨C q * B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_C_mul hqne]
    exact hBd.trans (by simpa using hAd)
  · simp only [eval_mul, eval_C, hq0, Complex.ofReal_re]
    exact norm_pos_iff.mpr hB0
  · simp only [eval_mul, eval_C, hq0, Complex.ofReal_im]
  · intro z hz
    rw [eval_mul, eval_C]
    exact mul_ne_zero hqne (hBn z hz)
  · intro z hz
    simp only [eval_mul, eval_C, norm_mul, hqnorm, one_mul, hBc z hz]
    exact hcircleA z hz

end Qatlib.Concepts.LaurentPolys.ProfileFftBound.PositiveLaurentOuterFactor
