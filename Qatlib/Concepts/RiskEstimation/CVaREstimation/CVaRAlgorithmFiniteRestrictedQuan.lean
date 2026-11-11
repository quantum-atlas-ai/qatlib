/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.StableQuantileFiniteRestrictedQuan

/-!
# Finite conditional risk estimation

This module bounds the numerator and ratio errors used in finite conditional risk estimation. It
combines quantile bisection, CDF estimation, and a bounded tail payoff to prove
`riskCVaRAlgorithmFinite` under the stated separation and denominator conditions.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `risk_ratio_error`: If numerator and denominator errors are at most positive `eps`, with `0 ≤
  mu ≤ p` and `2 * eps < p`, the clipped ratio error is at most `4 * eps / p`.
* `riskCVaRAlgorithmFinite`: The finite CVaR procedure satisfies its quantile and
  conditional-mean error guarantee under the specified CDF margin conditions; see
  [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.PayoffEncoding
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.RiskEstimation.CVaREstimation
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- For losses in `[0, 1]`, every thresholded tail payoff lies in `[0, 1]`. -/
theorem riskTailPayoff_bounds {I : Type} (loss : I → ℚ) (t : ℚ)
    (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) : ∀ i, 0 ≤ riskTailPayoff loss t i ∧ riskTailPayoff loss t i ≤ 1 := by
  intro i; dsimp [riskTailPayoff]; split <;> simp_all

/-- The tail mean is the Born-weighted tail payoff numerator divided by the CDF mass. -/
theorem riskTailMean_eq {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ) :
    riskTailMean A j loss t = (∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ))/riskCDF A j loss t := by
  unfold riskTailMean
  rw [riskKet_eq (fun a b => Classical.propDecidable (a = b)) inferInstance j]

/-- For losses in `[0, 1]`, the tail payoff numerator is nonnegative and at most the CDF mass. -/
theorem risk_tail_numerator_bounds {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ) (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) :
    0 ≤ (∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ)) ∧
    (∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ)) ≤ riskCDF A j loss t := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (bornProb_nonneg _ _) (by exact_mod_cast (riskTailPayoff_bounds loss t hloss i).1)), ?_⟩
  rw [riskCDF_eq]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (bornProb_nonneg _ _)
  dsimp [riskTailPayoff, riskCDFPayoff]
  split_ifs
  · exact_mod_cast (hloss i).2
  · norm_num

/-- The median tail-numerator estimate exceeds error `π / M + π² / M² + 64 / 2 ^ k` with
probability at most `(8 / 9) ^ r`. -/
theorem risk_numerator_tail {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ) (k M r : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) (hM : 2 ≤ M) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF (riskNumeratorLaw A j loss t k M hA hloss hM) r)
      (fun z => Real.pi/M+Real.pi^2/(M:ℝ)^2+64/(2:ℝ)^k <
        |z-(∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ))|) ≤ ENNReal.ofReal ((8/9:ℝ)^r) := by
  classical
  have htail := riskTailPayoff_bounds loss t hloss
  have hf : ∀ i, (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro i
    have hh := (rationalPayoffCS_probability _ k (htail i).1 (htail i).2).2.2
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  have hg :=
      risk_mean_good A j (fun i => (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ)) M hA hf hM
  have hb := rational_payoff_weighted_bias A j (riskTailPayoff loss t) k hA htail
  apply risk_median_tail
  · positivity
  · apply hg.trans
    apply Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_mono
    intro z hz
    have hh := abs_sub_le (aeEstimate M z)
      (∑ i, BornProb (A *ᵥ Ket j) i*(rationalPayoffValue (riskTailPayoff loss t i) k : ℝ))
      (∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ))
    linarith

/-- If numerator and denominator errors are at most positive `eps`, with `0 ≤ mu ≤ p` and `2 *
eps < p`, the clipped ratio error is at most `4 * eps / p`. -/
theorem risk_ratio_error (p mu phat muhat eps : ℝ) (heps : 0 < eps) (hp : 2*eps < p)
    (hmu : 0 ≤ mu) (hmup : mu ≤ p) (hphat : |phat-p| ≤ eps) (hmuhat : |muhat-mu| ≤ eps) :
    |muhat/max eps phat-mu/p| ≤ 4*eps/p := by
  have hp0 : 0 < p := by linarith
  have hphi := abs_le.mp hphat
  have hphi0 : 0 < phat := by linarith
  have hmax : max eps phat = phat := max_eq_right (by linarith)
  rw [hmax]
  have heq : muhat/phat-mu/p = (p*(muhat-mu)+mu*(p-phat))/(phat*p) := by field_simp; ring
  rw [heq, abs_div, abs_of_pos (mul_pos hphi0 hp0)]
  apply (div_le_iff₀ (mul_pos hphi0 hp0)).mpr
  calc
    _ ≤ |p*(muhat-mu)|+|mu*(p-phat)| := abs_add_le _ _
    _ = p*|muhat-mu|+mu*|phat-p| := by rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_nonneg hmu, abs_sub_comm p phat]
    _ ≤ p*eps+mu*eps := add_le_add (mul_le_mul_of_nonneg_left hmuhat hp0.le) (mul_le_mul_of_nonneg_left hphat hmu)
    _ ≤ 2*p*eps := by nlinarith
    _ ≤ 4*eps*phat := by nlinarith
    _ = (4*eps/p)*(phat*p) := by field_simp

/-- The finite CVaR procedure satisfies its quantile and conditional-mean error guarantee under
the specified CDF margin conditions; see [WoernerEgger2019]. -/
theorem riskCVaRAlgorithmFinite : CVaRAlgorithmFiniteRestricted := by
  intro I _ _ A j loss xs q eps k M r v hA hloss hM hxs hs hsupport hq0 hq1 heps hv hwindow habove hbelow hp
  classical
  let p := riskCDF A j loss (xs.getD v 0)
  let mu := ∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss (xs.getD v 0) i : ℝ)
  let rho : ℝ≥0∞ := ENNReal.ofReal ((8/9:ℝ)^r)
  let E := fun z : ℕ × ℝ × ℕ => z.1 ≠ v ∨ 4*eps/p < |z.2.1-riskTailMean A j loss (xs.getD v 0)|
  have hbase : Real.pi/M+Real.pi^2/(M:ℝ)^2 ≤ eps := by
    have hb : (0:ℝ) ≤ 64/(2:ℝ)^k := by positivity
    linarith
  have hden : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF (riskCDFLaw A j loss (xs.getD v 0) M hA hM) r)
      (fun phat => eps < |phat-p|) ≤ rho := by
    apply le_trans (risk_event_mono _ (fun phat hh => lt_of_le_of_lt hbase hh))
    exact riskReadoutMedianFinite I A j loss (xs.getD v 0) M r hA hM
  have hnum : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF (riskNumeratorLaw A j loss (xs.getD v 0) k M hA hloss hM) r)
      (fun muhat => eps < |muhat-mu|) ≤ rho := by
    apply le_trans (risk_event_mono _ (fun muhat hh => lt_of_le_of_lt hwindow hh))
    exact risk_numerator_tail A j loss (xs.getD v 0) k M r hA hloss hM
  have hmub := risk_tail_numerator_bounds A j loss (xs.getD v 0) hloss
  have hgood : ∀ z : ℕ × ℕ, ¬z.1 ≠ v →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        ((riskMedianPMF (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM) r).bind (fun phat =>
          (riskMedianPMF (riskNumeratorLaw A j loss (xs.getD z.1 0) k M hA hloss hM) r).map
            (fun muhat => (z.1,muhat/max eps phat,z.2+2)))) E ≤ rho+rho := by
    intro z hz
    have hzv : z.1 = v := not_ne_iff.mp hz
    rw [hzv]
    apply le_trans (risk_bind_failure _ _ (fun phat => eps < |phat-p|) E rho ?_)
      (add_le_add hden le_rfl)
    intro phat hphat
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    apply le_trans (risk_event_mono _ ?_) hnum
    intro muhat hout
    by_contra hn
    have hratio := risk_ratio_error p mu phat muhat eps heps hp hmub.1 hmub.2
      (le_of_not_gt hphat) (le_of_not_gt hn)
    have ht : riskTailMean A j loss (xs.getD v 0) = mu/p := riskTailMean_eq A j loss (xs.getD v 0)
    dsimp only [E] at hout
    rw [ht] at hout
    rcases hout with hout | hout
    · exact hout rfl
    · exact not_lt_of_ge hratio hout
  have hvar := riskStableQuantileFinite I A j loss xs q eps M r v hA hM hxs hs hsupport
    hq0 hq1 heps hv hbase habove hbelow
  have hh := risk_bind_failure (riskVaR A j loss xs q M r hA hM)
    (fun z => (riskMedianPMF (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM) r).bind (fun phat =>
      (riskMedianPMF (riskNumeratorLaw A j loss (xs.getD z.1 0) k M hA hloss hM) r).map
        (fun muhat => (z.1,muhat/max eps phat,z.2+2)))) (fun z => z.1 ≠ v) E (rho+rho) hgood
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskVaR A j loss xs q M r hA hM) (fun z => z.1 ≠ v)+(rho+rho) := hh
    _ ≤ ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9:ℝ)^r)+(rho+rho) := add_le_add hvar le_rfl
    _ = ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9:ℝ)^r) := by
      dsimp [rho]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
end Qatlib.Concepts.RiskEstimation.CVaREstimation
