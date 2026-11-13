/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedReadoutStat
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedPayoffMassQuan
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationTaylorBiasQuan
import Qatlib.Concepts.RiskEstimation.CDFEstimation.NativeCDFReadoutRestrictedQuan

/-!
# Readout of expanded polynomial preparation

This module combines the exact flag-mass identity for expanded preparation with polynomial
rotation bias and native median concentration. It proves a readout guarantee for polynomial
payoffs evaluated on binary data registers.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `polyFigTwoExpandedReadout`: The rescaled native median of the expanded Figure 2 law estimates
  the polynomial payoff mean within `riskPolyReadoutWindow` except with probability at most `(8
  / 9) ^ r`; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline
set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix
open scoped Classical BigOperators ENNReal

/-- Event probability is monotone under pointwise inclusion of events. -/
private theorem event_le_of_subset {X : Type*} (p : PMF X) (E F : X → Prop)
    (h : ∀ x, E x → F x) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p F := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : E x
  · simp only [if_pos hx, if_pos (h x hx), mul_one]
    exact le_rfl
  · simp only [if_neg hx, mul_zero]
    positivity

/-- For unitary preparation and payoffs in `[0, 1]`, the polynomial rotation mean differs from
the affine target mean by at most `riskArcsinTail u * c ^ (2 * u + 3) / 2` when `0 < c ≤ 1`. -/
private theorem polynomial_payoff_mean_bias
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (u : ℕ) (c : ℝ) (hA : A ∈ unitaryGroup I ℂ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) (hc : 0 < c) (hc1 : c ≤ 1) :
    |(∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * Real.sin (c * riskSinTaylor u c (f i) + Real.pi / 4) ^ 2) -
      (c * ((∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * f i) - 1 / 2) + 1 / 2)| ≤
        riskArcsinTail u * c ^ (2 * u + 3) / 2 := by
  let p := fun i : I => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i
  let g := fun i : I => Real.sin (c * riskSinTaylor u c (f i) + Real.pi / 4) ^ 2
  let B := riskArcsinTail u * c ^ (2 * u + 3) / 2
  have hp (i : I) : 0 ≤ p i := sq_nonneg _
  have hs : ∑ i, p i = 1 := normalized_applyGate hA (normalized_ket j)
  have he : (∑ i, p i * g i) - (c * ((∑ i, p i * f i) - 1 / 2) + 1 / 2) =
      ∑ i, p i * (g i - (c * (f i - 1 / 2) + 1 / 2)) := by
    have ht (i : I) : p i * (g i - (c * (f i - 1 / 2) + 1 / 2)) =
        p i * g i - c * (p i * f i) + (c / 2 - 1 / 2) * p i := by ring
    rw [Finset.sum_congr rfl (fun i _ => ht i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hs]
    ring
  change |(∑ i, p i * g i) - (c * ((∑ i, p i * f i) - 1 / 2) + 1 / 2)| ≤ B
  rw [he]
  calc
    _ ≤ ∑ i, |p i * (g i - (c * (f i - 1 / 2) + 1 / 2))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i * |g i - (c * (f i - 1 / 2) + 1 / 2)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hp i)]
    _ ≤ ∑ i, p i * B := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
          (riskPolyRotationTaylorBias u c (f i) hc hc1 (hf i).1 (hf i).2) (hp i)
    _ = B := by rw [← Finset.sum_mul, hs, one_mul]

/-- The rescaled native median of the expanded Figure 2 law estimates the polynomial payoff mean
within `riskPolyReadoutWindow` except with probability at most `(8 / 9) ^ r`; see
[WoernerEgger2019]. -/
theorem polyFigTwoExpandedReadout : PolyFigTwoExpandedReadout := by
  intro n A j u c fp M r bits hA hM hf hc hc1
  classical
  let f := fun x : Reg n => fp.eval (figTwoRegEval x : ℝ)
  let p := figTwoExpandedLaw n A j u c fp M hA hM
  let g := fun i : Reg n => Real.sin (c * riskSinTaylor u c (f i) + Real.pi / 4) ^ 2
  let μ := ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * f i
  let ν := ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * g i
  let e := Real.pi / M + Real.pi ^ 2 / (M : ℝ) ^ 2
  let d := (1 / 2 : ℝ) ^ bits
  let B := riskArcsinTail u * c ^ (2 * u + 3) / 2
  have he : 0 ≤ e := by dsimp [e]; positivity
  let Bprep := figTwoExpandedPreparation n A u c fp
  let S := figTwoGoodSet n
  let jprep := figTwoStart n j
  have hB := figTwoExpandedPreparation_unitary (u := u) (c := c) (fp := fp) hA
  have hmass : MeasureProb (Bprep *ᵥ Qatlib.Foundations.PureStateMath.Ket jprep) S = ν :=
    polyFigTwoExpandedPayoffMass n A j u c fp hA
  have hν0 : 0 ≤ ν := hmass ▸ measureProb_nonneg _ _
  have hν1 : ν ≤ 1 := hmass ▸ measureProb_le_one (normalized_applyGate hB (normalized_ket _)) _
  have hs : Real.sqrt (ν*(1-ν)) ≤ 1/2 := by
    nlinarith [Real.sq_sqrt (mul_nonneg hν0 (by linarith : 0 ≤ 1-ν)),
      sq_nonneg (ν-1/2), Real.sqrt_nonneg (ν*(1-ν))]
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hw : 2*Real.pi*Real.sqrt (ν*(1-ν))/(M : ℝ) ≤ Real.pi/M := by
    apply (div_le_div_iff_of_pos_right hMr).mpr
    nlinarith [Real.pi_pos]
  have hgood : 8 / Real.pi ^ 2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => |aeEstimate M z - ν| ≤ e) := by
    have hg : 8 / Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => |aeEstimate M z - ν| ≤
        2*Real.pi*Real.sqrt (ν*(1-ν))/(M : ℝ)+Real.pi^2/(M : ℝ)^2) := by
      simpa only [Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass, p, figTwoExpandedLaw, preparedAAState, ApplyGate, hmass]
        using! (prepared_ae_bhmt_error_and_endpoints M hM Bprep jprep S hB).1
    apply hg.trans
    apply Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_mono
    intro z hz
    exact hz.trans (add_le_add hw le_rfl)
  have hmedian := risk_native_median_tail p bits r ν e he hgood
  have hbias : |ν - (c * (μ - 1 / 2) + 1 / 2)| ≤ B :=
    polynomial_payoff_mean_bias A j f u c hA hf hc hc1
  have hwindow : c * riskPolyReadoutWindow u c M bits = e + d + B := by
    unfold riskPolyReadoutWindow
    dsimp [e, d, B]
    rw [show 2 * u + 3 = (2 * u + 2) + 1 by omega, pow_succ]
    field_simp [hc.ne']
    ring
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((riskNativeSample bits r p).map
    (fun z : ℚ => ((z : ℝ) - 1 / 2) / c + 1 / 2))
    (fun w => riskPolyReadoutWindow u c M bits < |w - μ|) ≤ _
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply le_trans _ hmedian
  apply event_le_of_subset
  intro z hz
  by_contra hbad
  have hclose : |(z : ℝ) - ν| ≤ e + d := le_of_not_gt hbad
  have ht := (abs_sub_le (z : ℝ) ν (c * (μ - 1 / 2) + 1 / 2)).trans (add_le_add hclose hbias)
  have hid : c * (((z : ℝ) - 1 / 2) / c + 1 / 2 - μ) =
      (z : ℝ) - (c * (μ - 1 / 2) + 1 / 2) := by field_simp [hc.ne']; ring
  have habs : c * |((z : ℝ) - 1 / 2) / c + 1 / 2 - μ| =
      |(z : ℝ) - (c * (μ - 1 / 2) + 1 / 2)| := by
    rw [← hid, abs_mul, abs_of_pos hc]
  have hscaled := mul_lt_mul_of_pos_left hz hc
  rw [hwindow, habs] at hscaled
  exact (not_lt_of_ge ht) hscaled

end Qatlib.Concepts.RiskEstimation.PolyReadout
