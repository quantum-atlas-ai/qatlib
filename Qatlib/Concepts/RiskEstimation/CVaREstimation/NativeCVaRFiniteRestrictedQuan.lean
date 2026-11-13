/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.CVaREstimation.NativeCVaRFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.NativeVaRFiniteRestrictedQuan

/-!
# Native conditional risk readout and access counts

This module transfers the finite CVaR guarantee to native rational decoding. It bounds the
number of sampling calls on every supported output and records the resulting forward, backward,
query, and gate counts.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `riskNativeCVaRFinite`: The native CVaR procedure satisfies its error guarantee and
  supportwise sampling-call bound under the stated quantile margin conditions; see
  [WoernerEgger2019].
* `risk_native_cvar_access_ledger`: For every supported native CVaR output, the forward and
  backward access counts and counted-circuit query and gate counts have the displayed exact
  formulas, and the number of calls is at most `Nat.clog 2 xs.length + 3`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.PayoffEncoding
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.RiskEstimation.CVaREstimation
open Matrix
open scoped Classical BigOperators ENNReal

/-- The native median tail-numerator estimate has failure probability at most `(8 / 9) ^ r`
outside the combined amplitude, rotation, and decoding error window. -/
theorem risk_native_numerator_tail {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ) (k bits M r : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) (hM : 2 ≤ M) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeSample bits r (riskNumeratorLaw A j loss t k M hA hloss hM))
      (fun z => Real.pi/M+Real.pi^2/(M:ℝ)^2+64/(2:ℝ)^k+(1/2:ℝ)^bits <
        |(z : ℝ)-(∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ))|) ≤ ENNReal.ofReal ((8/9:ℝ)^r) := by
  classical
  have htail := riskTailPayoff_bounds loss t hloss
  have hf : ∀ i, (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro i
    have hh := (rationalPayoffCS_probability _ k (htail i).1 (htail i).2).2.2
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  have hg :=
      risk_mean_good A j (fun i => (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ)) M hA hf hM
  have hb := rational_payoff_weighted_bias A j (riskTailPayoff loss t) k hA htail
  apply risk_native_median_tail
  · positivity
  · apply hg.trans
    apply Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_mono
    intro z hz
    have hh := abs_sub_le (aeEstimate M z)
      (∑ i, BornProb (A *ᵥ Ket j) i*(rationalPayoffValue (riskTailPayoff loss t i) k : ℝ))
      (∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss t i : ℝ))
    linarith

/-- Every supported native CVaR output records at most `Nat.clog 2 xs.length + 3` sampling
calls. -/
theorem risk_native_cvar_support_calls {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q eps : ℚ)
    (k bits M r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) (hM : 2 ≤ M) :
    ∀ z ∈ (riskNativeCVaR A j loss xs q eps k bits M r hA hloss hM).support,
      z.2.2 ≤ Nat.clog 2 xs.length+3 := by
  intro z hz
  unfold riskNativeCVaR at hz
  obtain ⟨w, hw, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
  obtain ⟨phat, _, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
  obtain ⟨muhat, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  subst z
  have hh := risk_native_var_support_calls A j loss xs q bits M r hA hM w hw
  (try dsimp only)
  omega

/-- The native CVaR procedure satisfies its error guarantee and supportwise sampling-call bound
under the stated quantile margin conditions; see [WoernerEgger2019]. -/
theorem riskNativeCVaRFinite : NativeCVaRFiniteRestricted := by
  intro I _ _ A j loss xs q eps k bits M r v hA hM hloss hxs hs hsupport hq0 hq1 heps hv hwindow habove hbelow hp
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (riskNativeCVaR A j loss xs q eps k bits M r hA hloss hM) _ ≤ _ ∧ _
  have hepsR : (0 : ℝ) < eps := by exact_mod_cast heps
  classical
  let p := riskCDF A j loss (xs.getD v 0)
  let mu := ∑ i, BornProb (A *ᵥ Ket j) i*(riskTailPayoff loss (xs.getD v 0) i : ℝ)
  let rho : ℝ≥0∞ := ENNReal.ofReal ((8/9:ℝ)^r)
  let E :=
      fun z : ℕ × ℚ × ℕ => z.1 ≠ v ∨ 4*(eps : ℝ)/p < |(z.2.1 : ℝ)-riskTailMean A j loss (xs.getD v 0)|
  have hbase : Real.pi/M+Real.pi^2/(M:ℝ)^2+(1/2:ℝ)^bits ≤ (eps : ℝ) := by
    have hb : (0:ℝ) ≤ 64/(2:ℝ)^k := by positivity
    linarith
  have hden : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeSample bits r (riskCDFLaw A j loss (xs.getD v 0) M hA hM))
      (fun phat => (eps : ℝ) < |(phat : ℝ)-p|) ≤ rho := by
    apply le_trans (risk_event_mono _ (fun phat hh => lt_of_le_of_lt hbase hh))
    exact riskNativeCDFReadout I A j loss (xs.getD v 0) bits M r hA hM
  have hnum : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeSample bits r (riskNumeratorLaw A j loss (xs.getD v 0) k M hA hloss hM))
      (fun muhat => (eps : ℝ) < |(muhat : ℝ)-mu|) ≤ rho := by
    apply le_trans (risk_event_mono _ (fun muhat hh => lt_of_le_of_lt hwindow hh))
    exact risk_native_numerator_tail A j loss (xs.getD v 0) k bits M r hA hloss hM
  have hmub := risk_tail_numerator_bounds A j loss (xs.getD v 0) hloss
  have hgood : ∀ z : ℕ × ℕ, ¬z.1 ≠ v →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        ((riskNativeSample bits r (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM)).bind (fun phat =>
          (riskNativeSample bits r (riskNumeratorLaw A j loss (xs.getD z.1 0) k M hA hloss hM)).map
            (fun muhat => (z.1,muhat/max eps phat,z.2+2)))) E ≤ rho+rho := by
    intro z hz
    have hzv : z.1 = v := not_ne_iff.mp hz
    rw [hzv]
    apply le_trans (risk_bind_failure _ _ (fun phat : ℚ => (eps : ℝ) < |(phat : ℝ)-p|) E rho ?_)
      (add_le_add hden le_rfl)
    intro phat hphat
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    apply le_trans (risk_event_mono _ ?_) hnum
    intro muhat hout
    by_contra hn
    have hratio := risk_ratio_error p mu (phat : ℝ) (muhat : ℝ) (eps : ℝ) hepsR hp hmub.1 hmub.2
      (le_of_not_gt hphat) (le_of_not_gt hn)
    have ht : riskTailMean A j loss (xs.getD v 0) = mu/p := riskTailMean_eq A j loss (xs.getD v 0)
    dsimp only [E] at hout
    simp only [Rat.cast_div, Rat.cast_max, ht] at hout
    rcases hout with hout | hout
    · exact hout rfl
    · exact not_lt_of_ge hratio hout
  have hvar : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeVaR A j loss xs q bits M r hA hM)
      (fun z => z.1 ≠ v) ≤ ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9:ℝ)^r) := by
    apply le_trans (risk_event_mono _ (risk_stable_wrong_index A j loss xs (q : ℝ)
      (eps : ℝ) v hs hv habove hbelow))
    exact (riskNativeVaRFinite I A j loss xs q eps bits M r hA hM hxs hs hsupport
      hq0 hq1 heps hbase).1
  have hh := risk_bind_failure (riskNativeVaR A j loss xs q bits M r hA hM)
    (fun z => (riskNativeSample bits r (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM)).bind (fun phat =>
      (riskNativeSample bits r (riskNumeratorLaw A j loss (xs.getD z.1 0) k M hA hloss hM)).map
        (fun muhat => (z.1,muhat/max eps phat,z.2+2)))) (fun z => z.1 ≠ v) E (rho+rho) hgood
  refine ⟨?_, risk_native_cvar_support_calls A j loss xs q eps k bits M r hA hloss hM⟩
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeVaR A j loss xs q bits M r hA hM) (fun z => z.1 ≠ v)+(rho+rho) := hh
    _ ≤ ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9:ℝ)^r)+(rho+rho) := add_le_add hvar le_rfl
    _ = ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9:ℝ)^r) := by
      dsimp [rho]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- For every supported native CVaR output, the forward and backward access counts and
counted-circuit query and gate counts have the displayed exact formulas, and the number of
calls is at most `Nat.clog 2 xs.length + 3`. -/
theorem risk_native_cvar_access_ledger {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q eps t : ℚ)
    (k bits M r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) (hM : 2 ≤ M)
    (z : ℕ × ℚ × ℕ)
    (hz : z ∈ (riskNativeCVaR A j loss xs q eps k bits M r hA hloss hM).support) :
    z.2.2*(2*r+1)*aeForwardAccesses (aeAccessWord (I := I × Bool) M) = z.2.2*(2*r+1)*M ∧
    z.2.2*(2*r+1)*aeBackwardAccesses (aeAccessWord (I := I × Bool) M) = z.2.2*(2*r+1)*(M-1) ∧
    z.2.2*(2*r+1)*QueryCount (countedAECircuit M (payoffPreparation A (riskCDFPayoff loss t)) (j,false)) =
      z.2.2*(2*r+1)*(M-1) ∧
    z.2.2*(2*r+1)*GateCount (countedAECircuit M (payoffPreparation A (riskCDFPayoff loss t)) (j,false)) =
      z.2.2*(2*r+1)*(5*(M-1)+3) ∧
    QueryCount (countedAECircuit M (payoffPreparation A
      (fun i => (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ))) (j,false)) = M-1 ∧
    GateCount (countedAECircuit M (payoffPreparation A
      (fun i => (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ))) (j,false)) = 5*(M-1)+3 ∧
    z.2.2 ≤ Nat.clog 2 xs.length+3 := by
  have hc := risk_native_readout_charges (payoffPreparation A (riskCDFPayoff loss t))
    (j,false) M r z.2.2 hM
  have hn := prepared_ae_access_ledger M (by omega : 0 < M)
    (payoffPreparation A (fun i => (rationalPayoffValue (riskTailPayoff loss t i) k : ℝ))) (j,false)
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hn.1, hn.2.1,
    risk_native_cvar_support_calls A j loss xs q eps k bits M r hA hloss hM z hz⟩

end Qatlib.Concepts.RiskEstimation.CVaREstimation
