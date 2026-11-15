/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionStat
public import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch

@[expose] public section
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false

namespace Qatlib.Papers.SpatialWalk15.SpectralSearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
open Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionStat
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The spectral search Hamiltonian is Hermitian. -/
theorem spectral_search_hamiltonian_isHermitian
    {I : Type} [Fintype I] [DecidableEq I]
    (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ) (w : QState I) :
    (searchHamiltonian V lam r w).IsHermitian := by
  unfold searchHamiltonian
  exact (((spectralHamiltonian_isHermitian V lam).smul (IsSelfAdjoint.all (1+r))).sub
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all r))).add (rankOneProjector_isHermitian w)

set_option maxHeartbeats 1000000 in

/-- The spectral gap and overlap hypotheses guarantee a search parameter and bounded evolution
time attaining the stated target overlap probability. -/
theorem spectral_search_sufficient_condition : SpectralSearchSufficientCondition := by
  intro κ _ _ _ V lam σ c w hV hlamσ hlamc hc0 hc1 hw hεpos hεbound
  let ε := ‖Inner w (fun j => V j σ)‖
  let ν :=
      Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch.spectralGapParam c
  let s : QState κ := fun j => V j σ
  have hν : 0 < ν :=
      Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch.spectral_gap_param_pos hc0 hc1
  have hhalf : ε ≤ 1/2 := (le_min_iff.1 hεbound).2
  have hεlt : ε < 1 := by linarith
  obtain ⟨r, hrlo, hrhi, hcal⟩ := rank_one_calibration_exists V lam σ c w
    hV hlamσ hlamc hc0 hc1 hw hεlt
  obtain ⟨δp, δm, hpLo, hpHi, hmLo, hmHi, hrootp, hrootm⟩ :=
    rank_one_two_level_positioning V lam σ c r w hV hlamσ hlamc hc0 hc1 hw
      hrlo hrhi hεpos hεbound hcal
  change ε*Real.sqrt (ν/2) ≤ δp at hpLo
  change δp ≤ ν/2 at hpHi
  change ε*Real.sqrt (ν/2) ≤ δm at hmLo
  change δm ≤ ν/2 at hmHi
  have hp : 0 < δp := (mul_pos hεpos (Real.sqrt_pos.2 (by linarith))).trans_le hpLo
  have hm : 0 < δm := (mul_pos hεpos (Real.sqrt_pos.2 (by linarith))).trans_le hmLo
  have hgap (i : κ) (hi : i ≠ σ) : ν ≤ 1-rescaledEigenvalue lam r i :=
    rescaled_spectral_gap_lower_bound lam c r i hc0 hc1 hrlo (hlamc i hi)
  have hσ : rescaledEigenvalue lam r σ = 1 := by unfold rescaledEigenvalue; rw [hlamσ]; ring
  have hnep (i : κ) : 1+δp ≠ rescaledEigenvalue lam r i := by
    by_cases hi : i = σ
    · subst i; rw [hσ]; linarith
    · linarith [hgap i hi]
  have hnem (i : κ) : 1-δm ≠ rescaledEigenvalue lam r i := by
    by_cases hi : i = σ
    · subst i; rw [hσ]; linarith
    · linarith [hgap i hi]
  let H := searchHamiltonian V lam r w
  let up := rankOneSecularState V lam r w (1+δp)
  let um := rankOneSecularState V lam r w (1-δm)
  let k := rankOneResonantCoefficient V w σ δp δm
  let t := Real.pi/(δp+δm)
  have hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up :=
    rank_one_secular_state_eigen V lam r w (1+δp) hV hnep hrootp
  have hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um :=
    rank_one_secular_state_eigen V lam r w (1-δm) hV hnem hrootm
  have hwu : Inner w up = 1 := by rw [rankOneSecularState_overlap, hrootp, Complex.ofReal_one]
  have hwm : Inner w um = 1 := by rw [rankOneSecularState_overlap, hrootm, Complex.ofReal_one]
  have hsmall : ε ^ 2 ≤ ν ^ 3/64 := by
    have hb : ε ≤ ν ^ (3/2 : ℝ)/8 := (le_min_iff.1 hεbound).1
    have hpw : (ν ^ (3/2 : ℝ)) ^ 2 = ν ^ 3 := by
      rw [← Real.rpow_two, ← Real.rpow_mul hν.le]
      norm_num
    have hz : 0 ≤ ν ^ (3/2 : ℝ) := Real.rpow_nonneg hν.le _
    nlinarith
  have hrem : ‖toEuclidean_fromVec (s-k • (up-um))‖ ^ 2 ≤ ν/16 := by
    have hr := rank_one_resonant_remainder_bound V lam w σ r ν δp δm hV hlamσ hw
      hεpos hhalf hν hp hm hpHi hmHi hgap hcal hrootp hrootm
    change ‖toEuclidean_fromVec (s-k • (up-um))‖ ^ 2 ≤ 4*ε ^ 2/ν ^ 2 at hr
    apply hr.trans
    apply (div_le_iff₀ (sq_pos_of_pos hν)).2
    nlinarith only [hsmall]
  have hkbase : Real.sqrt (ν/2) ≤ 2*‖k‖ := by
    rw [rankOneResonantCoefficient_norm V w σ δp δm hp hm]
    change Real.sqrt (ν/2) ≤ 2*(δp*δm/(ε*(δp+δm)))
    rw [show 2*(δp*δm/(ε*(δp+δm))) = 2*δp*δm/(ε*(δp+δm)) by ring]
    apply (le_div_iff₀ (mul_pos hεpos (add_pos hp hm))).2
    have h1 := mul_le_mul_of_nonneg_right hpLo hm.le
    have h2 := mul_le_mul_of_nonneg_right hmLo hp.le
    nlinarith only [h1, h2]
  have hsqrt : (2/3 : ℝ)*Real.sqrt ν ≤ Real.sqrt (ν/2) := by
    nlinarith only [Real.sq_sqrt hν.le, Real.sq_sqrt (by linarith : 0 ≤ ν/2),
      Real.sqrt_nonneg ν, Real.sqrt_nonneg (ν/2)]
  have hk : (2/3 : ℝ)*Real.sqrt ν ≤ 2*‖k‖ := hsqrt.trans hkbase
  have hsqgap : Real.sqrt ν ≤ 2*Real.sqrt (ν/2) := by
    nlinarith only [Real.sq_sqrt hν.le, Real.sq_sqrt (by linarith : 0 ≤ ν/2),
      Real.sqrt_nonneg ν, Real.sqrt_nonneg (ν/2)]
  have htgap : ε*Real.sqrt ν ≤ δp+δm := by
    have h1 := mul_le_mul_of_nonneg_left hsqgap hεpos.le
    nlinarith only [h1, hpLo, hmLo]
  have hden : 0 < ε*Real.sqrt ν := mul_pos hεpos (Real.sqrt_pos.2 hν)
  have ht0 : 0 ≤ t := div_nonneg Real.pi_pos.le (add_pos hp hm).le
  have ht : |t| ≤ 4/(ε*Real.sqrt ν) := by
    rw [abs_of_nonneg ht0]
    apply (div_le_div_iff₀ (add_pos hp hm) hden).2
    have h1 := mul_le_mul_of_nonneg_right Real.pi_le_four hden.le
    have h2 := mul_le_mul_of_nonneg_left htgap (by norm_num : (0 : ℝ) ≤ 4)
    linarith only [h1, h2]
  refine ⟨r, hrlo, hrhi, t, ht, ?_⟩
  exact rank_one_resonant_probability_bound H w s up um k ν δp δm
    (spectral_search_hamiltonian_isHermitian V lam r w) hw hν hp hm hup hum hwu hwm hk hrem

end Qatlib.Papers.SpatialWalk15.SpectralSearch
