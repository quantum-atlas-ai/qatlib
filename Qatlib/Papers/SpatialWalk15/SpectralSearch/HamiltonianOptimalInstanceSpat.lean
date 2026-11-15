/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.SpatialWalk15.SpectralSearch.HamiltonianOptimalInstanceStat
public import Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionSpat

@[expose] public section
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false

namespace Qatlib.Papers.SpatialWalk15.SpectralSearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
open Matrix
open scoped Classical BigOperators

/-- The probability of a singleton outcome equals the squared norm of the inner product with its
basis state. -/
theorem measureProb_singleton_eq_inner_ket
    {I : Type} [Fintype I] [DecidableEq I] (ψ : QState I) (ι : I) :
    MeasureProb ψ {ι} = ‖Inner (Qatlib.Foundations.PureStateMath.Ket ι) ψ‖ ^ 2 := by
  simp [MeasureProb, BornProb, inner_apply, Qatlib.Foundations.PureStateMath.Ket]

set_option maxHeartbeats 1000000 in

/-- Under the spectral and overlap hypotheses, spatial search achieves the specified success
probability in time bounded by a constant times the square root of the state space size
divided by the square root of the gap parameter. -/
theorem spatial_search_hamiltonian_optimal_instance : SpatialSearchHamiltonianOptimalInstance := by
  intro κ _ _ _ V lam σ c ι hV hlamσ hlamc hc0 hc1 hN hεlo hεbound
  let w : QState κ := Qatlib.Foundations.PureStateMath.Ket ι
  let s : QState κ := fun j => V j σ
  let ε := ‖Inner w s‖
  let ν :=
      Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch.spectralGapParam c
  have hNpos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card κ by omega)
  have hsqrtN : 0 < Real.sqrt (Fintype.card κ) := Real.sqrt_pos.2 hNpos
  have hεpos : 0 < ε := (inv_pos.2 hsqrtN).trans_le hεlo
  have hν : 0 < ν :=
      Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch.spectral_gap_param_pos hc0 hc1
  have hsqrtν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  obtain ⟨r, hrlo, hrhi, t, ht, hprob⟩ := spectral_search_sufficient_condition V lam σ c w
    hV hlamσ hlamc hc0 hc1 (normalized_ket ι) hεpos hεbound
  let H := searchHamiltonian V lam r w
  let τ := |t|
  have hH : H.IsHermitian := spectral_search_hamiltonian_isHermitian V lam r w
  have heigen : spectralHamiltonian V lam *ᵥ s = s := by
    simpa [s, hlamσ] using spectralHamiltonian_eigen V lam σ hV
  have hHs : H *ᵥ s = s+Inner w s • w := by
    simp only [H, searchHamiltonian, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, rankOneProjector_mulVec, heigen]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_one]
    ring
  have ha : Inner w s ≠ 0 := norm_ne_zero_iff.1 hεpos.ne'
  have hrev := hamiltonianEvolution_rank_one_reciprocity H s w (Inner w s) hH ha hHs t
  have htime : ‖Inner w (HamiltonianEvolution H (-τ) *ᵥ s)‖ =
      ‖Inner w (HamiltonianEvolution H t *ᵥ s)‖ := by
    by_cases ht0 : 0 ≤ t
    · simpa only [τ, abs_of_nonneg ht0] using hrev
    · simp only [τ, abs_of_neg (lt_of_not_ge ht0), neg_neg]
  have hphys : -(rankOneProjector w)-(1+r) • spectralHamiltonian V lam =
      (-H)+(-r) • (1 : Matrix κ κ ℂ) := by
    dsimp [H, searchHamiltonian]
    module
  have hneg : HamiltonianEvolution (-H) τ = HamiltonianEvolution H (-τ) := by
    unfold HamiltonianEvolution
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Complex.ofReal_neg]
    ring
  have hphase : ‖Complex.exp ((-Complex.I*(τ : ℂ))*((-r : ℝ) : ℂ))‖ = 1 := by
    have he : (-Complex.I*(τ : ℂ))*((-r : ℝ) : ℂ) = ((τ*r : ℝ) : ℂ)*Complex.I := by
      push_cast
      ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hphysical : ‖Inner w ((HamiltonianEvolution
      (-(rankOneProjector w)-(1+r) • spectralHamiltonian V lam) τ) *ᵥ s)‖ =
      ‖Inner w (HamiltonianEvolution H t *ᵥ s)‖ := by
    rw [hphys, hamiltonianEvolution_shift_mulVec, inner_smul_state, norm_mul,
      hphase, one_mul, hneg, htime]
  have hrecip : 1/ε ≤ Real.sqrt (Fintype.card κ) := by
    apply (div_le_iff₀ hεpos).2
    have he : 1 ≤ ε*Real.sqrt (Fintype.card κ) :=
      (div_le_iff₀ hsqrtN).1 (by simpa only [inv_eq_one_div] using hεlo)
    linarith only [he]
  have hnum : 4/ε ≤ 4*Real.sqrt (Fintype.card κ) := by
    have he := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 4)
    simpa only [mul_one_div] using he
  have hτ : τ ≤ 4*Real.sqrt (Fintype.card κ)/Real.sqrt ν := by
    apply ht.trans
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hnum hsqrtν.le
  refine ⟨r, hrlo, hrhi, τ, abs_nonneg t, hτ, ?_⟩
  change ν/8 ≤ MeasureProb ((HamiltonianEvolution
    (-(rankOneProjector w)-(1+r) • spectralHamiltonian V lam) τ) *ᵥ s) {ι}
  rw [measureProb_singleton_eq_inner_ket, hphysical]
  exact hprob

end Qatlib.Papers.SpatialWalk15.SpectralSearch
