/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedFailureMass
import Qatlib.Papers.HamLCUSim12.LCUDeferred.Theorem3LCUFailureCorrectedStat

/-!
# Failure bound for the corrected signed LCU protocol

This module proves the corrected failure bound corresponding to Theorem 3 of [ChildsWiebe2012].
For nonzero signed coefficients with both signs present, pairwise unitary-difference bounds give
a failure estimate of `k * Δ ^ 2 / 4 + 4 * κ / (κ + 1) ^ 2`, where `κ` is the ratio of positive
to absolute negative coefficient mass.

The proof uses the signed-mixture norm identity and bounds for the positive and negative state
means. Singleton sign groups have unit norm, supplying the case of two total terms.

## Main statements

* `cw_positive_mean_singleton_norm`: gives unit norm for a singleton positive group.
* `cw_negative_mean_singleton_norm`: gives unit norm for a singleton negative group.
* `theorem3LCUFailureCorrected`: proves the corrected signed LCU failure contract.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical
variable {I : Type} [Fintype I] [DecidableEq I]

/-- If the positive coefficient group contains exactly one index, its normalized weighted state
mean has norm one for unitary system matrices and a normalized input. -/
theorem cw_positive_mean_singleton_norm (k : ℕ) (c : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ)
    (hp : ∃ q,0<c q) (hcard : (cwPositiveTerms k c).card=1)
    (ψ : QState I) (hψ : Normalized ψ) : ‖cwStateMeanPositive k c U ψ‖=1 := by
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hcard
  have hw : cwPositiveWeight k c=c q := by simp only [cwPositiveWeight,hq,Finset.sum_singleton]
  have hc : (c q:ℂ)≠0 := by exact_mod_cast (hw ▸ (cw_positive_weight_pos k c hp).ne')
  have he : cwStateMeanPositive k c U ψ=stateVector (U q*ᵥψ) := by
    ext x
    rw [cw_positive_mean_coordinate]
    simp only [hq,Finset.sum_singleton,hw,Matrix.smul_mulVec,Pi.smul_apply,Complex.real_smul]
    field_simp
  rw [he]
  exact (normalized_iff_stateVector_norm _).mp (normalized_applyGate (hU q) hψ)

/-- If the negative coefficient group contains exactly one index, its normalized absolute-weight
state mean has norm one for unitary system matrices and a normalized input. -/
theorem cw_negative_mean_singleton_norm (k : ℕ) (c : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ)
    (hn : ∃ q,c q<0) (hcard : (cwNegativeTerms k c).card=1)
    (ψ : QState I) (hψ : Normalized ψ) : ‖cwStateMeanNegative k c U ψ‖=1 := by
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hcard
  have hw : cwNegativeWeight k c=|c q| := by simp only [cwNegativeWeight,hq,Finset.sum_singleton]
  have hc : ((|c q|:ℝ):ℂ)≠0 := by exact_mod_cast (hw ▸ (cw_negative_weight_pos k c hn).ne')
  have he : cwStateMeanNegative k c U ψ=stateVector (U q*ᵥψ) := by
    ext x
    rw [cw_negative_mean_coordinate]
    simp only [hq,Finset.sum_singleton,hw,Matrix.smul_mulVec,Pi.smul_apply,Complex.real_smul]
    field_simp
  rw [he]
  exact (normalized_iff_stateVector_norm _).mp (normalized_applyGate (hU q) hψ)

/-- The corrected signed LCU protocol satisfies the failure bound `k * Δ ^ 2 / 4 + 4 * κ / (κ +
1) ^ 2` under the unitary, coefficient-sign, and uniform difference hypotheses of
`Theorem3LCUFailureCorrected` [Childs and Wiebe, Theorem 3][ChildsWiebe2012]. -/
theorem theorem3LCUFailureCorrected : Theorem3LCUFailureCorrected := by
  intro k I _ _ hk U hU c hc hp hn Δ _ hΔ ψ hψ
  let a := cwPositiveWeight k c
  let b := cwNegativeWeight k c
  let p := a/(a+b)
  let q := b/(a+b)
  let A := cwStateMeanPositive k c U ψ
  let B := cwStateMeanNegative k c U ψ
  have ha : 0<a := cw_positive_weight_pos k c hp
  have hb : 0<b := cw_negative_weight_pos k c hn
  have hs : 0<a+b := add_pos ha hb
  have hp0 : 0≤p := div_nonneg ha.le hs.le
  have hq0 : 0≤q := div_nonneg hb.le hs.le
  have hpq : p+q=1 := by dsimp [p,q];field_simp
  have hf : cwFailureProbCorrected k c U ψ=1-‖(p:ℂ) • A-(q:ℂ) • B‖^2 :=
    cw_failure_signed_mix k hk c U hU hc hp hn ψ hψ
  have hmeans := cw_state_means_bounds k c U hU hp hn Δ hΔ ψ hψ
  have hsum : ‖A+B‖^2≤4 := by
    have hh : ‖A+B‖≤2 := (norm_add_le A B).trans (by linarith [hmeans.1,hmeans.2.1])
    nlinarith [norm_nonneg (A+B)]
  have hadd : p*(1-‖A‖^2)+q*(1-‖B‖^2)≤(k:ℝ)*Δ^2/4 := by
    by_cases h1 : k=1
    · have hcards := cw_sign_cards k c hc
      have hpc := Finset.card_pos.mpr (cw_positive_nonempty k c hp)
      have hnc := Finset.card_pos.mpr (cw_negative_nonempty k c hn)
      have hp1 : (cwPositiveTerms k c).card=1 := by omega
      have hn1 : (cwNegativeTerms k c).card=1 := by omega
      have hA : ‖A‖=1 := cw_positive_mean_singleton_norm k c U hU hp hp1 ψ hψ
      have hB : ‖B‖=1 := cw_negative_mean_singleton_norm k c U hU hn hn1 ψ hψ
      rw [hA,hB]
      nlinarith [sq_nonneg Δ,Nat.cast_nonneg (α := ℝ) k]
    · have hk2 : (2:ℝ)≤k := by exact_mod_cast (show 2≤k by omega)
      have hAp := mul_le_mul_of_nonneg_left hmeans.2.2.1 hp0
      have hBq := mul_le_mul_of_nonneg_left hmeans.2.2.2 hq0
      have hstep : Δ^2/2≤(k:ℝ)*Δ^2/4 := by nlinarith [sq_nonneg Δ]
      calc _≤p*(Δ^2/2)+q*(Δ^2/2) := add_le_add hAp hBq
           _=Δ^2/2 := by rw [← add_mul,hpq,one_mul]
           _≤_ := hstep
  have hm : p*q*‖A+B‖^2≤4*p*q := by nlinarith [mul_le_mul_of_nonneg_left hsum (mul_nonneg hp0 hq0)]
  have hbound : cwFailureProbCorrected k c U ψ≤(k:ℝ)*Δ^2/4+4*p*q := by
    rw [hf,nearby_signed_mix_norm_sq p q hpq A B]
    nlinarith [hadd,hm]
  have hcoeff : 4*p*q=4*(a/b)/(a/b+1)^2 := by
    dsimp [p,q]
    field_simp
  rw [hcoeff] at hbound
  simpa only [a,b,cwPositiveWeight,cwNegativeWeight,cwPositiveTerms,cwNegativeTerms,Finset.sum_filter] using hbound
end Qatlib.Papers.HamLCUSim12.LCUDeferred
