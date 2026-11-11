/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductKappaBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductGammaThresholdStat

/-!
# A threshold for the multiproduct exponent

This module proves `multiproductGammaThreshold`, deriving coefficient-mass control and a
terminal-node ratio bound from an explicit lower threshold on γ. The scalar lemma
`multiproduct_gamma_numerical` provides the exponential inequalities used to combine the
coefficient and mass estimates. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `multiproductGammaThreshold`: Under the analytic hypotheses and the stated threshold on γ,
  four times the negative coefficient mass is at most δ times the positive mass, and k²
  exp(−2γ(k + 1)) is at most 1 / 2.
* `multiproduct_gamma_numerical`: For K ≥ 1, γ > 0, η > 1 / 4, and 0 < δ ≤ 1, the stated
  logarithmic threshold on γ implies 2K² ≤ exp(2γ(K + 1)) and that δ times the explicit mass
  scale is at least 4.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

/-- For K ≥ 1, γ > 0, η > 1 / 4, and 0 < δ ≤ 1, the stated logarithmic threshold on γ implies
2K² ≤ exp(2γ(K + 1)) and that δ times the explicit mass scale is at least 4. -/
theorem multiproduct_gamma_numerical (K γ η δ : ℝ) (hK : 1 ≤ K) (hγ : 0 < γ)
    (hη : 1/4 < η) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ht : 1+Real.log η/2+(1/(2*K))*Real.log ((2*K)^((5 : ℝ)/2)/δ) ≤ γ) :
    2*K^2 ≤ Real.exp (2*γ*(K+1)) ∧
      4 ≤ δ*((2 : ℝ)^(-(1 : ℝ)/2)*K^(-(5 : ℝ)/2)*
        Real.exp (-(2*K)*(1+Real.log η/2-γ))) := by
  have hK0 : 0 < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlogδ : Real.log δ ≤ 0 := by
    have h := Real.log_le_log hδ hδ1
    simpa using h
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2up := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hηlog := multiproduct_eta_log_lower η hη
  have hA : 0 ≤ 1+Real.log η/2 := by linarith
  let R := (2*K)^((5 : ℝ)/2)/δ
  have hlR : Real.log R = (5/2 : ℝ)*(Real.log 2+Real.log K)-Real.log δ := by
    dsimp [R]
    rw [Real.log_div (by positivity) hδ.ne', Real.log_rpow (by positivity),
      Real.log_mul (by norm_num) hK0.ne']
  have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*K)
  have he : (2*K)*((1/(2*K))*Real.log R) = Real.log R := by field_simp
  have hmain : Real.log R ≤ 2*K*(γ-1-Real.log η/2) := by
    change 2*K*(1+Real.log η/2+(1/(2*K))*Real.log R) ≤ 2*K*γ at hmul
    nlinarith [he]
  have hlpow : Real.log (2*K^2) ≤ Real.log R := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlR]
    norm_num
    nlinarith
  have hcrit : 2*K^2 ≤ Real.exp (2*γ*(K+1)) := by
    have heg : Real.log (2*K^2) ≤ 2*γ*(K+1) := by nlinarith
    calc
      _ = Real.exp (Real.log (2*K^2)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr heg
  let scale := (2 : ℝ)^(-(1 : ℝ)/2)*K^(-(5 : ℝ)/2)*
    Real.exp (-(2*K)*(1+Real.log η/2-γ))
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hlscale : Real.log (δ*scale) = Real.log δ - Real.log 2/2 -
      (5/2 : ℝ)*Real.log K + 2*K*(γ-1-Real.log η/2) := by
    dsimp [scale]
    rw [Real.log_mul hδ.ne' hscale.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hK0, Real.log_exp]
    ring
  have hl4 : Real.log 4 ≤ Real.log (δ*scale) := by
    rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow, hlscale]
    norm_num
    rw [hlR] at hmain
    nlinarith
  exact ⟨hcrit, (Real.log_le_log_iff (by norm_num) (mul_pos hδ hscale)).mp hl4⟩

/-- Under the analytic hypotheses and the stated threshold on γ, four times the negative
coefficient mass is at most δ times the positive mass, and k² exp(−2γ(k + 1)) is at most 1 /
2. See [ChildsWiebe2012]. -/
theorem multiproductGammaThreshold : MultiproductGammaThreshold := by
  intro k hk γ η δ hγ hη hδ hδ1 hE hF ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnum := multiproduct_gamma_numerical (k : ℝ) γ η δ hkR hγ hη hδ hδ1 ht
  have hcast : ((k+1 : ℕ) : ℝ) = (k : ℝ)+1 := by push_cast; ring
  have hc : 2*(k : ℝ)^2 ≤ Real.exp (2*γ*((k+1 : ℕ) : ℝ)) := by
    rw [hcast]
    exact hnum.1
  have hm := multiproductKappaBound k hk γ η hγ hη hE hF hc
  let negMass := ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) =>
    mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q < 0),
    |mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q|
  let posMass := ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) =>
    0 < mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q),
    mCoeff k (Real.exp (γ*((k+1 : ℕ) : ℝ))) q
  let scale := (2 : ℝ)^(-(1 : ℝ)/2)*(k : ℝ)^(-(5 : ℝ)/2)*
    Real.exp (-(2*(k : ℝ))*(1+Real.log η/2-γ))
  have hn : 0 ≤ negMass := Finset.sum_nonneg (fun q _ => abs_nonneg _)
  change negMass*scale ≤ posMass at hm
  have hnscale := hnum.2
  change 4 ≤ δ*scale at hnscale
  constructor
  · change 4*negMass ≤ δ*posMass
    have hd := mul_le_mul_of_nonneg_left hm hδ.le
    have hn4 := mul_le_mul_of_nonneg_right hnscale hn
    nlinarith
  · have hprod : Real.exp (2*γ*((k+1 : ℕ) : ℝ))*
        Real.exp (-(2*γ)*((k+1 : ℕ) : ℝ)) = 1 := by
      rw [← Real.exp_add]
      have he : 2*γ*((k+1 : ℕ) : ℝ) + -(2*γ)*((k+1 : ℕ) : ℝ) = 0 := by ring
      rw [he, Real.exp_zero]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(2*γ)*((k+1 : ℕ) : ℝ))).le
    rw [hprod] at hh
    nlinarith

end Qatlib.Papers.HamLCUSim12.Multiproduct
