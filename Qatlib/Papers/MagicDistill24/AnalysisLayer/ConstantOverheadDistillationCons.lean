/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.ConstantOverheadDistillationStat
public import Qatlib.Papers.MagicDistill24.AnalysisLayer.ChooseEntropyBoundCons
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.MagicDistill24.AnalysisLayer
open Filter

/-- Shows that binary entropy divided by its argument decreases on the stated positive interval. -/
private theorem entropy_div_antitone {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hr1 : r ≤ 1) :
    Real.binEntropy r/r ≤ Real.binEntropy a/a := by
  have hr0 : 0 < r := ha.trans_le har
  have hcoef : 0 ≤ 1-a/r := sub_nonneg.2 ((div_le_one hr0).2 har)
  have h := Real.strictConcave_binEntropy.concaveOn.2 ⟨hr0.le,hr1⟩
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (show 0 ≤ a/r by positivity) hcoef (show a/r+(1-a/r)=1 by ring)
  simp only [smul_eq_mul,Real.binEntropy_zero,mul_zero,add_zero,div_mul_cancel₀ a hr0.ne'] at h
  apply (le_div_iff₀ ha).2
  have he : Real.binEntropy r/r*a=(a/r)*Real.binEntropy r := by ring
  rw [he]
  exact h

/-- Shows that a fixed base below one raised to a positive linear exponent eventually falls
below any positive tolerance. -/
private theorem rpow_linear_eventually_le {x a : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (ha : 0 < a) :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n' ≥ n₀, x^(a*(n' : ℝ)) ≤ ε := by
  intro ε hε
  have hy0 := Real.rpow_nonneg hx0 a
  have hy1 := Real.rpow_lt_one hx0 hx1 ha
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hy0 hy1
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 (ht.eventually_le_const hε)
  refine ⟨n₀,fun n' hn' => ?_⟩
  calc
    _ = (x^a)^(n' : ℝ) := Real.rpow_mul hx0 a (n' : ℝ)
    _ = (x^a)^n' := Real.rpow_natCast _ _
    _ ≤ ε := hn₀ n' hn'

/-- Establishes the constant-overhead distillation result specified by
`ConstantOverheadDistillation`. -/
theorem constantOverheadDistillation : ConstantOverheadDistillation := by
  intro C cK cTl cTh hC hcK hcTl hcTlTh hcTh1
  have hC0 : 0 < C := by linarith only [hC]
  let H := Real.binEntropy cTl/cTl
  let pth := Real.exp (-H)/C
  have hpth : 0 < pth := by dsimp [pth]; positivity
  refine ⟨hpth,?_⟩
  intro pPh hp0 hp1 n k t hn hk htlo hthi
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  let r := ((t : ℝ)+1)/(n : ℝ)
  have har : cTl ≤ r := (le_div_iff₀ hnr).2 htlo
  have hr0 : 0 < r := hcTl.trans_le har
  have hrTh : r ≤ cTh := (div_le_iff₀ hnr).2 hthi
  have hr1 : r ≤ 1 := hrTh.trans hcTh1
  have htn : t+1 ≤ n := by
    have he := (div_le_one hnr).1 hr1
    exact_mod_cast he
  have hratio := entropy_div_antitone hcTl har hr1
  have hnrEq : (n : ℝ)*r=(t : ℝ)+1 := by dsimp [r]; field_simp
  have hentropy : (n : ℝ)*Real.binEntropy r ≤ ((t : ℝ)+1)*H := by
    have h := (div_le_iff₀ hr0).1 hratio
    calc
      _ ≤ (n : ℝ)*(H*r) := mul_le_mul_of_nonneg_left h hnr.le
      _ = H*((n : ℝ)*r) := by ring
      _ = _ := by rw [hnrEq]; ring
  have he : (Nat.choose n (t+1) : ℝ) ≤ (Real.exp H)^(t+1) := by
    apply (chooseEntropyBound n (t+1) htn).trans
    simp only [Nat.cast_add,Nat.cast_one]
    change Real.exp ((n : ℝ)*Real.binEntropy r) ≤ _
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    simpa only [Nat.cast_add,Nat.cast_one] using hentropy
  have hxEq : pPh/pth=Real.exp H*(C*pPh) := by
    dsimp [pth]
    rw [Real.exp_neg]
    field_simp
  have hx0 : 0 ≤ pPh/pth := div_nonneg hp0 hpth.le
  have hx1 : pPh/pth < 1 := (div_lt_one hpth).2 hp1
  constructor
  · calc
      _ ≤ (Real.exp H)^(t+1)*(C*pPh)^(t+1) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ = (Real.exp H*(C*pPh))^(t+1) := (mul_pow _ _ _).symm
      _ = _ := by rw [← hxEq]
  constructor
  · have hk0 : 0 < (k : ℝ) := lt_of_lt_of_le (mul_pos hcK hnr) hk
    apply (div_le_div_iff₀ hk0 hcK).2
    have he := mul_le_mul_of_nonneg_left hk hC0.le
    nlinarith only [he]
  · exact rpow_linear_eventually_le hx0 hx1 hcTl

end Qatlib.Papers.MagicDistill24.AnalysisLayer
