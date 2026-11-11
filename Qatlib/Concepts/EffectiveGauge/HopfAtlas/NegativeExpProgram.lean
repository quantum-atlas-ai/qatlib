/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.NegativeExpSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite execution of the exp_negative cutoff, Taylor loop and squaring

The next-term test stops at the same first successful index as Python.
Clamping is part of the actual program. The cutoff uses exp(1)>2.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of negative Exp Loop in the Hopf Atlas construction. -/
def negativeExpLoop (x tolerance : ℚ) (n : ℕ) (answer term : ℚ) : ℕ → RationalScalarResult
  | 0 => ⟨answer,|term|,n⟩
  | fuel+1 =>
    if |term| ≤ tolerance then ⟨answer,|term|,n⟩
    else negativeExpLoop x tolerance (n+1) (answer+term) (term*(-x)/((n+1 : ℕ) : ℚ)) fuel

/-- Definition of reduced Negative Exp in the Hopf Atlas construction. -/
def reducedNegativeExp (x tolerance : ℚ) : RationalScalarResult :=
  negativeExpLoop x tolerance 1 1 (-x) (arctanFuel tolerance)

/-- Definition of scalar Clamp in the Hopf Atlas construction. -/
def scalarClamp (x : ℚ) : ℚ := min 1 (max 0 x)

/-- Definition of negative Exp Squares in the Hopf Atlas construction. -/
def negativeExpSquares : ℕ → RationalScalarResult → RationalScalarResult
  | 0,r => r
  | n+1,r => negativeExpSquares n ⟨r.value*r.value,2*r.error,r.terms⟩

/-- Definition of negative Exp Halvings in the Hopf Atlas construction. -/
def negativeExpHalvings (x : ℚ) : ℕ := Nat.clog 2 (Nat.ceil (2*x))

/-- Definition of rational Negative Exp in the Hopf Atlas construction. -/
def rationalNegativeExp (x tolerance : ℚ) : RationalScalarResult :=
  let cutoff := arctanFuel tolerance
  if (cutoff : ℚ) ≤ x then ⟨0,(2^cutoff : ℚ)⁻¹,0⟩
  else
    let h := negativeExpHalvings x
    let r := reducedNegativeExp (x/(2^h : ℚ)) (tolerance/(2^h : ℚ))
    negativeExpSquares h ⟨scalarClamp r.value,r.error,r.terms⟩

/-- Original `negativeExpCutoff_first` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExpCutoff_first (tolerance : ℚ) (ht : 0<tolerance) (k : ℕ)
    (hk : k<arctanFuel tolerance) : tolerance<(2^k : ℚ)⁻¹ := by
  have hp : 2^k<Nat.ceil (1/tolerance) := (Nat.lt_clog_iff_pow_lt (by decide)).mp hk
  have h : (2^k : ℚ)<1/tolerance := by exact_mod_cast Nat.lt_ceil.mp hp
  have hm := (lt_div_iff₀ ht).mp h
  have hd : tolerance<1/(2^k : ℚ) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  simpa only [one_div] using hd

/-- Original `negativeExp_term_step` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExp_term_step (x : ℚ) (n : ℕ) :
    ((-x)^n/(n.factorial : ℚ))*(-x)/((n+1 : ℕ) : ℚ)=(-x)^(n+1)/((n+1).factorial : ℚ) := by
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  field_simp

/-- Original `negativeExpTerm_abs` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExpTerm_abs (x : ℚ) (n : ℕ) :
    |(-x)^n/(n.factorial : ℚ)|=negativeExpMagnitude x n := by
  rw [abs_div,abs_pow,abs_neg,abs_of_nonneg (by positivity : (0 : ℚ) ≤ n.factorial)]
  rfl

/-- Original `negativeExpLoop_spec` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExpLoop_spec (x tolerance : ℚ) (fuel n : ℕ)
    (hstop : negativeExpMagnitude x (n+fuel) ≤ tolerance) :
    let r := negativeExpLoop x tolerance n (negativeExpPartial x n) ((-x)^n/(n.factorial : ℚ)) fuel
    r.value=negativeExpPartial x r.terms ∧ r.error=negativeExpMagnitude x r.terms ∧
      n ≤ r.terms ∧ r.terms ≤ n+fuel ∧ r.error ≤ tolerance ∧
      ∀ k, n ≤ k → k<r.terms → tolerance<negativeExpMagnitude x k := by
  induction fuel generalizing n with
  | zero =>
    dsimp only [negativeExpLoop]
    refine ⟨rfl,negativeExpTerm_abs x n,le_rfl,by omega,?_,?_⟩
    · simpa only [negativeExpTerm_abs,Nat.add_zero] using hstop
    · intro k hk hlt
      change k<n at hlt
      omega
  | succ fuel ih =>
    simp only [negativeExpLoop]
    split_ifs with h
    · dsimp only
      refine ⟨rfl,negativeExpTerm_abs x n,le_rfl,by omega,?_,?_⟩
      · simpa only [negativeExpTerm_abs] using h
      · intro k hk hlt
        omega
    · rw [negativeExp_term_step,← negativeExpPartial_succ]
      have hs : negativeExpMagnitude x ((n+1)+fuel) ≤ tolerance := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hstop
      obtain ⟨hv,he,hlo,hhi,hbudget,hprior⟩ := ih (n+1) hs
      refine ⟨hv,he,by omega,by omega,hbudget,?_⟩
      intro k hk hlt
      by_cases hkn : k=n
      · subst k
        simpa only [negativeExpTerm_abs] using lt_of_not_ge h
      · exact hprior k (by omega) hlt

/-- Original `reducedNegativeExp_spec` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem reducedNegativeExp_spec (x tolerance : ℚ) (hx : |x| ≤ 1/2) (ht : 0<tolerance) :
    let r := reducedNegativeExp x tolerance
    r.value=negativeExpPartial x r.terms ∧ r.error=negativeExpMagnitude x r.terms ∧
      1 ≤ r.terms ∧ r.terms ≤ 1+arctanFuel tolerance ∧ r.error ≤ tolerance ∧
      ∀ k, 1 ≤ k → k<r.terms → tolerance<negativeExpMagnitude x k := by
  have hp : (2^arctanFuel tolerance : ℚ) ≤ 2^(1+arctanFuel tolerance) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : (2^(1+arctanFuel tolerance) : ℚ)⁻¹ ≤ (2^arctanFuel tolerance : ℚ)⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp
  have hstop : negativeExpMagnitude x (1+arctanFuel tolerance) ≤ tolerance :=
    (negativeExpMagnitude_dyadic x hx _).trans (hi.trans (arctanFuel_budget tolerance ht))
  have hinit : negativeExpPartial x 1=1 := by simp [negativeExpPartial]
  simpa only [reducedNegativeExp,hinit,Nat.factorial_one,Nat.cast_one,div_one,pow_one]
    using negativeExpLoop_spec x tolerance (arctanFuel tolerance) 1 hstop

/-- Original `negativeExpHalvings_reduced` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExpHalvings_reduced (x : ℚ) (hx : 0 ≤ x) :
    0 ≤ x/(2^negativeExpHalvings x : ℚ) ∧ x/(2^negativeExpHalvings x : ℚ) ≤ 1/2 := by
  refine ⟨by positivity,?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℚ)<2^negativeExpHalvings x)).mpr
  have h : 2*x ≤ (2^negativeExpHalvings x : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (Nat.ceil (2*x)))
  linarith

/-- Original `negativeExpHalvings_first` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExpHalvings_first (x : ℚ) (k : ℕ) (hk : k<negativeExpHalvings x) :
    1/2<x/(2^k : ℚ) := by
  have hp : 2^k<Nat.ceil (2*x) := (Nat.lt_clog_iff_pow_lt (by decide)).mp hk
  have h : (2^k : ℚ)<2*x := by exact_mod_cast Nat.lt_ceil.mp hp
  apply (lt_div_iff₀ (by positivity : (0 : ℚ)<2^k)).mpr
  linarith

/-- Original `negativeExpSquares_spec` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExpSquares_spec (h : ℕ) (r : RationalScalarResult) :
    (negativeExpSquares h r).value=r.value^(2^h) ∧
      (negativeExpSquares h r).error=(2^h : ℚ)*r.error ∧ (negativeExpSquares h r).terms=r.terms := by
  induction h generalizing r with
  | zero => simp [negativeExpSquares]
  | succ h ih =>
    rw [negativeExpSquares]
    obtain ⟨hv,he,ht⟩ := ih ⟨r.value*r.value,2*r.error,r.terms⟩
    refine ⟨?_,?_,ht⟩
    · rw [hv]
      change (r.value*r.value)^(2^h)=r.value^(2^(h+1))
      rw [← pow_two,← pow_mul,pow_succ]
      congr 1
      omega
    · rw [he]
      change (2^h : ℚ)*(2*r.error)=(2^(h+1) : ℚ)*r.error
      rw [pow_succ]
      ring

/-- Original `scalarClamp_range` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem scalarClamp_range (x : ℚ) : 0 ≤ scalarClamp x ∧ scalarClamp x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

noncomputable section

/-- Original `unit_pow_error` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
private theorem unit_pow_error (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (n : ℕ) :
    |a^n-b^n| ≤ (n : ℝ)*|a-b| := by
  have hm : max |a| |b| ≤ 1 := by simpa only [abs_of_nonneg ha.1,abs_of_nonneg hb.1] using max_le ha.2 hb.2
  have hp : (max |a| |b|)^(n-1) ≤ (1 : ℝ) := pow_le_one₀ (by positivity) hm
  calc
    _ ≤ |a-b| *(n : ℝ)*(max |a| |b|)^(n-1) := abs_pow_sub_pow_le a b n
    _ ≤ |a-b| *(n : ℝ)*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- Original `negativeExp_cutoff` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem negativeExp_cutoff (x : ℝ) (n : ℕ) (hn : (n : ℝ) ≤ x) :
    Real.exp (-x) ≤ (2^n : ℝ)⁻¹ := by
  rw [Real.exp_neg]
  have hpow : (2 : ℝ)^n ≤ Real.exp x := by
    calc
      (2 : ℝ)^n ≤ (Real.exp 1)^n := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le n
      _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hn
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ)<2^n) hpow

/-- Original `scalarClamp_error` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem scalarClamp_error (x : ℚ) (a e : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (herr : |(x : ℝ)-a| ≤ e) :
    |(scalarClamp x : ℝ)-a| ≤ e := by
  have h := abs_le.mp herr
  by_cases hx : x ≤ 0
  · have hc : scalarClamp x=0 := by simp only [scalarClamp,max_eq_left hx]; norm_num
    rw [hc,Rat.cast_zero,zero_sub,abs_neg,abs_of_nonneg ha]
    have hxR : (x : ℝ) ≤ 0 := by exact_mod_cast hx
    linarith
  · by_cases hx1 : 1 ≤ x
    · simp only [scalarClamp,max_eq_right (le_of_not_ge hx),min_eq_left hx1,Rat.cast_one]
      rw [abs_of_nonneg (by linarith)]
      have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
      linarith
    · simpa only [scalarClamp,max_eq_right (le_of_not_ge hx),min_eq_right (le_of_not_ge hx1)] using herr

/-- Original `reducedNegativeExp_error` guarantee for the `NegativeExpProgram` construction; the complete source hypotheses are retained. -/
theorem reducedNegativeExp_error (x tolerance : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1/2) (ht : 0<tolerance) :
    |((reducedNegativeExp x tolerance).value : ℝ)-Real.exp (-(x : ℝ))| ≤
      ((reducedNegativeExp x tolerance).error : ℝ) := by
  have hs := reducedNegativeExp_spec x tolerance (by rwa [abs_of_nonneg hx]) ht
  rw [hs.1,hs.2.1]
  exact negativeExpPartial_error x hx hx1 _

/-- The returned rational value and its actual error ledger approximate the
real exponential; no exponential oracle is supplied to the execution. -/
theorem rationalNegativeExp_spec (x tolerance : ℚ) (hx : 0 ≤ x) (ht : 0<tolerance) :
    let r := rationalNegativeExp x tolerance
    |(r.value : ℝ)-Real.exp (-(x : ℝ))| ≤ (r.error : ℝ) ∧
      0 ≤ r.value ∧ r.value ≤ 1 ∧ 0 ≤ r.error ∧ r.error ≤ tolerance ∧
      r.terms ≤ 1+arctanFuel (tolerance/(2^negativeExpHalvings x : ℚ)) := by
  dsimp only [rationalNegativeExp]
  split_ifs with hcut
  · dsimp only
    refine ⟨?_,by norm_num,by norm_num,by positivity,arctanFuel_budget tolerance ht,by omega⟩
    rw [Rat.cast_zero,zero_sub,abs_neg,abs_of_pos (Real.exp_pos _)]
    push_cast
    exact negativeExp_cutoff (x : ℝ) (arctanFuel tolerance) (by exact_mod_cast hcut)
  · let h := negativeExpHalvings x
    let y := x/(2^h : ℚ)
    let t := tolerance/(2^h : ℚ)
    let r := reducedNegativeExp y t
    let c : RationalScalarResult := ⟨scalarClamp r.value,r.error,r.terms⟩
    have hy := negativeExpHalvings_reduced x hx
    have hyQ : 0 ≤ y := hy.1
    have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hyQ
    have ht0 : 0<t := by dsimp [t]; positivity
    have hr := reducedNegativeExp_spec y t (by rw [abs_of_nonneg hy.1]; exact hy.2) ht0
    have he0 : 0 ≤ r.error := by rw [hr.2.1]; dsimp [negativeExpMagnitude]; positivity
    have he : |((scalarClamp r.value : ℚ) : ℝ)-Real.exp (-(y : ℝ))| ≤ (r.error : ℝ) :=
      scalarClamp_error r.value _ _ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hyR))
        (reducedNegativeExp_error y t hy.1 hy.2 ht0)
    have hc := scalarClamp_range r.value
    have hs := negativeExpSquares_spec h c
    have hb : (2^h : ℚ)*r.error ≤ tolerance := by
      have htR := hr.2.2.2.2.1
      change r.error ≤ tolerance/(2^h : ℚ) at htR
      exact (mul_le_mul_of_nonneg_left htR (by positivity)).trans_eq (by field_simp)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [hs.1,hs.2.1]
      change |(((scalarClamp r.value)^(2^h) : ℚ) : ℝ)-Real.exp (-(x : ℝ))| ≤ (((2^h : ℚ)*r.error : ℚ) : ℝ)
      push_cast
      have hexp : (Real.exp (-(y : ℝ)))^(2^h)=Real.exp (-(x : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp only [y]
        push_cast
        field_simp
      rw [← hexp]
      exact (unit_pow_error _ _ ⟨by exact_mod_cast hc.1,by exact_mod_cast hc.2⟩
        ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hyR)⟩ _).trans
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (2^h : ℕ)))
    · rw [hs.1]
      exact pow_nonneg hc.1 _
    · rw [hs.1]
      exact pow_le_one₀ hc.1 hc.2
    · rw [hs.2.1]
      exact mul_nonneg (by positivity) he0
    · exact hs.2.1.le.trans hb
    · rw [hs.2.2]
      exact hr.2.2.2.1

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
