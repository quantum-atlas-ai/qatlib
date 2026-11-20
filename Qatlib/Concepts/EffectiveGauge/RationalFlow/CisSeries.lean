/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.NegativeExpProgram
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseLogProgram

@[expose] public section

/-! # Actual rational complex Taylor prefixes for cis -/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of cis Pair Add in the Rational Flow construction. -/
def cisPairAdd (a b : RationalCircleSample) : RationalCircleSample := (a.1+b.1,a.2+b.2)
/-- Definition of cis Pair Mul in the Rational Flow construction. -/
def cisPairMul (a b : RationalCircleSample) : RationalCircleSample := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
/-- Definition of cis Term Step in the Rational Flow construction. -/
def cisTermStep (x : ℚ) (n : ℕ) (t : RationalCircleSample) : RationalCircleSample :=
  (-t.2*x/(n : ℚ),t.1*x/(n : ℚ))

/-- Definition of cis Taylor Term in the Rational Flow construction. -/
def cisTaylorTerm (x : ℚ) : ℕ → RationalCircleSample
  | 0 => (1,0)
  | n+1 => cisTermStep x (n+1) (cisTaylorTerm x n)

/-- Definition of cis Taylor Partial in the Rational Flow construction. -/
def cisTaylorPartial (x : ℚ) : ℕ → RationalCircleSample
  | 0 => (0,0)
  | n+1 => cisPairAdd (cisTaylorPartial x n) (cisTaylorTerm x n)

/-- The magnitude of term `n + 1` equals that of term `n` multiplied by `|x| / (n + 1)`. -/
theorem cisMagnitude_step (x : ℚ) (n : ℕ) :
    negativeExpMagnitude x (n+1)=negativeExpMagnitude x n*|x|/((n+1 : ℕ) : ℚ) := by
  unfold negativeExpMagnitude
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  field_simp

noncomputable section

/-- Adding rational circle pairs and casting gives the sum of the two complex casts. -/
theorem cisPairAdd_cast (a b : RationalCircleSample) :
    rationalCircleCast (cisPairAdd a b)=rationalCircleCast a+rationalCircleCast b := by
  apply Complex.ext <;> simp [cisPairAdd,rationalCircleCast]

/-- Multiplying rational circle pairs and casting gives the product of the two complex casts. -/
theorem cisPairMul_cast (a b : RationalCircleSample) :
    rationalCircleCast (cisPairMul a b)=rationalCircleCast a*rationalCircleCast b := by
  apply Complex.ext <;> simp [cisPairMul,rationalCircleCast]

/-- After casting, a Taylor term update multiplies the input by `x * I` and divides by the supplied
index `n`. -/
theorem cisTermStep_cast (x : ℚ) (n : ℕ) (t : RationalCircleSample) :
    rationalCircleCast (cisTermStep x n t)=
      rationalCircleCast t*((x : ℂ)*Complex.I)/(n : ℂ) := by
  rw [Complex.div_natCast]
  apply Complex.ext <;> simp [cisTermStep,rationalCircleCast]

/-- The rational pair with both coordinates zero casts to complex zero. -/
@[simp] theorem rationalCircleCast_zero : rationalCircleCast (0,0)=0 := by
  apply Complex.ext <;> norm_num [rationalCircleCast]

/-- The rational Taylor term at index `n` casts to `(x * I)^n / n!`. -/
theorem cisTaylorTerm_cast (x : ℚ) (n : ℕ) :
    rationalCircleCast (cisTaylorTerm x n)=((x : ℂ)*Complex.I)^n/(n.factorial : ℂ) := by
  induction n with
  | zero => simp [cisTaylorTerm]
  | succ n ih =>
    rw [cisTaylorTerm,cisTermStep_cast,ih,Nat.factorial_succ,pow_succ]
    push_cast
    field_simp

/-- The rational partial sum casts to the complex exponential series summed over indices strictly
below `n` at argument `x * I`. -/
theorem cisTaylorPartial_cast (x : ℚ) (n : ℕ) :
    rationalCircleCast (cisTaylorPartial x n)=
      ∑ j ∈ Finset.range n, ((x : ℂ)*Complex.I)^j/(j.factorial : ℂ) := by
  induction n with
  | zero => simp [cisTaylorPartial]
  | succ n ih => rw [cisTaylorPartial,cisPairAdd_cast,ih,cisTaylorTerm_cast,Finset.sum_range_succ]

/-- The complex phase at real angle `x` is the complex exponential of `x * I`. -/
theorem complexPhase_eq_exp (x : ℝ) : complexPhase x=Complex.exp ((x : ℂ)*Complex.I) := by
  apply Complex.ext
  · exact (Complex.exp_ofReal_mul_I_re x).symm
  · exact (Complex.exp_ofReal_mul_I_im x).symm

/-- The next-term norm times two bounds the whole complex tail. Unlike the
negative exponential this is not an alternating real-series argument. -/
theorem cisTaylorPartial_error (x : ℚ) (hx : |x| ≤ 1/2) (n : ℕ) :
    ‖rationalCircleCast (cisTaylorPartial x n)-complexPhase (x : ℝ)‖ ≤
      ((2*negativeExpMagnitude x n : ℚ) : ℝ) := by
  have hxR : |(x : ℝ)| ≤ 1/2 := by
    have h : ((|x| : ℚ) : ℝ) ≤ (((1/2 : ℚ) : ℝ)) := Rat.cast_le.mpr hx
    simpa only [Rat.cast_abs,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hz : ‖(x : ℂ)*Complex.I‖=|(x : ℝ)| := by simp
  have hbound : ‖(x : ℂ)*Complex.I‖/((n+1 : ℕ) : ℝ) ≤ 1/2 := by
    rw [hz]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<(n+1 : ℕ))).mpr
    linarith
  have he := Complex.exp_bound' hbound
  rw [hz] at he
  rw [cisTaylorPartial_cast,complexPhase_eq_exp,norm_sub_rev]
  simpa only [Complex.ofReal_ratCast,negativeExpMagnitude,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,Rat.cast_pow,
    Rat.cast_abs,Rat.cast_natCast,mul_comm] using he

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
