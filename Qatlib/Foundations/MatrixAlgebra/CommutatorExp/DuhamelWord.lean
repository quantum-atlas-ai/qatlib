/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.WordIntegral

/-!
# Duhamel formula for exponential words

`word_continuous` establishes continuity of finite exponential words. Differentiating the path
`exp((t - s)K) * word ks s` yields the difference between the word generator and the reference
generator `K`.

Integrating this derivative gives `word_duhamel`, an exact integral formula for the error
relative to `exp(tK)`. This is a foundation for product-formula error analysis such as
[HejaziZiniArrazola2024].

## Main statements

* `duhamel_path_derivative`: Derivative of the interpolating exponential-word path.
* `word_duhamel`: Integral representation of the exponential-word error.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A finite exponential word is continuous in its real time parameter. -/
theorem word_continuous (ks : List A) : Continuous (word ks) :=
  continuous_iff_continuousAt.mpr (fun t => (word_hasDerivAt ks t).continuousAt)

/-- The derivative at `s` of `exp((t - u)K) * word ks u` is `exp((t - s)K) * (generator ks s -
K) * word ks s`. -/
theorem duhamel_path_derivative (K : A) (ks : List A) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((t-u) • K)*word ks u)
      (NormedSpace.exp ((t-s) • K)*(generator ks s-K)*word ks s) s := by
  have he := (hasDerivAt_exp_smul_const K (t-s)).scomp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have hd := he.mul (word_hasDerivAt ks s)
  convert! hd using 1
  (try simp only [Function.comp_apply, zero_sub, neg_smul, one_smul, neg_mul])
  noncomm_ring

/-- The difference between an exponential word and `exp(tK)` equals the interval integral of the
propagated generator difference from zero to `t`. -/
theorem word_duhamel (K : A) (ks : List A) (t : ℝ) :
    word ks t-NormedSpace.exp (t • K) =
      ∫ s in (0 : ℝ)..t, NormedSpace.exp ((t-s) • K)*(generator ks s-K)*word ks s := by
  have hc : Continuous (fun s : ℝ => NormedSpace.exp ((t-s) • K)*(generator ks s-K)*word ks s) :=
    (((exp_time_continuous K).comp (continuous_const.sub continuous_id)).mul
      ((generator_continuous ks).sub continuous_const)).mul (word_continuous ks)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ Set.uIcc (0 : ℝ) t) => duhamel_path_derivative K ks t s)
    (hc.intervalIntegrable 0 t)
  simpa only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, sub_zero, word_zero,
      mul_one] using hi.symm
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
