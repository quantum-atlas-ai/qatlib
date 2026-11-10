/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.WordIntegral
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem word_continuous (ks : List A) : Continuous (word ks) :=
  continuous_iff_continuousAt.mpr (fun t => (word_hasDerivAt ks t).continuousAt)

theorem duhamel_path_derivative (K : A) (ks : List A) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((t-u) • K)*word ks u)
      (NormedSpace.exp ((t-s) • K)*(generator ks s-K)*word ks s) s := by
  have he := (hasDerivAt_exp_smul_const K (t-s)).scomp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have hd := he.mul (word_hasDerivAt ks s)
  convert! hd using 1
  (try simp only [Function.comp_apply, zero_sub, neg_smul, one_smul, neg_mul])
  noncomm_ring

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
