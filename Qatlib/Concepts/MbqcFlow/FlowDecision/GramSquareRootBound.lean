/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementData
open Qatlib.Foundations.PureStateMath
set_option warningAsError false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder MatrixOrder

private theorem sqrt_correction_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x ^ 2 - 3 * x + 2 * Real.sqrt x := by
  have hp : 0 ≤ Real.sqrt x * (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 2) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)) (by positivity)
  have hfactor :
      Real.sqrt x * (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 2) =
        (Real.sqrt x * Real.sqrt x) * (Real.sqrt x * Real.sqrt x) -
          3 * (Real.sqrt x * Real.sqrt x) + 2 * Real.sqrt x := by
    ring
  rw [hfactor, Real.mul_self_sqrt hx] at hp
  simpa only [pow_two] using hp

theorem gram_square_root_row_failure_bound (I : Type) [Fintype I] [DecidableEq I]
    (H : HermitianMat I ℂ) (hH : 0 ≤ H) (i : I) (hi : H.mat i i = 1) :
    1 - Complex.normSq (H.sqrt.mat i i) ≤
      ∑ j ∈ Finset.univ.erase i, Complex.normSq (H.mat i j) := by
  have hcorrection : 0 ≤ H ^ 2 - (3 : ℝ) • H + (2 : ℝ) • H.sqrt := by
    have hcfc : 0 ≤ H.cfc (fun x : ℝ => x ^ 2 - 3 * x + 2 * Real.sqrt x) :=
      HermitianMat.cfc_nonneg_of_nonneg hH sqrt_correction_nonneg
    simpa only [HermitianMat.cfc_add_apply, HermitianMat.cfc_sub_apply,
      HermitianMat.cfc_pow, HermitianMat.cfc_const_mul_id,
      HermitianMat.cfc_const_mul, HermitianMat.sqrt] using hcfc
  have hdiag :
      0 ≤ ((H ^ 2).mat i i).re - 3 + 2 * (H.sqrt.mat i i).re := by
    have hd := (HermitianMat.zero_le_iff.mp hcorrection).diag_nonneg (i := i)
    have hdre :
        0 ≤ ((H ^ 2 - (3 : ℝ) • H + (2 : ℝ) • H.sqrt).mat i i).re :=
      (Complex.nonneg_iff.mp hd).1
    simpa only [HermitianMat.mat_add, HermitianMat.mat_sub, HermitianMat.mat_smul,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.add_re,
      Complex.sub_re, Complex.smul_re, smul_eq_mul, hi, Complex.one_re, mul_one]
      using hdre
  have hrow : ((H ^ 2).mat i i).re =
      (∑ j ∈ Finset.univ.erase i, Complex.normSq (H.mat i j)) + 1 := by
    rw [HermitianMat.mat_pow, pow_two, Matrix.mul_apply, Complex.re_sum]
    calc
      ∑ j, (H.mat i j * H.mat j i).re = ∑ j, Complex.normSq (H.mat i j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← H.H.apply j i, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      _ = (∑ j ∈ Finset.univ.erase i, Complex.normSq (H.mat i j)) + 1 := by
        have hs := Finset.sum_erase_add Finset.univ
          (fun j => Complex.normSq (H.mat i j)) (Finset.mem_univ i)
        simpa only [hi, map_one] using hs.symm
  rw [hrow] at hdiag
  have him : (H.sqrt.mat i i).im = 0 := H.sqrt.complex_im_eq_zero i
  rw [Complex.normSq_apply, him, mul_zero, add_zero]
  nlinarith [sq_nonneg ((H.sqrt.mat i i).re - 1)]

end Qatlib.Concepts.MbqcFlow.FlowDecision
