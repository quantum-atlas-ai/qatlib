/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelRegulatorZeros
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD

theorem integerContourNumerator_ne_zero {a : ℝ} (ha : 0 < a) :
    ((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) ≠ 0 := by
  have he : Real.exp (-2 * Real.pi * a) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  exact_mod_cast (sub_ne_zero.mpr (ne_of_lt he))

theorem integerContourKernel_eq_denominator (m : ℕ) (a : ℝ) (z : ℂ) :
    integerContourKernel m a z =
      (Real.exp (-2 * Real.pi * a) - 1 : ℝ) / integerContourDenominator m a z := rfl

theorem integerContourIntegrand_eq_denominator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (m : ℕ) (a : ℝ) (U : ℂ → E) (z : ℂ) :
    integerContourIntegrand m a U z = (integerContourDenominator m a z)⁻¹ •
      (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) • U z) := by
  rw [integerContourIntegrand, integerContourKernel_eq_denominator, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

theorem integerContour_coefficient_neg_I (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (integerContourDenominator m a) (-Complex.I)) = 1 := by
  rw [(integerContourDenominator_hasDerivAt_neg_I m ha).deriv]
  exact div_self (integerContourNumerator_ne_zero ha)

theorem integerContour_coefficient_lattice (m : ℕ) {a : ℝ} (ha : 0 < a) (k : ℤ) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (integerContourDenominator m a) (((k : ℝ) / a : ℝ) : ℂ)) =
        -integerWeight m a ((k : ℝ) / a) := by
  rw [(integerContourDenominator_hasDerivAt_lattice m ha k).deriv]
  simp only [integerWeight, div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

theorem integerContour_coefficient_top (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (integerContourDenominator m a) (2 * Complex.I)) =
        integerTopResidueCoefficient m a := by
  rw [(integerContourDenominator_hasDerivAt_top m ha).deriv]
  simp only [integerTopResidueCoefficient, latticePoleFactor, integerLatticeExponential,
    div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

theorem integerContour_coefficient_row (m : ℕ) {a : ℝ} (ha : 0 < a) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (integerContourDenominator m a) ((r : ℂ) + Complex.I)) =
        integerRowResidueCoefficient m a r := by
  rw [(integerContourDenominator_hasDerivAt_row m ha r hr).deriv]
  simp only [integerRowResidueCoefficient, latticePoleFactor, integerLatticeExponential,
    div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
