/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelPoleCoefficients

/-!
# Strict positivity of integer weight mass

For positive spacing, `integerWeight` never vanishes at a real argument. Consequently the sum of
weight norms over any nonempty finite lattice index set is strictly positive.

The module specializes this fact to symmetric cutoffs and their attached subtype sums, providing
nonzero normalization masses for the LCU coefficients of [WangEtAl2026].

## Main statements

* `integerWeight_ne_zero`: proves nonvanishing of every real weight.
* `integerWeight_cutoff_mass_pos`: proves positivity for symmetric finite sums.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

/-- For positive spacing, the integer weight is nonzero at every real point. -/
theorem integerWeight_ne_zero (m : ℕ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    integerWeight m a x ≠ 0 := by
  unfold integerWeight
  apply div_ne_zero (integerContourNumerator_ne_zero ha)
  apply mul_ne_zero _ (integerRegulator_real_ne_zero m x)
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast ha.ne')
  · intro h
    have hi := congrArg Complex.im h
    norm_num at hi

/-- For positive spacing and a nonempty finite set of integer indices, the sum of the sampled
weight norms is strictly positive. -/
theorem integerWeight_finite_mass_pos (m : ℕ) {a : ℝ} (ha : 0 < a)
    (s : Finset ℤ) (hs : s.Nonempty) :
    0 < ∑ k ∈ s, ‖integerWeight m a ((k : ℝ) / a)‖ := by
  exact Finset.sum_pos (fun k _ => norm_pos_iff.mpr (integerWeight_ne_zero m ha _)) hs

/-- For positive spacing, the sum of the weight norms over any symmetric cutoff interval is
strictly positive. -/
theorem integerWeight_cutoff_mass_pos (m : ℕ) {a : ℝ} (ha : 0 < a) (K : ℕ) :
    0 < ∑ k ∈ Finset.Icc (-(K : ℤ)) K, ‖integerWeight m a ((k : ℝ) / a)‖ := by
  exact integerWeight_finite_mass_pos m ha _ ⟨0, by simp⟩

/-- For positive spacing, the sum of sampled weight norms over the subtype of retained cutoff
indices is strictly positive. -/
theorem integerWeight_attached_mass_pos (m : ℕ) {a : ℝ} (ha : 0 < a) (K : ℕ) :
    0 < ∑ k : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) K},
      ‖integerWeight m a ((k.val : ℝ) / a)‖ := by
  haveI : Nonempty {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) K} := ⟨⟨0, by simp⟩⟩
  exact Finset.sum_pos
      (fun k _ => norm_pos_iff.mpr (integerWeight_ne_zero m ha _)) Finset.univ_nonempty

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
