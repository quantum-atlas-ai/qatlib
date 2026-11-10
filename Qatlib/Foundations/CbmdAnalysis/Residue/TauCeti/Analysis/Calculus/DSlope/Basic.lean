/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.DSlope
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace TauCeti

theorem dslope_comm {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) : dslope f a b = dslope f b a := by
  rcases eq_or_ne b a with rfl | h
  · rfl
  · rw [dslope_of_ne f h, dslope_of_ne f h.symm, slope_comm]

lemma norm_dslope_eq_one_of_norm_sub_map_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {x y : 𝕜} (hxy : y ≠ x)
    (hnorm : ‖g y - g x‖ = ‖y - x‖) : ‖dslope g x y‖ = 1 := by
  rw [dslope_of_ne _ hxy, slope_def_module, norm_smul, norm_inv, hnorm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]

theorem sum_add_pow_sub_smul_iterate_dslope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) (n : ℕ) :
    ∑ j ∈ Finset.range n, (b - a) ^ j • (Function.swap dslope a)^[j] f a +
      (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ', Function.iterate_succ_apply, pow_succ', mul_smul,
      ← Finset.smul_sum, pow_zero, one_smul, Function.iterate_zero_apply]
    rw [add_right_comm, ← smul_add, ih]
    exact eq_sub_iff_add_eq.1 (sub_smul_dslope f a b)

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
