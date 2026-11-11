/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrectedStat
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorSegments

/-!
# Corrected skew-Hermitian commutator scaling

This module proves `TrotterCommutatorScalingCorrected`, the corrected segmented
commutator-scaling statement associated with Theorem 11 of [ChildsEtAl2021Trotter]. For
skew-Hermitian words matching exponential coefficients through positive order `p`, it supplies
unitarity, the executed word length, and the error budget with numerator `p! * pfCommAlphaSelf
xs (p + 1)` and denominator `(p + 1)! * r ^ p`.

## Main statements

* `trotterCommutatorScalingCorrected`: proves the corrected skew-Hermitian segmented bound.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical Matrix.Norms.L2Operator

/-- The corrected commutator-scaling statement holds for segmented matched-order words with
skew-Hermitian generators, including unitarity and the word-length identity. This is the
corrected formulation associated with [Childs et al., Theorem 11][ChildsEtAl2021Trotter]. -/
theorem trotterCommutatorScalingCorrected : TrotterCommutatorScalingCorrected := by
  intro I _ _ xs H p r hp hr hxs hH hc t
  (try dsimp only)
  refine ⟨?_,?_,?_⟩
  · rw [pf_segment_word_prod]
    exact (Matrix.unitaryGroup I ℂ).pow_mem (pf_word_unitary xs (t/r) hxs) r
  · simp [List.length_flatten]
  · rw [pf_segment_word_prod]
    exact pf_matched_word_segmented_skew xs H p r t hp hr hc hxs hH
end Qatlib.Concepts.TrotterFormula.GeneralOrder
