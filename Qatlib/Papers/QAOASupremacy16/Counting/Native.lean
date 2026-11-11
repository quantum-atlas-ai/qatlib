/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.Counting.Source
import Qatlib.Papers.QAOASupremacy16.CircuitModel.Native

/-!
# Recovering cost counts from actual matrix elements

`actual_matrix_elements_recover_count` expresses every level-set count of a cost bounded by `m`
as an inverse Fourier sum of actual circuit matrix elements at `m + 1` angles. The identity
connects the finite circuit construction with the counting transform.

This development accompanies the study of QAOA sampling and postselection in [FarhiHarrow2016].

## Main statements

* `actual_matrix_elements_recover_count`: For a natural-valued cost bounded by `m`, its count at
  value `v < m + 1` equals `2^n / (m + 1)` times the inverse Fourier sum of its actual matrix
  elements at angles `phaseAngle m r`.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOASupremacy16.Counting
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.CircuitDefs

/-- For a natural-valued cost bounded by `m`, its count at value `v < m + 1` equals `2^n / (m +
1)` times the inverse Fourier sum of its actual matrix elements at angles `phaseAngle m r`.
See [FarhiHarrow2016]. -/
theorem actual_matrix_elements_recover_count (n m : ℕ) (C : Reg n→ℕ)
    (hC : ∀ z, C z ≤ m) (v : Fin (m+1)) :
    (countVec C v.val:ℂ)=(((2:ℂ)^n)*(((m+1:ℕ):ℂ)⁻¹))*
      ∑ r : Fin (m+1),matrixElement (phaseAngle m r.val) C*dftChar (m+1) (v.val:ℤ) r.val := by
  simp_rw [matrixElement_eq_cspAmplitude]
  exact countVec_eq_inverse_transform n m C hC v
end Qatlib.Papers.QAOASupremacy16.Counting
