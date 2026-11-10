/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.Counting.Source
import Qatlib.Papers.QAOASupremacy16.CircuitModel.Native
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOASupremacy16.Counting
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.CircuitDefs

theorem actual_matrix_elements_recover_count (n m : ℕ) (C : Reg n→ℕ)
    (hC : ∀ z, C z ≤ m) (v : Fin (m+1)) :
    (countVec C v.val:ℂ)=(((2:ℂ)^n)*(((m+1:ℕ):ℂ)⁻¹))*
      ∑ r : Fin (m+1),matrixElement (phaseAngle m r.val) C*dftChar (m+1) (v.val:ℤ) r.val := by
  simp_rw [matrixElement_eq_cspAmplitude]
  exact countVec_eq_inverse_transform n m C hC v
end Qatlib.Papers.QAOASupremacy16.Counting
