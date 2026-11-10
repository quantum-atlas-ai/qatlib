/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
open scoped BigOperators

variable {n : ℕ}

theorem parseval_identity (F : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), uniformFourierCoeff S F ^ 2 =
      uniformExpect (fun x => F x ^ 2) := by
  unfold uniformExpect
  rw [sum_sq_eq_mul_sum_uniformFourierCoeff_sq]
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]

theorem parseval_boolean (F : (Fin n → Bool) → ℝ)
    (hF : ∀ x, F x ^ 2 = 1) :
    ∑ S : Finset (Fin n), uniformFourierCoeff S F ^ 2 = 1 := by
  rw [parseval_identity]
  unfold uniformExpect
  have hsum : ∑ x : Fin n → Bool, F x ^ 2 = (2 : ℝ) ^ n := by
    rw [Finset.sum_congr rfl (fun x _ => hF x)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hsum, inv_mul_cancel₀ (by positivity)]

theorem fsWeight_total (f : (Fin n → Bool) → Bool) :
    ∑ S : Finset (Fin n), fsWeight f S = 1 := by
  unfold fsWeight signCoeff
  exact parseval_boolean (signFun f) (fun x => by unfold signFun; split_ifs <;> norm_num)

end Qatlib.Papers.JuntaLearning07.MainResults
