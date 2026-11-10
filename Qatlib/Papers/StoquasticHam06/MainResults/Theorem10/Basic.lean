/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Theorem10

def pptMatrix {n : ℕ} (H : QMatrix n) (q : ℚ) : QMatrix n :=
  fun x y => (1 / 2) * ((if x = y then 1 else 0) - H x y / q)

theorem pptMatrix_nonneg {n : ℕ} (H : QMatrix n) (q : ℚ) (hq : 0 < q)
    (hoff : ∀ x y : Sigma n, x ≠ y → H x y ≤ 0)
    (hdiag : ∀ x : Sigma n, H x x ≤ q) :
    ∀ x y : Sigma n, 0 ≤ QMatrix.toReal (pptMatrix H q) x y := by
  intro x y
  unfold QMatrix.toReal pptMatrix
  have hq' : (0 : ℚ) < q := hq
  have key : (0 : ℚ) ≤ (1 / 2) * ((if x = y then 1 else 0) - H x y / q) := by
    by_cases hxy : x = y
    · subst hxy
      have hit : (if x = x then (1 : ℚ) else 0) = 1 := if_pos rfl
      rw [hit]
      have hle : H x x / q ≤ 1 := by
        rw [div_le_one hq']
        exact hdiag x
      have h1 : (0 : ℚ) ≤ 1 - H x x / q := by linarith
      have hpos : (0 : ℚ) < 1 / 2 := by norm_num
      nlinarith [h1, hpos]
    · rw [if_neg hxy]
      have hHq : H x y / q ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (hoff x y hxy) hq'.le
      have h1 : (0 : ℚ) ≤ - H x y / q := by
        have := neg_nonneg.mpr hHq
        rwa [← neg_div] at this
      have hpos : (0 : ℚ) < 1 / 2 := by norm_num
      nlinarith [h1, hpos]
  exact_mod_cast key

end Qatlib.Papers.StoquasticHam06.MainResults.Theorem10
