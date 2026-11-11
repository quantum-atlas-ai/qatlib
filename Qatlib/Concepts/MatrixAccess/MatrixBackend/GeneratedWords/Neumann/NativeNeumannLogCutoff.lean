/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitReciprocalCutoff
import Mathlib.Data.Nat.Log
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

/-!
Logarithmic cutoffs for an actual native Neumann program.

 The proofs and resource boundaries
are retained; the results do not establish the entire original problem or
additional gate and bit complexity claims.
-/
/-! A logarithmic explicit reciprocal-tail cutoff. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.LogarithmicReciprocalTail


/-- One K² block of the exact geometric tail decreases by at least one half. -/
private theorem geometric_block_half (K : ℕ) (hK : 2 ≤ K) :
    (1 - (K : ℝ)⁻¹^2)^(K*K) ≤ ((2:ℝ)⁻¹) := by
  have hKp : (0:ℝ) < (K:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hKqq : (0:ℝ) < (K:ℝ)*(K:ℝ) := by positivity
  have hinv2 : (K:ℝ)⁻¹^2 = ((K:ℝ)*(K:ℝ))⁻¹ := by rw [inv_pow, sq]
  have hKsq : (1:ℝ) ≤ (K:ℝ)*(K:ℝ) := by
    have hn : (1:ℕ) ≤ K*K := by nlinarith
    exact_mod_cast hn
  have hq1 : ((K:ℝ)*(K:ℝ))⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ hKqq (by norm_num : (0:ℝ) < 1)).mpr hKsq
  have hb0 : (0:ℝ) ≤ 1 - (K:ℝ)⁻¹^2 := by rw [hinv2]; linarith
  have he2 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  have hle : 1 - ((K:ℝ)*(K:ℝ))⁻¹ ≤ Real.exp (-((K:ℝ)*(K:ℝ))⁻¹) := by
    have h := Real.add_one_le_exp (-((K:ℝ)*(K:ℝ))⁻¹)
    linarith
  have hb0' : (0:ℝ) ≤ 1 - ((K:ℝ)*(K:ℝ))⁻¹ := by rw [← hinv2]; exact hb0
  calc
    (1 - (K:ℝ)⁻¹^2)^(K*K)
        = (1 - ((K:ℝ)*(K:ℝ))⁻¹)^(K*K) := by rw [hinv2]
    _ ≤ (Real.exp (-((K:ℝ)*(K:ℝ))⁻¹))^(K*K) :=
      pow_le_pow_left₀ hb0' hle _
    _ = Real.exp (((K*K : ℕ):ℝ) * -((K:ℝ)*(K:ℝ))⁻¹) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(1:ℝ)) := by rw [Nat.cast_mul]; field_simp
    _ = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    _ ≤ ((2:ℝ)⁻¹) := (inv_le_inv₀ (by positivity) (by norm_num)).mpr he2

/-- K²(k+ceil(log₂ K)+2) achieves the exact geometric tail budget. -/
theorem logarithmic_reciprocal_tail (K k : ℕ) (hK : 2 ≤ K) :
    Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (K:ℝ)⁻¹ (K*K*(k+Nat.clog 2 K+2)) ≤ ((2:ℝ)⁻¹)^(k+2) := by
  have hKp : (0:ℝ) < (K:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hK)
  have hi : (K:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hKp).mpr hK1
  have hb0 : (0:ℝ) ≤ 1 - (K:ℝ)⁻¹^2 := by
    nlinarith [inv_nonneg.mpr hKp.le, sq_nonneg ((K:ℝ)⁻¹-1)]
  have hbm := geometric_block_half K hK
  have hp0 : (0:ℝ) ≤ (1 - (K:ℝ)⁻¹^2)^(K*K) := pow_nonneg hb0 _
  have hmono := pow_le_pow_left₀ hp0 hbm (k+Nat.clog 2 K+2)
  have hcast : (K:ℝ) ≤ (2:ℝ)^(Nat.clog 2 K) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) K
  have hhalf : ((2:ℝ)⁻¹)^(Nat.clog 2 K) * (K:ℝ) ≤ 1 := by
    rw [inv_pow]
    exact (inv_mul_le_one₀ (by positivity)).mpr hcast
  unfold Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError
  rw [div_eq_mul_inv, inv_inv, pow_mul]
  calc
    ((1 - (K:ℝ)⁻¹^2)^(K*K))^(k+Nat.clog 2 K+2) * (K:ℝ)
        ≤ ((2:ℝ)⁻¹)^(k+Nat.clog 2 K+2) * (K:ℝ) :=
      mul_le_mul_of_nonneg_right hmono hKp.le
    _ = ((2:ℝ)⁻¹)^(k+2) * (((2:ℝ)⁻¹)^(Nat.clog 2 K) * (K:ℝ)) := by
      have he : k+Nat.clog 2 K+2 = (k+2)+Nat.clog 2 K := by omega
      rw [he, pow_add]
      ring
    _ ≤ ((2:ℝ)⁻¹)^(k+2) * 1 :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = _ := mul_one _

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.LogarithmicReciprocalTail
