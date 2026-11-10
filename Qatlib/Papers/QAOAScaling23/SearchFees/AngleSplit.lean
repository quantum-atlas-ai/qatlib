/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.FeeRecurrence
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.SearchFees

theorem lowQ_double_sine (θ:ℝ) (h0:0<θ) (h1:θ<Real.pi/2) (hQ:(Real.sin θ)^2≤1/2) :
    Real.sin θ≤Real.sin (2*θ) := by
  have hs:0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc:0<Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],h1⟩
  have hid:=Real.sin_sq_add_cos_sq θ
  have hh:(1/2:ℝ)≤Real.cos θ := by nlinarith
  rw [Real.sin_two_mul]
  nlinarith

theorem lowQ_source_cap (M:ℕ) (θ:ℝ) (h0:0<θ) (h1:θ<Real.pi/2)
    (hQ:(Real.sin θ)^2≤1/2) (hcap:1≤(M:ℝ)*Real.sin θ) :
    1≤(M:ℝ)*Real.sin (2*θ) :=
  hcap.trans (mul_le_mul_of_nonneg_left (lowQ_double_sine θ h0 h1 hQ) (Nat.cast_nonneg M))
end Qatlib.Papers.QAOAScaling23.SearchFees
