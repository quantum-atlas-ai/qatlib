/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # The literal single-entry Haar-tail envelope

Aaronson--Arkhipov, arXiv:1011.3245v1, Lemma 38. This proves the exact
algebraic envelope occurring in the historical source. Establishing that
an actual Haar entry has the displayed law remains a separate measure
transport; it is not an input probability conclusion here.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.HaarTail

/-- The original explicit single-entry tail envelope, without an assertion that it is a Haar law. -/
def sTail (m n : ℕ) (k : ℝ) : ℝ :=
  (n : ℝ)^2 * (1-k/((m : ℝ)*(n : ℝ)^2))^(m-1)

/-- The complete original algebraic Haar-tail target follows from the exponential bound. -/
theorem envelope (m n : ℕ) (k : ℝ) (hm : 2 ≤ m) (hk : 0 ≤ k)
    (hk1 : k ≤ (m : ℝ)*(n : ℝ)^2) :
    sTail m n k ≤ (n : ℝ)^2 * Real.exp (-(k/(2*(n : ℝ)^2))) := by
  by_cases hn : n = 0
  · subst n
    simp [sTail]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hspos : (0 : ℝ) < (n : ℝ)^2 := sq_pos_of_pos hnpos
  have hdpos : (0 : ℝ) < (m : ℝ)*(n : ℝ)^2 := mul_pos hmpos hspos
  let x := k/((m : ℝ)*(n : ℝ)^2)
  have hx0 : 0 ≤ x := div_nonneg hk hdpos.le
  have hx1 : x ≤ 1 := (div_le_one hdpos).mpr hk1
  have he : 1-x ≤ Real.exp (-x) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x)
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hx1) he (m-1)
  rw [← Real.exp_nat_mul] at hp
  have hcast : ((m-1 : ℕ) : ℝ) = (m : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hex : ((m-1 : ℕ) : ℝ)*(-x) ≤ -(k/(2*(n : ℝ)^2)) := by
    rw [hcast]
    dsimp [x]
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    field_simp
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hmR)]
  have hc := hp.trans (Real.exp_le_exp.mpr hex)
  exact mul_le_mul_of_nonneg_left hc (sq_nonneg (n : ℝ))

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.HaarTail
