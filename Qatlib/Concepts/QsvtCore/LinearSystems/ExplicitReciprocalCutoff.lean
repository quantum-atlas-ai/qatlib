/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalApproximation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
set_option autoImplicit false

def explicitInverseCutoff (κ k : ℕ) : ℕ := κ * κ * (k + κ + 1)

theorem explicit_inverse_cutoff_integer_formula (κ k : ℕ) :
    explicitInverseCutoff κ k = κ*κ*(k+κ+1) ∧
      (0<κ → 0<explicitInverseCutoff κ k) :=
  ⟨rfl, fun hκ => Nat.mul_pos (Nat.mul_pos hκ hκ) (Nat.succ_pos _)⟩

private theorem nat_lt_two_pow (m : ℕ) : m < (2:ℕ)^m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.pow_succ]
    have h1 : (1:ℕ) ≤ (2:ℕ)^n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)
    omega

private theorem half_pow_succ_mul_le_one (κ : ℕ) :
    ((2:ℝ)⁻¹)^(κ+1) * (κ:ℝ) ≤ 1 := by
  have hcast : (κ:ℝ) ≤ ((2:ℝ)^(κ+1)) := by
    have h : (κ:ℝ) ≤ ((2:ℝ)^κ) := by exact_mod_cast (nat_lt_two_pow κ).le
    calc (κ:ℝ) ≤ ((2:ℝ)^κ) := h
      _ ≤ ((2:ℝ)^(κ+1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [inv_pow]
  exact (inv_mul_le_one₀ (by positivity)).mpr hcast

theorem explicit_inverse_geometric_precision :
    ∀ (κ k : ℕ), 0<κ →
      reciprocalError (κ:ℝ)⁻¹ (explicitInverseCutoff κ k) ≤ (2:ℝ)⁻¹^k := by
  intro κ k hκ
  have hκp : (0:ℝ) < (κ:ℝ) := Nat.cast_pos.mpr hκ
  have hκqq : (0:ℝ) < (κ:ℝ)*(κ:ℝ) := by positivity
  have hinv2 : (κ:ℝ)⁻¹^2 = ((κ:ℝ)*(κ:ℝ))⁻¹ := by rw [inv_pow, sq]
  rcases Nat.lt_or_ge κ 2 with hκ2 | hκ2
  · have hκ1 : κ = 1 := by omega
    subst hκ1
    have hn : (1:ℕ)*1*(k+1+1) ≠ 0 := by omega
    unfold reciprocalError explicitInverseCutoff
    simp only [Nat.cast_one, inv_one, one_pow, sub_self]
    rw [zero_pow hn]
    simp only [zero_div]
    positivity
  · have hκκ : (4:ℕ) ≤ κ*κ := by
      have h := Nat.mul_le_mul hκ2 hκ2
      simpa using h
    have hκsq : (4:ℝ) ≤ (κ:ℝ)*(κ:ℝ) := by exact_mod_cast hκκ
    have hκ1 : (1:ℝ) ≤ (κ:ℝ)*(κ:ℝ) := by nlinarith
    have hq4 : ((κ:ℝ)*(κ:ℝ))⁻¹ ≤ (4:ℝ)⁻¹ :=
      (inv_le_inv₀ hκqq (by norm_num)).mpr hκsq
    have hq1 : ((κ:ℝ)*(κ:ℝ))⁻¹ ≤ 1 :=
      ((inv_le_inv₀ hκqq (by norm_num)).mpr hκ1).trans (by norm_num)
    have hb0 : (0:ℝ) ≤ 1 - (κ:ℝ)⁻¹^2 := by rw [hinv2]; nlinarith
    have he2 : (2:ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      linarith
    have hle : 1 - ((κ:ℝ)*(κ:ℝ))⁻¹ ≤ Real.exp (-((κ:ℝ)*(κ:ℝ))⁻¹) := by
      have h := Real.add_one_le_exp (-((κ:ℝ)*(κ:ℝ))⁻¹)
      linarith
    have hb0' : (0:ℝ) ≤ 1 - ((κ:ℝ)*(κ:ℝ))⁻¹ := by rw [← hinv2]; exact hb0
    have hbm : (1 - (κ:ℝ)⁻¹^2)^(κ*κ) ≤ ((2:ℝ)⁻¹) := by
      calc (1 - (κ:ℝ)⁻¹^2)^(κ*κ)
          = (1 - ((κ:ℝ)*(κ:ℝ))⁻¹)^(κ*κ) := by rw [hinv2]
        _ ≤ (Real.exp (-((κ:ℝ)*(κ:ℝ))⁻¹))^(κ*κ) :=
            pow_le_pow_left₀ hb0' hle _
        _ = Real.exp (((κ*κ : ℕ):ℝ) * -((κ:ℝ)*(κ:ℝ))⁻¹) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(1:ℝ)) := by rw [Nat.cast_mul]; field_simp
        _ = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
        _ ≤ ((2:ℝ)⁻¹) := (inv_le_inv₀ (by positivity) (by norm_num)).mpr he2
    have hbpos : (0:ℝ) ≤ (1 - (κ:ℝ)⁻¹^2)^(κ*κ) := pow_nonneg hb0 _
    have hmono := pow_le_pow_left₀ hbpos hbm (k+κ+1)
    unfold reciprocalError explicitInverseCutoff
    have hsplit := pow_mul (1 - (κ:ℝ)⁻¹^2) (κ*κ) (k+κ+1)
    rw [div_eq_mul_inv, inv_inv]
    calc (1 - (κ:ℝ)⁻¹^2)^(κ*κ*(k+κ+1)) * (κ:ℝ)
        = ((1 - (κ:ℝ)⁻¹^2)^(κ*κ))^(k+κ+1) * (κ:ℝ) := by rw [hsplit]
      _ ≤ ((2:ℝ)⁻¹)^(k+κ+1) * (κ:ℝ) :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
      _ = ((2:ℝ)⁻¹)^k * (((2:ℝ)⁻¹)^(κ+1) * (κ:ℝ)) := by
          rw [pow_add]
          ring
      _ ≤ ((2:ℝ)⁻¹)^k * 1 :=
          mul_le_mul_of_nonneg_left (half_pow_succ_mul_le_one κ) (by positivity)
      _ = ((2:ℝ)⁻¹)^k := mul_one _

end Qatlib.Concepts.QsvtCore.LinearSystems
