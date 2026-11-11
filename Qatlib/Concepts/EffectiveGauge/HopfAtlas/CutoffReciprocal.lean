/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Executed reciprocal majorants for the actual transition denominator -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of cutoff Denominator in the Hopf Atlas construction. -/
noncomputable def cutoffDenominator (x : ℝ) : ℝ := expNegInvGlue x+expNegInvGlue (1-x)
/-- Definition of cutoff Reciprocal in the Hopf Atlas construction. -/
noncomputable def cutoffReciprocal (x : ℝ) : ℝ := (cutoffDenominator x)⁻¹

/-- Definition of cutoff Reciprocal Majorant in the Hopf Atlas construction. -/
def cutoffReciprocalMajorant : ℕ → ℕ
  | 0 => 8
  | n+1 => 8*∑ j : Fin (n+1), (n+1).choose (j.val+1)*
      (2*cutoffBumpMajorant (j.val+1))*cutoffReciprocalMajorant (n-j.val)
termination_by n => n

noncomputable section
open scoped ContDiff

/-- Original `cutoffDenominator_pos` guarantee for the `CutoffReciprocal` construction; the complete source hypotheses are retained. -/
theorem cutoffDenominator_pos (x : ℝ) : 0<cutoffDenominator x :=
  Real.smoothTransition.pos_denom x

/-- Original `contDiff_cutoffDenominator` guarantee for the `CutoffReciprocal` construction; the complete source hypotheses are retained. -/
theorem contDiff_cutoffDenominator {n : ℕ∞} : ContDiff ℝ n cutoffDenominator :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- Original `contDiff_cutoffReciprocal` guarantee for the `CutoffReciprocal` construction; the complete source hypotheses are retained. -/
theorem contDiff_cutoffReciprocal {n : ℕ∞} : ContDiff ℝ n cutoffReciprocal :=
  contDiff_cutoffDenominator.inv (fun x => (cutoffDenominator_pos x).ne')

/-- Original `cutoffDenominator_lower` guarantee for the `CutoffReciprocal` construction; the complete source hypotheses are retained. -/
theorem cutoffDenominator_lower (x : ℝ) : (1/8 : ℝ) ≤ cutoffDenominator x := by
  have he : Real.exp 1 ≤ (11/4 : ℝ) :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  have hs : (Real.exp 1)^2 ≤ (11/4 : ℝ)^2 :=
    (sq_le_sq₀ (Real.exp_pos 1).le (by norm_num)).mpr he
  have he2 : Real.exp (2 : ℝ) ≤ 8 := by
    rw [show (2 : ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith
  have hhalf : (1/8 : ℝ) ≤ expNegInvGlue (1/2) := by
    have hg : expNegInvGlue (1/2)=Real.exp (-2) := by norm_num [expNegInvGlue]
    rw [hg,Real.exp_neg,one_div]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ)<8) (Real.exp_pos 2)).mpr he2
  apply hhalf.trans
  rcases le_total (1/2 : ℝ) x with hx|hx
  · have h := expNegInvGlue.monotone hx
    have h' := expNegInvGlue.nonneg (1-x)
    dsimp only [cutoffDenominator]
    linarith
  · have h := expNegInvGlue.monotone (show (1/2 : ℝ) ≤ 1-x by linarith)
    have h' := expNegInvGlue.nonneg x
    dsimp only [cutoffDenominator]
    linarith

/-- Original `cutoffReciprocal_abs_le` guarantee for the `CutoffReciprocal` construction; the complete source hypotheses are retained. -/
theorem cutoffReciprocal_abs_le (x : ℝ) : |cutoffReciprocal x| ≤ 8 := by
  rw [cutoffReciprocal,abs_inv,abs_of_pos (cutoffDenominator_pos x)]
  rw [← one_div]
  apply (div_le_iff₀ (cutoffDenominator_pos x)).mpr
  linarith [cutoffDenominator_lower x]

/-- Original `cutoffDenominator_derivative_bound` guarantee for the `CutoffReciprocal` construction; the complete source hypotheses are retained. -/
theorem cutoffDenominator_derivative_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n cutoffDenominator x| ≤ 2*(cutoffBumpMajorant n : ℝ) := by
  have hf : ContDiffAt ℝ n expNegInvGlue x := expNegInvGlue.contDiff.contDiffAt
  have hg : ContDiffAt ℝ n (fun y => expNegInvGlue (1-y)) x :=
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)).contDiffAt
  change |iteratedDeriv n (fun y => expNegInvGlue y+expNegInvGlue (1-y)) x| ≤ _
  rw [iteratedDeriv_fun_add hf hg,iteratedDeriv_comp_const_sub]
  change |iteratedDeriv n expNegInvGlue x+(-1 : ℝ)^n*iteratedDeriv n expNegInvGlue (1-x)| ≤ _
  calc
    _ ≤ |iteratedDeriv n expNegInvGlue x|+|iteratedDeriv n expNegInvGlue (1-x)| := by
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using
        abs_add_le (iteratedDeriv n expNegInvGlue x)
          ((-1 : ℝ)^n*iteratedDeriv n expNegInvGlue (1-x))
    _ ≤ (cutoffBumpMajorant n : ℝ)+(cutoffBumpMajorant n : ℝ) :=
      add_le_add (iteratedDeriv_expNegInvGlue_abs_le n x) (iteratedDeriv_expNegInvGlue_abs_le n (1-x))
    _ = _ := by ring

/-- The highest derivative of the reciprocal is solved from H*(1/H)=1;
only strictly lower reciprocal derivatives enter its computed budget. -/
theorem cutoffReciprocal_derivative_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n cutoffReciprocal x| ≤ (cutoffReciprocalMajorant n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [iteratedDeriv_zero,cutoffReciprocalMajorant] using cutoffReciprocal_abs_le x
    | succ n =>
      let S := ∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*
        iteratedDeriv (j+1) cutoffDenominator x*iteratedDeriv (n-j) cutoffReciprocal x
      let T := ∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*
        (2*(cutoffBumpMajorant (j+1) : ℝ))*(cutoffReciprocalMajorant (n-j) : ℝ)
      have hp : (fun y => cutoffDenominator y*cutoffReciprocal y)=fun _ => (1 : ℝ) := by
        funext y
        exact mul_inv_cancel₀ (cutoffDenominator_pos y).ne'
      have hH : ContDiffAt ℝ (n+1) cutoffDenominator x := contDiff_cutoffDenominator.contDiffAt
      have hJ : ContDiffAt ℝ (n+1) cutoffReciprocal x := contDiff_cutoffReciprocal.contDiffAt
      have hprod := iteratedDeriv_fun_mul hH hJ
      rw [hp] at hprod
      simp only [iteratedDeriv_const,if_neg (show n+1≠0 by omega)] at hprod
      rw [Finset.sum_range_succ'] at hprod
      simp only [Nat.choose_zero_right,Nat.cast_one,iteratedDeriv_zero,
        one_mul,Nat.sub_zero,Nat.add_sub_add_right] at hprod
      have hmain : cutoffDenominator x*iteratedDeriv (n+1) cutoffReciprocal x+S=0 := by
        dsimp only [S]
        linarith [hprod]
      have heq : iteratedDeriv (n+1) cutoffReciprocal x= -cutoffReciprocal x*S := by
        apply mul_left_cancel₀ (cutoffDenominator_pos x).ne'
        have hid : cutoffDenominator x*(-cutoffReciprocal x*S)= -S := by
          dsimp only [cutoffReciprocal]
          field_simp [(cutoffDenominator_pos x).ne']
        rw [hid]
        linarith [hmain]
      have hS : |S| ≤ T := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (cutoffDenominator_derivative_bound (j+1) x) (Nat.cast_nonneg _))
          (ih (n-j) (by omega)) (abs_nonneg _) (by positivity)
      rw [heq,abs_mul,abs_neg]
      calc
        _ ≤ 8*T := mul_le_mul (cutoffReciprocal_abs_le x) hS (abs_nonneg _) (by norm_num)
        _ = (cutoffReciprocalMajorant (n+1) : ℝ) := by
          conv_rhs => rw [cutoffReciprocalMajorant.eq_def]
          simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
          dsimp only [T]
          rw [Finset.sum_range]

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
