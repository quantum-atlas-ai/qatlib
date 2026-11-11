/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffReciprocal

/-! # Computed derivative bounds for the actual smooth transition and unit cutoff -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of cutoff Transition Majorant in the Hopf Atlas construction. -/
def cutoffTransitionMajorant (n : ℕ) : ℕ :=
  ∑ j ∈ range (n+1), n.choose j*cutoffBumpMajorant j*cutoffReciprocalMajorant (n-j)

/-- Definition of cutoff Unit Majorant in the Hopf Atlas construction. -/
def cutoffUnitMajorant (eta : ℚ) (n : ℕ) : ℚ :=
  if n=0 then 1 else (4/eta)^n*(cutoffTransitionMajorant n : ℚ)

noncomputable section
open scoped ContDiff

/-- Definition of unit Gluing Cutoff in the Hopf Atlas construction. -/
def unitGluingCutoff (eta : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x-(1-eta/2))/(eta/4))

/-- Original `contDiff_unitGluingCutoff` guarantee for the `CutoffTransition` construction; the complete source hypotheses are retained. -/
theorem contDiff_unitGluingCutoff {n : ℕ∞} (eta : ℝ) : ContDiff ℝ n (unitGluingCutoff eta) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- Original `cutoffTransition_derivative_bound` guarantee for the `CutoffTransition` construction; the complete source hypotheses are retained. -/
theorem cutoffTransition_derivative_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n Real.smoothTransition x| ≤ (cutoffTransitionMajorant n : ℝ) := by
  have heq : Real.smoothTransition=fun y => expNegInvGlue y*cutoffReciprocal y := by
    funext y
    simp only [Real.smoothTransition,cutoffReciprocal,cutoffDenominator,div_eq_mul_inv]
  have hg : ContDiffAt ℝ n expNegInvGlue x := expNegInvGlue.contDiff.contDiffAt
  have hJ : ContDiffAt ℝ n cutoffReciprocal x := contDiff_cutoffReciprocal.contDiffAt
  rw [heq,iteratedDeriv_fun_mul hg hJ]
  calc
    _ ≤ ∑ j ∈ range (n+1),
        |(n.choose j : ℝ)*iteratedDeriv j expNegInvGlue x*iteratedDeriv (n-j) cutoffReciprocal x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (n+1),
        (n.choose j : ℝ)*(cutoffBumpMajorant j : ℝ)*(cutoffReciprocalMajorant (n-j) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (iteratedDeriv_expNegInvGlue_abs_le j x) (Nat.cast_nonneg _))
        (cutoffReciprocal_derivative_bound (n-j) x) (abs_nonneg _) (by positivity)
    _ = (cutoffTransitionMajorant n : ℝ) := by
      simp only [cutoffTransitionMajorant,Nat.cast_sum,Nat.cast_mul]

/-- The zero-order cutoff bound is one, rather than the looser product
estimate. Positive orders retain the exact affine slope 4/eta. -/
theorem unitGluingCutoff_derivative_bound (eta : ℚ) (he : 0<eta) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (unitGluingCutoff (eta : ℝ)) x| ≤ (cutoffUnitMajorant eta n : ℝ) := by
  have heR : (0 : ℝ)<eta := Rat.cast_pos.mpr he
  by_cases hn : n=0
  · subst n
    rw [iteratedDeriv_zero]
    rw [show cutoffUnitMajorant eta 0=1 from rfl,Rat.cast_one]
    rw [unitGluingCutoff,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · let a : ℝ := 4/(eta : ℝ)
    let b : ℝ := 1-(eta : ℝ)/2
    have ha : 0<a := div_pos (by norm_num) heR
    have heq : unitGluingCutoff (eta : ℝ)=
        fun y => (fun z => Real.smoothTransition (a*z)) (y-b) := by
      funext y
      unfold unitGluingCutoff
      congr 1
      dsimp only [a,b]
      field_simp [heR.ne']
    rw [heq,iteratedDeriv_comp_sub_const (n := n)
      (f := fun z => Real.smoothTransition (a*z)) (s := b)]
    change |iteratedDeriv n (fun z => Real.smoothTransition (a*z)) (x-b)| ≤ _
    have hs : ContDiff ℝ n Real.smoothTransition := Real.smoothTransition.contDiff
    rw [congrFun (iteratedDeriv_comp_const_mul hs a) (x-b),abs_mul,abs_pow,abs_of_pos ha]
    calc
      _ ≤ a^n*(cutoffTransitionMajorant n : ℝ) :=
        mul_le_mul_of_nonneg_left (cutoffTransition_derivative_bound n (a*(x-b))) (pow_nonneg ha.le _)
      _ = (cutoffUnitMajorant eta n : ℝ) := by
        simp only [cutoffUnitMajorant,if_neg hn,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
          Rat.cast_ofNat,Rat.cast_natCast]
        rfl

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
