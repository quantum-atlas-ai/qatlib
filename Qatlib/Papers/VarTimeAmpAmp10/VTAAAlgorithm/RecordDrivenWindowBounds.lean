/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmStat
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascadeAux
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.NormNum.RealSqrt
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

set_option autoImplicit false
set_option maxHeartbeats 900000
open Matrix
open scoped Classical BigOperators

variable {C : Type} [Fintype C] [DecidableEq C]

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
noncomputable section

theorem rdvt_arcsin_le_div {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Real.arcsin t ≤ t/Real.sqrt (1-t^2) := by
  have h0 : 0 ≤ Real.arcsin t := (Real.arcsin_nonneg).2 ht
  have h1 : Real.arcsin t < Real.pi/2 := (Real.arcsin_lt_pi_div_two).2 ht1
  have hs : Real.sin (Real.arcsin t) = t :=
    Real.sin_arcsin (by linarith : (-1:ℝ) ≤ t) ht1.le
  have hc : Real.cos (Real.arcsin t) = Real.sqrt (1-t^2) := Real.cos_arcsin t
  have hle := Real.le_tan h0 h1
  rwa [Real.tan_eq_sin_div_cos, hs, hc] at hle
end
noncomputable section

theorem rdvt_crossing_window {a est : ℝ} {n m : ℕ} (hm : 17 ≤ m) (hn : 3 ≤ n)
    (hest : |est-a| ≤ a/100)
    (hhigh : (n:ℝ)^2*est ≤ 3/(2*(m:ℝ))) :
    ((n:ℝ)*Real.arcsin (Real.sqrt a))^2 ≤ 8/(5*(m:ℝ)) := by
  have hm' : (17:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := le_trans (by norm_num) hm'
  have h594m : (0:ℝ) < 594*(m:ℝ) := by positivity
  have h10098 : (10098:ℝ) ≤ 594*(m:ℝ) := by nlinarith [hm1]
  have ha0 : 0 ≤ a := by
    have h4 : (0:ℝ) ≤ a/100 := le_trans (abs_nonneg _) hest
    have h5 : (100:ℝ)*(a/100) = a := by field_simp
    rw [← h5]
    positivity
  have hest0 : 0 ≤ est := by
    have h2 := (abs_le.mp hest).1
    field_simp at h2
    nlinarith [ha0, h2]
  have hae : ((n:ℝ)^2)*a*99 ≤ ((n:ℝ)^2)*est*100 := by
    have h2 := (abs_le.mp hest).1
    field_simp at h2
    have q1 : a*99 ≤ est*100 := by linarith
    have q2 := mul_le_mul_of_nonneg_right q1 (by positivity : (0:ℝ) ≤ (n:ℝ)^2)
    calc ((n:ℝ)^2)*a*99 = a*99*((n:ℝ)^2) := by ring
      _ ≤ est*100*((n:ℝ)^2) := q2
      _ = ((n:ℝ)^2)*est*100 := by ring
  have hn2 : 9 ≤ (n:ℝ)^2 := by exact_mod_cast (show (9:ℕ) ≤ n^2 by nlinarith)
  have hq1 : ((n:ℝ)^2*est)*(2*(m:ℝ)) ≤ 3 :=
    (le_div_iff₀ (by positivity : (0:ℝ) < 2*(m:ℝ))).mp hhigh
  have hest6m : est*(6*(m:ℝ)) ≤ 1 := by
    have s1 : (3:ℝ)*6 ≤ ((n:ℝ)^2)*2 := by nlinarith [hn2]
    have q4 : (est*(6*(m:ℝ)))*3 ≤ ((n:ℝ)^2*est*2)*(m:ℝ) := by
      calc (est*(6*(m:ℝ)))*3 = (est*(m:ℝ))*((3:ℝ)*6) := by ring
        _ ≤ (est*(m:ℝ))*(((n:ℝ)^2)*2) :=
          mul_le_mul_of_nonneg_left s1 (mul_nonneg hest0 (Nat.cast_nonneg m))
        _ = ((n:ℝ)^2*est*2)*(m:ℝ) := by ring
    have q5 : (est*(6*(m:ℝ)))*3 ≤ 1*3 := by
      calc (est*(6*(m:ℝ)))*3 ≤ ((n:ℝ)^2*est*2)*(m:ℝ) := q4
        _ = ((n:ℝ)^2*est)*(2*(m:ℝ)) := by ring
        _ ≤ 3 := hq1
        _ = 1*3 := by ring
    exact le_of_mul_le_mul_right q5 (by norm_num : (0:ℝ) < 3)
  have hsmall : a*(594*(m:ℝ)) ≤ 100 := by
    have p1 : a*99 ≤ est*100 := by
      have h2 := (abs_le.mp hest).1
      field_simp at h2
      linarith
    have p0 := mul_le_mul_of_nonneg_right p1 (by positivity : (0:ℝ) ≤ 6*(m:ℝ))
    have p3 : (est*100)*(6*(m:ℝ)) = (est*(6*(m:ℝ)))*100 := by ring
    have p4 : (est*(6*(m:ℝ)))*100 ≤ 1*100 := mul_le_mul_of_nonneg_right hest6m (by norm_num)
    have p2 : (a*99)*(6*(m:ℝ)) = a*(594*(m:ℝ)) := by ring
    rw [p2, p3] at p0
    linarith
  have hn2a' : ((n:ℝ)^2*a)*(33*(m:ℝ)) ≤ 50 := by
    have p1 : ((n:ℝ)^2*a*99)*(2*(m:ℝ)) ≤ ((n:ℝ)^2*est*100)*(2*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hae (by positivity)
    have p2 : ((n:ℝ)^2*est*100)*(2*(m:ℝ)) ≤ 3*(100:ℝ) := by
      have q2 := mul_le_mul_of_nonneg_right hq1 (by norm_num : (0:ℝ) ≤ 100)
      calc ((n:ℝ)^2*est*100)*(2*(m:ℝ))
          = ((n:ℝ)^2*est)*(2*(m:ℝ))*(100:ℝ) := by ring
        _ ≤ 3*(100:ℝ) := q2
    have p5 : ((n:ℝ)^2*a)*(33*(m:ℝ))*6 ≤ 50*6 := by
      calc ((n:ℝ)^2*a)*(33*(m:ℝ))*6
          = ((n:ℝ)^2*a*99)*(2*(m:ℝ)) := by ring
        _ ≤ ((n:ℝ)^2*est*100)*(2*(m:ℝ)) := p1
        _ ≤ 3*(100:ℝ) := p2
        _ = 50*6 := by ring
    exact le_of_mul_le_mul_right p5 (by norm_num : (0:ℝ) < 6)
  have ha132 : a*(132*(594*(m:ℝ))) ≤ 7*(594*(m:ℝ)) := by
    have p1 : (a*(594*(m:ℝ)))*(132:ℝ) ≤ (100:ℝ)*(132:ℝ) :=
      mul_le_mul_of_nonneg_right hsmall (by norm_num)
    have p3 : (13200:ℝ) ≤ 7*(594*(m:ℝ)) := by nlinarith [h10098]
    calc a*(132*(594*(m:ℝ))) = (a*(594*(m:ℝ)))*(132:ℝ) := by ring
      _ ≤ (100:ℝ)*(132:ℝ) := p1
      _ = (13200:ℝ) := by ring
      _ ≤ 7*(594*(m:ℝ)) := p3
  have h1a : 0 < 1-a := by
    have p2 : (100:ℝ) < (594:ℝ)*(m:ℝ) := by nlinarith [hm1]
    have p3 : a*((594:ℝ)*(m:ℝ)) < 1*((594:ℝ)*(m:ℝ)) := by
      apply lt_of_le_of_lt hsmall
      linarith
    have p4 : a < 1 := lt_of_mul_lt_mul_right p3 (le_of_lt h594m)
    linarith
  have hsa1 : Real.sqrt a < 1 := by
    have hone : ((1:ℝ))^2 = 1 := by norm_num
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1), hone]
    linarith
  have hθ : Real.arcsin (Real.sqrt a) ≤ Real.sqrt a/Real.sqrt (1-a) := by
    have h5 : (Real.sqrt a)^2 = a := Real.sq_sqrt ha0
    have q := rdvt_arcsin_le_div (Real.sqrt_nonneg a) hsa1
    rw [h5] at q
    exact q
  have hnθ : 0 ≤ (n:ℝ)*Real.arcsin (Real.sqrt a) :=
    mul_nonneg (by positivity) ((Real.arcsin_nonneg).2 (Real.sqrt_nonneg a))
  have hd1 : (0:ℝ) < Real.sqrt (1-a) := Real.sqrt_pos.mpr h1a
  have hnθ' : (n:ℝ)*Real.arcsin (Real.sqrt a) ≤ (n:ℝ)*(Real.sqrt a/Real.sqrt (1-a)) :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have hsq : ((n:ℝ)*Real.arcsin (Real.sqrt a))^2 ≤ ((n:ℝ)*(Real.sqrt a/Real.sqrt (1-a)))^2 := by
    have q := mul_self_le_mul_self hnθ hnθ'
    calc ((n:ℝ)*Real.arcsin (Real.sqrt a))^2
        = (n:ℝ)*Real.arcsin (Real.sqrt a)*((n:ℝ)*Real.arcsin (Real.sqrt a)) := by ring
      _ ≤ (n:ℝ)*(Real.sqrt a/Real.sqrt (1-a))*((n:ℝ)*(Real.sqrt a/Real.sqrt (1-a))) := q
      _ = ((n:ℝ)*(Real.sqrt a/Real.sqrt (1-a)))^2 := by ring
  have hexpand : ((n:ℝ)*(Real.sqrt a/Real.sqrt (1-a)))^2 = (n:ℝ)^2*a/(1-a) := by
    have h5 : (Real.sqrt a)^2 = a := Real.sq_sqrt ha0
    have h6 : (Real.sqrt (1-a))^2 = 1-a := Real.sq_sqrt (by linarith)
    rw [mul_pow, div_pow, h5, h6, ← mul_div_assoc]
  have hfin : (n:ℝ)^2*a/(1-a) ≤ 8/(5*(m:ℝ)) := by
    apply (div_le_div_iff₀ h1a (by positivity : (0:ℝ) < 5*(m:ℝ))).2
    have c2m : ((n:ℝ)^2*a*(33*(m:ℝ)))*5 ≤ 250 := by
      have q := mul_le_mul_of_nonneg_right hn2a' (by norm_num : (0:ℝ) ≤ 5)
      nlinarith [q]
    have c3 : ((n:ℝ)^2*a*(5*(m:ℝ)))*33 ≤ 250 := by
      have cX : ((n:ℝ)^2*a*(5*(m:ℝ)))*33 = ((n:ℝ)^2*a*(33*(m:ℝ)))*5 := by ring
      rw [cX]
      exact c2m
    have d2 : (264:ℝ)*a ≤ 14 := by
      have e2 := mul_le_mul_of_nonneg_right ha132 (by norm_num : (0:ℝ) ≤ 2)
      have e1 : (594*(m:ℝ))*((264:ℝ)*a) ≤ (594*(m:ℝ))*(14:ℝ) := by
        calc (594*(m:ℝ))*((264:ℝ)*a) = a*(132*(594*(m:ℝ)))*(2:ℝ) := by ring
          _ ≤ 7*(594*(m:ℝ))*(2:ℝ) := e2
          _ = (594*(m:ℝ))*(14:ℝ) := by ring
      exact le_of_mul_le_mul_left e1 h594m
    have last : ((n:ℝ)^2*a*(5*(m:ℝ)))*33 ≤ (8*(1-a))*33 := by
      have f1 : (8*(1-a))*33 = (264:ℝ)-264*a := by ring
      rw [f1]
      nlinarith [c3, d2]
    exact le_of_mul_le_mul_right last (by norm_num : (0:ℝ) < 33)
  exact le_trans (le_trans hsq (le_of_eq hexpand)) hfin
end
noncomputable section

theorem rdvt_window_gain {a : ℝ} {N m : ℕ} (hm : 17 ≤ m) (hN : 1 ≤ N) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1)
    (hwin : ((N:ℝ)*Real.arcsin (Real.sqrt a))^2 ≤ 8/(5*(m:ℝ))) :
    (1-4/(5*(m:ℝ)))*((N:ℝ)^2)*a ≤ (Real.sin (((N:ℝ))*Real.arcsin (Real.sqrt a)))^2 := by
  have hmR : (17:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsa1 : Real.sqrt a ≤ 1 := by
    have hq := Real.sqrt_le_sqrt ha1
    rwa [Real.sqrt_one] at hq
  set θ := Real.arcsin (Real.sqrt a) with hθd
  have hθ0 : 0 ≤ θ := (Real.arcsin_nonneg).2 (Real.sqrt_nonneg a)
  have hsin : Real.sin θ = Real.sqrt a :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hsa1
  have h7 : 8/(5*(m:ℝ)) ≤ 8/85 := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 5*(m:ℝ)) (by norm_num : (0:ℝ) < 85)).2
    nlinarith [hmR]
  have hθsq : θ*θ ≤ 8/85 := by
    have hNθle : θ ≤ (N:ℝ)*θ := by
      have hq := mul_le_mul_of_nonneg_right hN1 hθ0
      linarith [hq]
    have h5 : θ*θ ≤ ((N:ℝ)*θ)*((N:ℝ)*θ) := by
      have h5a : θ*θ ≤ ((N:ℝ)*θ)*θ :=
        mul_le_mul_of_nonneg_right hNθle hθ0
      have h5b : ((N:ℝ)*θ)*θ ≤ ((N:ℝ)*θ)*((N:ℝ)*θ) :=
        mul_le_mul_of_nonneg_left hNθle (mul_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) hθ0)
      exact le_trans h5a h5b
    have h6 : ((N:ℝ)*θ)^2 ≤ 8/(5*(m:ℝ)) := hwin
    have h6' : ((N:ℝ)*θ)*((N:ℝ)*θ) ≤ 8/(5*(m:ℝ)) := by
      have hkey : ((N:ℝ)*θ)*((N:ℝ)*θ) = ((N:ℝ)*θ)^2 := by ring
      rw [hkey]
      exact hwin
    exact le_trans h5 (le_trans h6' h7)
  have hθlt : θ < 1 := by nlinarith [hθsq]
  have hθpi : θ ≤ Real.pi :=
    le_trans (Real.arcsin_le_pi_div_two (Real.sqrt a)) (by linarith [Real.pi_pos])
  have hNθ : (N:ℝ)*θ ≤ 1 := by
    have h8 : (0:ℝ) ≤ (N:ℝ)*θ := mul_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) hθ0
    have h9 : ((N:ℝ)*θ)*((N:ℝ)*θ) ≤ 8/85 := by
      calc ((N:ℝ)*θ)*((N:ℝ)*θ) = ((N:ℝ)*θ)^2 := by ring
        _ ≤ 8/(5*(m:ℝ)) := hwin
        _ ≤ 8/85 := h7
    nlinarith [h8, h9]
  have hcoef : 1-4/(5*(m:ℝ)) ≤ (1-((N:ℝ)*θ)^2/4)^2 := by
    have hA : ((N:ℝ)*θ)^2/4 ≤ 2/(5*(m:ℝ)) := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by positivity : (0:ℝ) < 5*(m:ℝ))).2
      have hA1 : ((N:ℝ)*θ)^2*5*(m:ℝ) ≤ (8/(5*(m:ℝ)))*5*(m:ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hwin (by norm_num : (0:ℝ) ≤ 5)) (by positivity)
      have hA2 : (8/(5*(m:ℝ)))*5*(m:ℝ) = 8 := by field_simp
      linarith
    have h2m : 2/(5*(m:ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 5*(m:ℝ))).2
      linarith [hm1]
    have hB : 1-2/(5*(m:ℝ)) ≤ 1-((N:ℝ)*θ)^2/4 := by linarith [hA, h2m]
    have hC : (1-2/(5*(m:ℝ)))^2 ≤ (1-((N:ℝ)*θ)^2/4)^2 := by
      have hC0 := mul_self_le_mul_self (by linarith [h2m] : (0:ℝ) ≤ 1-2/(5*(m:ℝ))) hB
      calc (1-2/(5*(m:ℝ)))^2
          = (1-2/(5*(m:ℝ)))*(1-2/(5*(m:ℝ))) := by ring
        _ ≤ (1-((N:ℝ)*θ)^2/4)*(1-((N:ℝ)*θ)^2/4) := hC0
        _ = (1-((N:ℝ)*θ)^2/4)^2 := by ring
    have hD : 1-4/(5*(m:ℝ)) ≤ (1-2/(5*(m:ℝ)))^2 := by
      have hE : (1-2/(5*(m:ℝ)))^2 = (1-4/(5*(m:ℝ)))+(2/(5*(m:ℝ)))^2 := by ring
      rw [hE]
      linarith [(sq_nonneg (2/(5*(m:ℝ))))]
    exact le_trans hD hC
  have hgain := sine_small_window_gain_sq θ ((N:ℝ)) hθ0 hθpi
    (by positivity : (0:ℝ) ≤ (N:ℝ)) hNθ
  have hsina : (Real.sin θ)^2 = a := by rw [hsin, Real.sq_sqrt ha0]
  calc (1-4/(5*(m:ℝ)))*((N:ℝ)^2)*a
      = (1-4/(5*(m:ℝ)))*((N:ℝ)^2)*(Real.sin θ)^2 := by rw [hsina]
    _ ≤ (1-((N:ℝ)*θ)^2/4)^2*((N:ℝ)^2)*(Real.sin θ)^2 := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity)
    _ = ((N:ℝ)^2)*(1-((N:ℝ)*θ)^2/4)^2*(Real.sin θ)^2 := by ring
    _ ≤ (Real.sin ((N:ℝ)*θ))^2 := hgain
end
noncomputable section

theorem rdvt_sin_sq_abs_sub_le (x y : ℝ) :
    |(Real.sin x)^2-(Real.sin y)^2| ≤ |x-y| := by
  have hid : (Real.sin x)^2-(Real.sin y)^2 = Real.sin (x+y)*Real.sin (x-y) := by
    rw [Real.sin_add, Real.sin_sub]
    have e1 : (Real.sin x)^2+(Real.cos x)^2 = 1 := Real.sin_sq_add_cos_sq x
    have e2 : (Real.sin y)^2+(Real.cos y)^2 = 1 := Real.sin_sq_add_cos_sq y
    nlinarith [e1, e2, sq_nonneg (Real.sin x), sq_nonneg (Real.cos y)]
  have h1 : |Real.sin (x-y)| ≤ |x-y| := Real.abs_sin_le_abs
  have h2 : |Real.sin (x+y)| ≤ 1 := Real.abs_sin_le_one _
  rw [hid, abs_mul]
  calc (|Real.sin (x+y)|)*(|Real.sin (x-y)|)
      = (|Real.sin (x-y)|)*(|Real.sin (x+y)|) := by ring
    _ ≤ (|x-y|)*(|Real.sin (x+y)|) := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ (|x-y|)*1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |x-y| := by ring
end
noncomputable section

theorem rdvt_sin_sq_ge_of_window {x : ℝ} (h1 : Real.pi/4 ≤ x) (h2 : x ≤ 3*Real.pi/4) :
    1/2 ≤ (Real.sin x)^2 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hm4 : Real.pi/4 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith
  have hs : Real.sqrt 2/2 ≤ Real.sin x := by
    by_cases hx : x ≤ Real.pi/2
    · have mx : x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
        constructor <;> linarith
      by_cases hxe : Real.pi/4 < x
      · have hlt := Real.strictMonoOn_sin hm4 mx hxe
        rw [Real.sin_pi_div_four] at hlt
        exact le_of_lt hlt
      · have hxeq : x = Real.pi/4 := by linarith
        subst hxeq
        exact le_of_eq (Real.sin_pi_div_four).symm
    · have hy : Real.pi/4 ≤ Real.pi-x := by linarith
      have hy2 : Real.pi-x ≤ Real.pi/2 := by linarith
      have my : Real.pi-x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
        constructor <;> linarith
      rw [← Real.sin_pi_sub x]
      by_cases hxe : Real.pi/4 < Real.pi-x
      · have hlt := Real.strictMonoOn_sin hm4 my hxe
        rw [Real.sin_pi_div_four] at hlt
        exact le_of_lt hlt
      · have hxeq : Real.pi-x = Real.pi/4 := by linarith
        rw [hxeq]
        exact le_of_eq (Real.sin_pi_div_four).symm
  have hsq : (Real.sqrt 2/2)*(Real.sqrt 2/2) ≤ (Real.sin x)*(Real.sin x) :=
    mul_self_le_mul_self (by positivity) hs
  have hval : (Real.sqrt 2/2)*(Real.sqrt 2/2) = 1/2 := by
    rw [show (Real.sqrt 2/2)*(Real.sqrt 2/2) = ((Real.sqrt 2)^2)/4 from by
      field_simp
      ring]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hconv : (Real.sin x)^2 = (Real.sin x)*(Real.sin x) := by ring
  rw [hconv]
  linarith
end
noncomputable section

theorem rdvt_sin_sq_lt_of_lt {x : ℝ} (h0 : 0 ≤ x) (h : x < Real.pi/4) :
    (Real.sin x)^2 < 1/2 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hm4 : Real.pi/4 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith
  have mx : x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith
  have hs : Real.sin x < Real.sqrt 2/2 := by
    have hlt := Real.strictMonoOn_sin mx hm4 h
    rw [Real.sin_pi_div_four] at hlt
    exact hlt
  have hx2 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  have hval : (Real.sqrt 2/2)*(Real.sqrt 2/2) = 1/2 := by
    rw [show (Real.sqrt 2/2)*(Real.sqrt 2/2) = ((Real.sqrt 2)^2)/4 from by
      field_simp
      ring]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hkey : (Real.sin x)^2 < (Real.sqrt 2/2)*(Real.sqrt 2/2) := by
    have hq : (0:ℝ) ≤ Real.sqrt 2/2 := by positivity
    have hsq := mul_self_lt_mul_self hx2 hs
    calc (Real.sin x)^2 = (Real.sin x)*(Real.sin x) := by ring
      _ < (Real.sqrt 2/2)*(Real.sqrt 2/2) := hsq
  linarith
end
noncomputable section

theorem rdvt_arcsin_lipschitz {s t u : ℝ} (h0 : 0 ≤ u) (hu1 : u < 1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsu : s ≤ u) (htu : t ≤ u) :
    |Real.arcsin s-Real.arcsin t| ≤ |s-t|/Real.sqrt (1-u^2) := by
  have hu2 : u^2 < 1 := by
    have hp := pow_lt_pow_left₀ hu1 h0 (by norm_num : 2 ≠ 0)
    rwa [one_pow] at hp
  have hC : (0:ℝ) < Real.sqrt (1-u^2) := Real.sqrt_pos.mpr (by nlinarith [hu2])
  have hmem : ∀ z : ℝ, 0 ≤ z → z ≤ u → z ∈ Set.Icc 0 u := fun z hz1 hz2 => ⟨hz1, hz2⟩
  have hdiff : ∀ z ∈ Set.Icc 0 u, DifferentiableAt ℝ Real.arcsin z := by
    intro z hz
    rw [Real.differentiableAt_arcsin]
    exact ⟨by intro hcon; linarith [hz.1], by intro hcon; linarith [hz.2, hu1]⟩
  have hbound : ∀ z ∈ Set.Icc 0 u, ‖deriv Real.arcsin z‖ ≤ 1/Real.sqrt (1-u^2) := by
    intro z hz
    have hz1 : z^2 < 1 := by
      have hp := pow_lt_pow_left₀ (lt_of_le_of_lt hz.2 hu1) hz.1 (by norm_num : 2 ≠ 0)
      rwa [one_pow] at hp
    have hpos : (0:ℝ) < Real.sqrt (1-z^2) := Real.sqrt_pos.mpr (by nlinarith [hz1])
    simp only [Real.deriv_arcsin]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
    exact (one_div_le_one_div hpos hC).2
      (Real.sqrt_le_sqrt (by nlinarith [hz.2, hz.1, h0]))
  have hkey := fun x y hx1 hx2 hy1 hy2 =>
    Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.arcsin) hdiff hbound
      (convex_Icc 0 u) (hmem y hy1 hy2) (hmem x hx1 hx2)
  have e1 := hkey t s ht htu hs hsu
  have e2 := hkey s t hs hsu ht htu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at e1 e2
  have hconv : ∀ x : ℝ, (1/Real.sqrt (1-u^2))*x = x/Real.sqrt (1-u^2) :=
    fun x => one_div_mul_eq_div _ _
  rw [hconv] at e1 e2
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hle : |t-s|/Real.sqrt (1-u^2) ≤ |s-t|/Real.sqrt (1-u^2) := by
      rw [abs_sub_comm t s]
    have habs := le_trans e1 hle
    linarith [habs, neg_le_abs (Real.arcsin s-Real.arcsin t)]
  · exact le_trans (le_abs_self _) e2
end
noncomputable section

theorem rdvt_final_success {g est : ℝ} {k : ℕ} (hk : 1 ≤ k) (hg0 : 0 < g)
    (hgest : |est-g| ≤ g/100) (hest : est < 1/2)
    (hcross : 1/2 ≤ (Real.sin ((2*(k:ℝ)+1)*Real.arcsin (Real.sqrt est)))^2)
    (hmin : ∀ j : ℕ, j < k →
      (Real.sin ((2*(j:ℝ)+1)*Real.arcsin (Real.sqrt est)))^2 < 1/2) :
    2/5 ≤ (Real.sin ((2*(k:ℝ)+1)*Real.arcsin (Real.sqrt g)))^2 := by
  have hD' : (0:ℝ) < Real.sqrt g := Real.sqrt_pos.mpr hg0
  have hest0 : (0:ℝ) ≤ est := by
    have h1 := (abs_le.mp hgest).1
    nlinarith [h1, hg0]
  have hg99 : g*99 ≤ est*100 := by
    have h3 : -(g/100) ≤ est-g := (abs_le.mp hgest).1
    have h4 : (-(g/100))*100 ≤ (est-g)*100 :=
      mul_le_mul_of_nonneg_right h3 (by norm_num)
    have h5 : (-(g/100))*100 = -(g:ℝ) := by field_simp
    rw [h5] at h4
    nlinarith [h4]
  have hest101 : est*100 ≤ g*101 := by
    have h2 : est-g ≤ g/100 := (abs_le.mp hgest).2
    have h5 : (est-g)*100 ≤ (g/100)*100 :=
      mul_le_mul_of_nonneg_right h2 (by norm_num)
    have h6 : (g/100)*100 = g := by field_simp
    rw [h6] at h5
    nlinarith [h5]
  have hg50 : g*99 < (50:ℝ) := by nlinarith [hg99, hest]
  set th : ℝ := Real.arcsin (Real.sqrt est) with hthd
  set θ : ℝ := Real.arcsin (Real.sqrt g) with hθd
  have hsest1 : Real.sqrt est < 1 := by
    have h1sq : ((1:ℝ)^2) = 1 := by norm_num
    have h12 : (1:ℝ)/2 ≤ 1 := by norm_num
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).2
    rw [h1sq]
    linarith [h12]
  have hsinest : (Real.sin th)^2 = est := by
    rw [hthd, Real.sin_arcsin
      (by linarith [Real.sqrt_nonneg est] : (-1:ℝ) ≤ Real.sqrt est) (le_of_lt hsest1)]
    exact Real.sq_sqrt hest0
  have hsg1 : Real.sqrt g < 1 := by
    rw [(Real.sqrt_lt' (by norm_num : (0:ℝ) < 1))]
    have h1sq : ((1:ℝ)^2) = 1 := by norm_num
    rw [h1sq]
    nlinarith [hg50]
  have hth0 : (0:ℝ) ≤ th := (Real.arcsin_nonneg).2 (Real.sqrt_nonneg est)
  have hθ4 : th < Real.pi/4 := by
    by_contra hcon
    push Not at hcon
    have hxle : th ≤ 3*Real.pi/4 :=
      le_trans (Real.arcsin_le_pi_div_two (Real.sqrt est)) (by linarith [Real.pi_pos])
    have hge := rdvt_sin_sq_ge_of_window hcon hxle
    rw [hthd, Real.sin_arcsin
      (by linarith [Real.sqrt_nonneg est] : (-1:ℝ) ≤ Real.sqrt est) (le_of_lt hsest1),
      Real.sq_sqrt hest0] at hge
    linarith
  have hmono : ∀ j : ℕ, j ≤ k → (2*(j:ℝ)+1)*th < 3*Real.pi/4 := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 : (2*((0:ℕ):ℝ)+1)*th = th := by norm_num
      rw [h1]
      linarith [Real.pi_pos]
    | succ j ih =>
      intro hj
      by_cases hc : (2*(j:ℝ)+1)*th < Real.pi/4
      · have hstep : (2*((j+1 : ℕ):ℝ)+1)*th = (2*(j:ℝ)+1)*th+2*th := by
          push_cast
          ring
        rw [hstep]
        have h2 : 2*th ≤ 2*(Real.pi/4) := by
          apply mul_le_mul_of_nonneg_left hθ4.le (by norm_num)
        have h3 : (2*(j:ℝ)+1)*th+2*(Real.pi/4) < Real.pi/4+2*(Real.pi/4) := by linarith
        have h4 : Real.pi/4+2*(Real.pi/4) = 3*Real.pi/4 := by ring
        linarith
      · push Not at hc
        have hge : 1/2 ≤ (Real.sin ((2*(j:ℝ)+1)*th))^2 :=
          rdvt_sin_sq_ge_of_window hc (le_of_lt (ih (by omega)))
        have hmin' := hmin j (by omega)
        rw [hthd] at hmin'
        rw [hthd] at hge
        exact absurd hge (by linarith)
  have hNth1 : (2*(k:ℝ)+1)*th < 3 := by
    have h1 := hmono k (le_refl k)
    have h2 : 3*Real.pi/4 < 3 := by linarith [Real.pi_lt_four]
    linarith
  have hθle : Real.sqrt est ≤ th := by
    by_contra hcon
    push Not at hcon
    have hmem1 : Real.sqrt est ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
      constructor
      · linarith [Real.pi_pos, Real.sqrt_nonneg est]
      · have h3pi : (3:ℝ) < Real.pi := Real.pi_gt_three
        linarith
    have hmem2 : th ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
      constructor
      · linarith [Real.pi_pos, hth0]
      · exact Real.arcsin_le_pi_div_two (Real.sqrt est)
    have hsinlt : Real.sin th < Real.sin (Real.sqrt est) :=
      Real.strictMonoOn_sin hmem2 hmem1 hcon
    rw [hthd, Real.sin_arcsin
      (by linarith [Real.sqrt_nonneg est] : (-1:ℝ) ≤ Real.sqrt est) (le_of_lt hsest1)] at hsinlt
    have hsinle : Real.sin (Real.sqrt est) ≤ Real.sqrt est := by
      have habs := Real.abs_sin_le_abs (x := Real.sqrt est)
      rw [abs_of_nonneg (Real.sqrt_nonneg est)] at habs
      exact (abs_le.mp habs).2
    linarith
  have hg99sqrt : 99*Real.sqrt g ≤ 100*Real.sqrt est := by
    have hsqa : (99*Real.sqrt g)^2 ≤ (100*Real.sqrt est)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hg0.le, Real.sq_sqrt hest0]
      nlinarith [hg99, hg0.le]
    have habs : |99*Real.sqrt g| ≤ |100*Real.sqrt est| := (sq_le_sq).mp hsqa
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ 99*Real.sqrt g),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 100*Real.sqrt est)] at habs
  have hθge : 99*Real.sqrt g ≤ 100*th :=
    le_trans hg99sqrt (mul_le_mul_of_nonneg_left hθle (by norm_num : (0:ℝ) ≤ 100))
  have hN4 : (2*(k:ℝ)+1)*Real.sqrt g < 300 := by
    have h1 : (2*(k:ℝ)+1)*(99*Real.sqrt g) ≤ (2*(k:ℝ)+1)*(100*th) :=
      mul_le_mul_of_nonneg_left hθge (by positivity : (0:ℝ) ≤ 2*(k:ℝ)+1)
    have h2 : (2*(k:ℝ)+1)*(100*th) = 100*((2*(k:ℝ)+1)*th) := by ring
    have h3 : (2*(k:ℝ)+1)*th < 3 := hNth1
    nlinarith [h1, h2, h3]
  have hident : (Real.sqrt g-Real.sqrt est)*(Real.sqrt g+Real.sqrt est) = g-est := by
    calc (Real.sqrt g-Real.sqrt est)*(Real.sqrt g+Real.sqrt est)
        = (Real.sqrt g)*(Real.sqrt g)-(Real.sqrt est)*(Real.sqrt est) := by ring
      _ = g-est := by
          have e1 : (Real.sqrt g)*(Real.sqrt g) = g := by
            rw [← sq]; exact Real.sq_sqrt hg0.le
          have e2 : (Real.sqrt est)*(Real.sqrt est) = est := by
            rw [← sq]; exact Real.sq_sqrt hest0
          rw [e1, e2]
  have habsid : (|Real.sqrt g-Real.sqrt est|)*(Real.sqrt g+Real.sqrt est) = |est-g| := by
    have h1 : |(Real.sqrt g-Real.sqrt est)*(Real.sqrt g+Real.sqrt est)|
        = (|Real.sqrt g-Real.sqrt est|)*|(Real.sqrt g+Real.sqrt est)| := abs_mul _ _
    rw [hident, abs_sub_comm g est] at h1
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt g+Real.sqrt est)] at h1
    exact h1.symm
  have hdsq : (|Real.sqrt g-Real.sqrt est|)*Real.sqrt g ≤ g/100 := by
    have hstep1 : (|Real.sqrt g-Real.sqrt est|)*Real.sqrt g
        ≤ (|Real.sqrt g-Real.sqrt est|)*(Real.sqrt g+Real.sqrt est) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg est))
        (abs_nonneg _)
    rw [habsid] at hstep1
    exact le_trans hstep1 hgest
  have h50 : g ≤ 50/99 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 99)).2
    nlinarith [hg50]
  have hu1 : Real.sqrt ((101/100)*g) < 1 := by
    have h1sq : ((1:ℝ)^2) = 1 := by norm_num
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).2
    rw [h1sq]
    have hnum : ((101:ℝ)/100)*((50:ℝ)/99) < 1 := by norm_num
    calc (101/100)*g ≤ (101/100)*((50:ℝ)/99) :=
        mul_le_mul_of_nonneg_left h50 (by norm_num : (0:ℝ) ≤ 101/100)
      _ < 1 := hnum
  have hu2sq : (Real.sqrt ((101/100)*g))^2 = (101/100)*g :=
    Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 101/100) hg0.le)
  have hden : (100:ℝ)/143 ≤ Real.sqrt (1-(101/100)*g) := by
    have hfrac : ((100:ℝ)/143)^2 ≤ 1-(101/100)*((50:ℝ)/99) := by norm_num
    have hsq : ((100:ℝ)/143)*((100:ℝ)/143) ≤ 1-(101/100)*g := by
      calc ((100:ℝ)/143)*((100:ℝ)/143) = ((100:ℝ)/143)^2 := (sq _).symm
        _ ≤ 1-(101/100)*((50:ℝ)/99) := hfrac
        _ ≤ 1-(101/100)*g := by
            apply sub_le_sub_left
            exact mul_le_mul_of_nonneg_left h50 (by norm_num : (0:ℝ) ≤ 101/100)
    calc (100:ℝ)/143 = Real.sqrt (((100:ℝ)/143)^2) :=
        (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 100/143)).symm
      _ = Real.sqrt (((100:ℝ)/143)*((100:ℝ)/143)) := by rw [sq]
      _ ≤ Real.sqrt (1-(101/100)*g) := Real.sqrt_le_sqrt hsq
  have hden0 : (0:ℝ) < Real.sqrt (1-(101/100)*g) := by
    apply Real.sqrt_pos.mpr
    have hnum : (101:ℝ)/100*((50:ℝ)/99) < 1 := by norm_num
    calc (0:ℝ) < 1-(101/100)*((50:ℝ)/99) := by norm_num
      _ ≤ 1-(101/100)*g := by
          apply sub_le_sub_left
          exact mul_le_mul_of_nonneg_left h50 (by norm_num : (0:ℝ) ≤ 101/100)
  have hlip := rdvt_arcsin_lipschitz
    (Real.sqrt_nonneg ((101/100)*g)) hu1
    (Real.sqrt_nonneg g) (Real.sqrt_nonneg est)
    (Real.sqrt_le_sqrt (by nlinarith [hg0, hest101] : g ≤ (101/100)*g))
    (Real.sqrt_le_sqrt (by nlinarith [hest101, hg0] : est ≤ (101/100)*g))
  rw [hu2sq] at hlip
  have hden143 : 1/Real.sqrt (1-(101/100)*g) ≤ 143/100 := by
    rw [show (143:ℝ)/100 = 1/((100:ℝ)/143) from by field_simp]
    exact (one_div_le_one_div hden0 (by norm_num : (0:ℝ) < 100/143)).2 hden
  have hnum100 : |Real.sqrt g-Real.sqrt est| ≤ Real.sqrt g/100 := by
    have hgq : Real.sqrt g/100 = (g/100)/Real.sqrt g := by
      field_simp
      rw [Real.sq_sqrt hg0.le]
    rw [hgq]
    exact (le_div_iff₀ hD').2 hdsq
  have hstep2 : (|Real.sqrt g-Real.sqrt est|)/Real.sqrt (1-(101/100)*g)
      ≤ (Real.sqrt g/100)*(143/100) := by
    have e1 : (|Real.sqrt g-Real.sqrt est|)/Real.sqrt (1-(101/100)*g)
        ≤ (Real.sqrt g/100)/Real.sqrt (1-(101/100)*g) := by
      apply (div_le_div_iff₀ hden0 hden0).2
      exact mul_le_mul_of_nonneg_right hnum100 hden0.le
    have e2 : (Real.sqrt g/100)/Real.sqrt (1-(101/100)*g)
        = (Real.sqrt g/100)*(1/Real.sqrt (1-(101/100)*g)) := by
      field_simp
    refine le_trans e1 ?_
    rw [e2]
    exact mul_le_mul_of_nonneg_left hden143 (by positivity)
  have hcoef : ((143:ℝ)/10000) ≤ 1/64 := by norm_num
  have hconv7 : (Real.sqrt g/100)*(143/100) ≤ Real.sqrt g/64 := by
    have e4 : ((143:ℝ)/100)*((1:ℝ)/100) ≤ 1/64 := by norm_num
    have hconv : ((143:ℝ)/100)*((1:ℝ)/100)*Real.sqrt g ≤ (1/64)*Real.sqrt g :=
      mul_le_mul_of_nonneg_right e4 (le_of_lt hD')
    have heq : (Real.sqrt g/100)*(143/100)
        = ((143:ℝ)/100)*((1:ℝ)/100)*Real.sqrt g := by
      field_simp
    have hgq : Real.sqrt g/64 = (1/64)*Real.sqrt g := by field_simp
    rw [heq, hgq]
    exact hconv
  have hθθ' : |θ-th| ≤ Real.sqrt g/64 := le_trans (le_trans hlip hstep2) hconv7
  have hNX : (2*(k:ℝ)+1)*Real.sqrt g ≤ 4 := by nlinarith [hN4]
  have hNbound : (2*(k:ℝ)+1)*(Real.sqrt g/64) ≤ 1/16 := by
    have heq : (2*(k:ℝ)+1)*(Real.sqrt g/64)
        = ((2*(k:ℝ)+1)*Real.sqrt g)/64 := by
      field_simp
    rw [heq]
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ) < 64) (by norm_num : (0:ℝ) < 16)).2
    nlinarith [hNX]
  have hNθθ' : |(2*(k:ℝ)+1)*θ-(2*(k:ℝ)+1)*th| ≤ 1/16 := by
    have hstep : |(2*(k:ℝ)+1)*θ-(2*(k:ℝ)+1)*th|
        ≤ (2*(k:ℝ)+1)*(Real.sqrt g/64) := by
      have heq : (2*(k:ℝ)+1)*θ-(2*(k:ℝ)+1)*th = (2*(k:ℝ)+1)*(θ-th) := by ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*(k:ℝ)+1)]
      exact mul_le_mul_of_nonneg_left hθθ' (by positivity : (0:ℝ) ≤ 2*(k:ℝ)+1)
    exact le_trans hstep hNbound
  have hkey := rdvt_sin_sq_abs_sub_le ((2*(k:ℝ)+1)*θ) ((2*(k:ℝ)+1)*th)
  have hfrac1 : (1:ℝ)/2-1/16 = 7/16 := by norm_num
  have hfrac2 : (7:ℝ)/16 = 2/5+3/80 := by norm_num
  have hge : (Real.sin ((2*(k:ℝ)+1)*θ))^2
      ≥ (Real.sin ((2*(k:ℝ)+1)*th))^2-|(2*(k:ℝ)+1)*θ-(2*(k:ℝ)+1)*th| := by
    have habs' := rdvt_sin_sq_abs_sub_le ((2*(k:ℝ)+1)*θ) ((2*(k:ℝ)+1)*th)
    have hopen := (abs_le.mp habs').1
    linarith [hopen]
  have hcr : 1/2 ≤ (Real.sin ((2*(k:ℝ)+1)*th))^2 := hcross
  have h180 : (0:ℝ) ≤ 3/80 := by norm_num
  linarith [hge, hcr, hNθθ', hfrac1, hfrac2, h180]
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
