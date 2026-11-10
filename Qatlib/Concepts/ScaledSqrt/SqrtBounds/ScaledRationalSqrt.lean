/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ScaledSqrt.SqrtBounds.ScaledRationalSqrtDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.ScaledSqrt.SqrtBounds
set_option autoImplicit false

theorem g1 :
    ∀ (q S : ℚ) (k : ℕ), 0<S → 0≤q → q≤S*S →
      let b := bracket q S k
      0≤b.1 ∧ b.1≤b.2.1 ∧ b.2.1≤S ∧ b.1^2≤q ∧ q≤b.2.1^2 ∧
      b.2.1-b.1=S/(2:ℚ)^k ∧ b.2.2=k ∧
      (b.1:ℝ)≤Real.sqrt (q:ℝ) ∧ Real.sqrt (q:ℝ)≤(b.2.1:ℝ) := by
  intro q S k hS hq hqS
  have hSS : 0 < S*S := mul_pos hS hS
  have hn0 : 0 ≤ q/(S*S) := div_nonneg hq hSS.le
  have hn1 : q/(S*S) ≤ 1 := (div_le_one hSS).mpr hqS
  obtain ⟨hl,hlu,hu,hlq,hqu,hw,hk,_⟩ :=
    Qatlib.Concepts.MonteCarloMean.PayoffRotation.rational_sqrt_bracket_actual_interval_and_comparisons (q/(S*S)) k hn0 hn1
  let t := Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q/(S*S)) k
  have hlo : 0 ≤ S*t.1 := mul_nonneg hS.le hl
  have hlu' : S*t.1 ≤ S*t.2.1 := mul_le_mul_of_nonneg_left hlu hS.le
  have hhi : S*t.2.1 ≤ S := by simpa using mul_le_mul_of_nonneg_left hu hS.le
  have hsqlo : (S*t.1)^2 ≤ q := by
    have h := mul_le_mul_of_nonneg_right hlq hSS.le
    rw [div_mul_cancel₀ q (ne_of_gt hSS)] at h
    nlinarith only [h]
  have hsqhi : q ≤ (S*t.2.1)^2 := by
    have h := mul_le_mul_of_nonneg_right hqu hSS.le
    rw [div_mul_cancel₀ q (ne_of_gt hSS)] at h
    nlinarith only [h]
  have hwidth : S*t.2.1-S*t.1 = S/(2:ℚ)^k := by
    calc
      _ = S*(t.2.1-t.1) := by ring
      _ = _ := by rw [hw]; ring
  have hloR : (0:ℝ) ≤ ((S*t.1:ℚ):ℝ) := by exact_mod_cast hlo
  have hhiR : (0:ℝ) ≤ ((S*t.2.1:ℚ):ℝ) := by exact_mod_cast hlo.trans hlu'
  have hsqloR : (((S*t.1:ℚ):ℝ))^2 ≤ (q:ℝ) := by exact_mod_cast hsqlo
  have hsqhiR : (q:ℝ) ≤ (((S*t.2.1:ℚ):ℝ))^2 := by exact_mod_cast hsqhi
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ q by exact_mod_cast hq)
  dsimp only [bracket]
  refine ⟨hlo,hlu',hhi,hsqlo,hsqhi,hwidth,hk,?_,?_⟩
  · nlinarith [Real.sqrt_nonneg (q:ℝ)]
  · nlinarith [Real.sqrt_nonneg (q:ℝ)]

private theorem sqrt_gap (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b-a) := by
  have hb : 0 ≤ b := ha.trans hab
  have hd : 0 ≤ b-a := sub_nonneg.mpr hab
  have hsa := Real.sqrt_nonneg a
  have hsb := Real.sqrt_nonneg b
  have hsd := Real.sqrt_nonneg (b-a)
  have hqa := Real.sq_sqrt ha
  have hqb := Real.sq_sqrt hb
  have hqd := Real.sq_sqrt hd
  nlinarith [mul_nonneg hsa hsd]

theorem g2 :
    ∀ (a b S : ℚ) (x : ℝ) (k : ℕ), 0<S → 0≤a → a≤b → b≤S*S →
      (a:ℝ)≤x → x≤(b:ℝ) →
      let c := uncertain a b S k
      (c.1:ℝ)≤Real.sqrt x ∧ Real.sqrt x≤(c.2:ℝ) ∧
      ((c.2-c.1:ℚ):ℝ) ≤ 2*(S:ℝ)/(2:ℝ)^k+Real.sqrt ((b-a:ℚ):ℝ) := by
  intro a b S x k hS ha hab hb hax hxb
  obtain ⟨ha0,haLH,haS,haSq,haSq',haw,han,haLow,haUp⟩ :=
    g1 a S k hS ha (hab.trans hb)
  obtain ⟨hb0,hbLH,hbS,hbSq,hbSq',hbw,hbn,hbLow,hbUp⟩ :=
    g1 b S k hS (ha.trans hab) hb
  have hwidthA : ((bracket a S k).2.1:ℝ) - (bracket a S k).1 = (S:ℝ)/(2:ℝ)^k := by
    exact_mod_cast haw
  have hwidthB : ((bracket b S k).2.1:ℝ) - (bracket b S k).1 = (S:ℝ)/(2:ℝ)^k := by
    exact_mod_cast hbw
  have hgap := sqrt_gap (a:ℝ) (b:ℝ) (by exact_mod_cast ha) (by exact_mod_cast hab)
  dsimp only [uncertain]
  refine ⟨haLow.trans (Real.sqrt_le_sqrt hax), (Real.sqrt_le_sqrt hxb).trans hbUp,?_⟩
  push_cast
  calc
    _ ≤ (S:ℝ)/(2:ℝ)^k + (S:ℝ)/(2:ℝ)^k + Real.sqrt ((b:ℝ)-(a:ℝ)) := by
      linarith only [hwidthA,hwidthB,hbLow,haUp,hgap]
    _ = _ := by ring

end Qatlib.Concepts.ScaledSqrt.SqrtBounds
