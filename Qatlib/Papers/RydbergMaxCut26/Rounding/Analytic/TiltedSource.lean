/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.TiltedProductMoments
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.PairGaussianLaw
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedSource
open Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedClosed
open Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedMoments

theorem inverse_sqrt_rpow (d : ℝ) (hd : 0 ≤ d) : 1/Real.sqrt d=d^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg hd,← Real.sqrt_eq_rpow,one_div]

theorem inverse_threehalf_rpow (d : ℝ) (hd : 0 < d) :
    1/(d*Real.sqrt d)=d^(-(3/2:ℝ)) := by
  have hr : d^(3/2:ℝ)=d*Real.sqrt d := by
    rw [show (3/2:ℝ)=1+(1/2) by norm_num,Real.rpow_add hd,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hd.le,hr,one_div]

theorem inverse_fivehalf_rpow (d : ℝ) (hd : 0 < d) :
    1/(d^2*Real.sqrt d)=d^(-(5/2:ℝ)) := by
  have hr : d^(5/2:ℝ)=d^2*Real.sqrt d := by
    rw [show (5/2:ℝ)=2+(1/2) by norm_num,Real.rpow_add hd,Real.rpow_two,← Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hd.le,hr,one_div]

theorem actual_pair_mass (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ w : ℝ×ℝ,Real.exp (-(a*w.1^2+b*(t*w.1+Real.sqrt (1-t^2)*w.2)^2))
      ∂standard1.prod standard1)=(determinant t a b)^(-(1/2:ℝ)) := by
  calc
    _ = pairTiltZero t (Real.sqrt (1-t^2)) a b := mass_product_iterated t _ a b ha hb
    _ = _ := (pair_mass t a b ht ha hb).trans (inverse_sqrt_rpow _ (determinant_positive t a b ht ha hb).le)

theorem actual_pair_cross (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ w : ℝ×ℝ,w.1*(t*w.1+Real.sqrt (1-t^2)*w.2)*
      Real.exp (-(a*w.1^2+b*(t*w.1+Real.sqrt (1-t^2)*w.2)^2))
      ∂standard1.prod standard1)=t*(determinant t a b)^(-(3/2:ℝ)) := by
  calc
    _ = pairTiltCross t (Real.sqrt (1-t^2)) a b := cross_product_iterated t _ a b ha hb
    _ = t/(determinant t a b*Real.sqrt (determinant t a b)) := pair_cross t a b ht ha hb
    _ = _ := by rw [← inverse_threehalf_rpow _ (determinant_positive t a b ht ha hb)];ring

theorem actual_tilted_closed (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tiltedMoment t a b=3*t/((determinant t a b)^2*Real.sqrt (determinant t a b)) := by
  rw [tiltedMoment_pairs]
  exact dot_closed t a b ht ha hb

theorem actual_tilted_rpow (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tiltedMoment t a b=3*t*(determinant t a b)^(-(5/2:ℝ)) := by
  rw [actual_tilted_closed t a b ht ha hb,
    ← inverse_fivehalf_rpow _ (determinant_positive t a b ht ha hb)]
  ring
end Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedSource
