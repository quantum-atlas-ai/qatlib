/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Literal scale convention in the printed triangulation estimator

Fixed 1011.3245v1, Lemma 47: the displayed data call C=c², while the
displayed estimator inserts C directly beside squared distances to lambda*w.
The exact-data instance r=c=1, lambda=2, theta=pi/2 has R=1,S=5,T=1,C=1.
That literal estimator returns pi, even at arbitrarily accurate data.
The historical chordal wrapper instead takes its C input as lambda²*c².
This diagnostic distinguishes those two conventions; it does not refute
the scale-corrected stability result.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.PrintedScale

/-- The literal estimator displayed in the fixed source with its C input unscaled. -/
def estimate (R S T C tau : ℝ) : ℝ :=
  tau + (if R+C-T < 0 then -1 else 1) * Real.arccos ((R+C-S)/(2*Real.sqrt (R*C)))

/-- Exact r=c=1,lambda=2,theta=pi/2 data satisfy every displayed approximation bound. -/
theorem exactData :
    |(1 : ℝ)-1^2| < (1/100)*2^2*1 ∧
    |(5 : ℝ)-(1^2+2^2*1^2-2*2*1*1*Real.cos (Real.pi/2))| < (1/100)*2^2*1 ∧
    |(1 : ℝ)-(1^2+2^2*1^2-2*2*1*1*Real.sin (Real.pi/2))| < (1/100)*2^2*1 ∧
    |(1 : ℝ)-1^2| < (1/100)*1 ∧
    (1/100 : ℝ) ≤ (1/10)*min 1 (1/(2^2*1)) := by
  norm_num

/-- The literal unscaled estimator returns pi on the exact admissible data. -/
theorem estimateValue : estimate 1 5 1 1 0 = Real.pi := by
  have ha : Real.arccos (-3/2) = Real.pi := Real.arccos_eq_pi.mpr (by norm_num)
  norm_num [estimate, ha]

/-- The estimator's absolute phase error is pi/2 and is already in the principal range. -/
theorem principalGap :
    |estimate 1 5 1 1 0 - Real.pi/2| = Real.pi/2 ∧
    |estimate 1 5 1 1 0 - Real.pi/2| ≤ Real.pi := by
  rw [estimateValue]
  have hp := Real.pi_pos
  constructor
  · rw [abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- The literal printed bound fails even at exact data and a permitted positive epsilon. -/
theorem printedGap :
    ¬(|estimate 1 5 1 1 0 - Real.pi/2| ≤
      |(0 : ℝ)-0| + 1.37*Real.sqrt (1/100)*(2*Real.sqrt (1/1)+1)) := by
  rw [principalGap.1]
  have hs0 := Real.sqrt_nonneg (1/100 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/100)
  have hs : Real.sqrt (1/100 : ℝ) = 1/10 := by nlinarith
  rw [hs]
  norm_num
  linarith [Real.pi_gt_three]

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.PrintedScale
