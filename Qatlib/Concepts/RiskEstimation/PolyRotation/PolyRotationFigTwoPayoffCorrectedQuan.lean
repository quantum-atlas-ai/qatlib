/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoPayoffCorrectedStat
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDepthCorrectedQuan
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Payoff semantics of corrected polynomial rotations

This module proves `riskPolyRotationFigTwoPayoffCorrected`, identifying the corrected Figure 2
program with payoff-rotation amplitudes on clean-work basis states when the payoff angle lies in
`[0, π / 2]`.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `riskPolyRotationFigTwoPayoffCorrected`: When the polynomial payoff angle lies in `[0, π /
  2]`, the corrected program with the negated doubled angle has the same embedded amplitudes as
  the corresponding squared-sine payoff rotation; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyReadout
open Qatlib.Concepts.BlockEncoding.LinearCombination

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation
open Matrix Polynomial
open scoped Classical BigOperators

/-- When the polynomial payoff angle lies in `[0, π / 2]`, the corrected program with the
negated doubled angle has the same embedded amplitudes as the corresponding squared-sine
payoff rotation; see [WoernerEgger2019]. -/
theorem riskPolyRotationFigTwoPayoffCorrected : PolyRotationFigTwoPayoffCorrected := by
  intro u n c fp x
  (try dsimp only)
  intro hφ0 hφ1
  let φ : ℝ:=c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4
  let g : Reg n →
      ℝ:=fun y=>Real.sin (c*riskSinTaylor u c (fp.eval (figTwoRegEval y : ℝ))+Real.pi/4)^2
  change 0 ≤ φ at hφ0
  change φ ≤ Real.pi/2 at hφ1
  have hp : (-riskFigTwoAnglePoly u c fp).natDegree ≤ fp.natDegree*(2*u+1) := by
    simpa only [Polynomial.natDegree_neg] using!
        riskFigTwoAnglePoly_degree u c fp fp.natDegree le_rfl
  have hs:=(riskPolyRotationFigTwoCorrected n (fp.natDegree*(2*u+1)) (-riskFigTwoAnglePoly u c fp) hp).2.1 x
  have he : -(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval x : ℝ)= -2*φ := by
    rw [riskFigTwoAnglePoly_eval]
    dsimp [φ]
    ring
  simp only [Polynomial.eval_neg] at hs
  rw [he] at hs
  change Run 1 (reflectionCompile (figTwoProgramCorrected (fp.natDegree*(2*u+1))
      (fun y=>-(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))))
      (Ket ((multiKnownSplit n).symm ((x,false),fun _=>false)))=
    ∑ b : Bool,((payoffRotation g)*ᵥKet (x,false)) (x,b) • Ket ((multiKnownSplit n).symm ((x,b),fun _=>false))
  rw [hs]
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (fun z : ℂ=>z • Ket ((multiKnownSplit n).symm ((x,b),fun _=>false)))
  have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hφ1⟩
  have hsq : 1-Real.sin φ^2=Real.cos φ^2 := by nlinarith [Real.sin_sq_add_cos_sq φ]
  have hr1 : Real.sqrt (Real.sin φ^2)=Real.sin φ := Real.sqrt_sq hsin
  have hr0 : Real.sqrt (1-Real.sin φ^2)=Real.cos φ := by rw [hsq];exact Real.sqrt_sq hcos
  have hgx : g x=Real.sin φ^2 := rfl
  have hhalf : (-2*φ)/2= -φ := by ring
  rw [mulVec_ket_apply,mulVec_ket_apply,payoffRotation_apply,hgx]
  cases b <;> simp only [qubitEulerRotation,Matrix.of_apply,hhalf,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,neg_neg,
    if_true,if_false,Bool.false_eq_true,Bool.true_eq_false,hr0,hr1]

end Qatlib.Concepts.RiskEstimation.PolyRotation
