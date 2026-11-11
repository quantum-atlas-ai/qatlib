/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDepthCorrectedStat
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoCorrectedQuan

/-!
# Degree and gate bounds for polynomial payoff angles

This module relates the polynomial representations of the truncated payoff angle to their scalar
evaluations. Degree bounds for composition yield the corrected Figure 2 circuit-length bound in
`riskPolyRotationFigTwoDepthCorrected`.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `riskFigTwoAnglePoly_degree`: If `fp` has degree at most `s`, the composed payoff-angle
  polynomial has degree at most `s * (2 * u + 1)`.
* `riskPolyRotationFigTwoDepthCorrected`: The payoff-angle polynomial has the stated evaluation
  and degree bound, and its corrected Figure 2 program satisfies the resulting polynomial length
  bound; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation
open Matrix Polynomial
open scoped Classical BigOperators

/-- Evaluating `riskSinTaylorPoly` gives the scalar truncated angle `riskSinTaylor`. -/
theorem riskSinTaylorPoly_eval (u : ℕ) (c y : ℝ) : (riskSinTaylorPoly u c).eval y=riskSinTaylor u c y := by
  simp only [riskSinTaylorPoly,riskSinTaylor,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X]

/-- The truncated angle polynomial has natural degree at most `2 * u + 1`. -/
theorem riskSinTaylorPoly_degree (u : ℕ) (c : ℝ) : (riskSinTaylorPoly u c).natDegree ≤ 2*u+1 := by
  unfold riskSinTaylorPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hju : j ≤ u := by simp only [Finset.mem_range] at hj;omega
  have hb : (Polynomial.X-Polynomial.C (1/2) : Polynomial ℝ).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
        (by simp only [Polynomial.natDegree_X,Polynomial.natDegree_C,Nat.max_zero];exact le_rfl)
  have hp : ((Polynomial.X-Polynomial.C (1/2) : Polynomial ℝ)^(2*j+1)).natDegree ≤ 2*j+1 :=
    (Polynomial.natDegree_pow_le).trans (by nlinarith)
  have hc :
      (Polynomial.C (((2*j).choose j : ℕ)/((2*j+1 : ℝ))*c^(2*j)) : Polynomial ℝ).natDegree=0 :=
      Polynomial.natDegree_C _
  have hh:=Polynomial.natDegree_mul_le (p := (Polynomial.C (((2*j).choose j : ℕ)/((2*j+1 : ℝ))*c^(2*j))))
    (q := (Polynomial.X-Polynomial.C (1/2))^(2*j+1))
  rw [hc,zero_add] at hh
  exact hh.trans (hp.trans (by omega))

/-- Evaluating `riskFigTwoAnglePoly` gives `2 * (c * riskSinTaylor u c (fp.eval y) + π / 4)`. -/
theorem riskFigTwoAnglePoly_eval (u : ℕ) (c : ℝ) (fp : Polynomial ℝ) (y : ℝ) :
    (riskFigTwoAnglePoly u c fp).eval y=2*(c*riskSinTaylor u c (fp.eval y)+Real.pi/4) := by
  simp only [riskFigTwoAnglePoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_comp,riskSinTaylorPoly_eval]
  ring

/-- If `fp` has degree at most `s`, the composed payoff-angle polynomial has degree at most `s *
(2 * u + 1)`. -/
theorem riskFigTwoAnglePoly_degree (u : ℕ) (c : ℝ) (fp : Polynomial ℝ) (s : ℕ) (hf : fp.natDegree ≤ s) :
    (riskFigTwoAnglePoly u c fp).natDegree ≤ s*(2*u+1) := by
  have hc : ((riskSinTaylorPoly u c).comp fp).natDegree ≤ s*(2*u+1) :=
    (Polynomial.natDegree_comp_le).trans (by
      have hm:=Nat.mul_le_mul (riskSinTaylorPoly_degree u c) hf
      simpa only [Nat.mul_comm] using! hm)
  unfold riskFigTwoAnglePoly
  refine (Polynomial.natDegree_add_le _ _).trans
      (max_le ?_ (by simp only [Polynomial.natDegree_C];omega))
  have hm:=Polynomial.natDegree_mul_le (p := Polynomial.C (2*c))
      (q := (riskSinTaylorPoly u c).comp fp)
  simp only [Polynomial.natDegree_C,zero_add] at hm
  exact hm.trans hc

/-- The payoff-angle polynomial has the stated evaluation and degree bound, and its corrected
Figure 2 program satisfies the resulting polynomial length bound; see [WoernerEgger2019]. -/
theorem riskPolyRotationFigTwoDepthCorrected : PolyRotationFigTwoDepthCorrected := by
  intro u n c fp
  refine ⟨fun x=>riskFigTwoAnglePoly_eval u c fp _,fun s hs=>riskFigTwoAnglePoly_degree u c fp s hs,?_⟩
  intro s hs hn
  have hp:=riskFigTwoAnglePoly_degree u c fp s hs
  exact (riskPolyRotationFigTwoCorrected n (s*(2*u+1)) (riskFigTwoAnglePoly u c fp) hp).2.2.2 hn

end Qatlib.Concepts.RiskEstimation.PolyRotation
