/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlow
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowClause2
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCounterexamples
import Qatlib.Concepts.MbqcFlow.FlowDecision.FlowExtended
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.FlowExtended
open Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled
open Qatlib
open Qatlib
open Matrix
open scoped ComplexOrder

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowExt

private theorem fig2b_pulse_apply (x y : Reg 3) :
    rbFig2bPulse x y =
      if x = y then
        bitPhase (x 1) * bitPhase (x 2) * bitPhase (x 0 && x 1) * bitPhase (x 0 && x 2)
      else 0 := by
  have h0 : incomingOdd rbFig2bEdges 0 = false := by decide +kernel
  have h1 : incomingOdd rbFig2bEdges 1 = true := by decide +kernel
  have h2 : incomingOdd rbFig2bEdges 2 = true := by decide +kernel
  rw [rbFig2bPulse, sourcePulse_eq_frame_cz, frameMatrix, czMatrix]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    rw [Finset.sum_eq_single x]
    · rw [Fin.prod_univ_three, h0, h1, h2]
      simp [bitPhase, rbFig2bEdges]
    · intro w _ hw
      simp [hw]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · rw [Finset.sum_eq_zero (fun w _ => by
      by_cases hxw : x = w
      · have hwy : w ≠ y := fun h => hxy (hxw.trans h)
        rw [if_pos hxw, if_neg hwy, mul_zero]
      · rw [if_neg hxw, zero_mul])]
    rw [if_neg hxy]

private theorem plane_basis_XY0_entry (z d : Bool) :
    MbqcPlaneBasis MbqcPlane.XY 0 false (boolEquivFin2 z) (boolEquivFin2 d) = (2 : ℂ)⁻¹ := by
  cases z <;> cases d <;>
    simp [MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB, pauliX, pauliY,
      Real.cos_zero, Real.sin_zero, boolEquivFin2]

private theorem fig2b_mg_entry (x y : Reg 3) :
    rbFig2bMeasureGate false x y =
      (2 : ℂ)⁻¹ *
        (∏ k ∈ Finset.univ.erase 0, if x k = y k then (1 : ℂ) else 0) := by
  rw [rbFig2bMeasureGate, mbqcRegWireGate]
  simp only [Matrix.of_apply]
  rw [plane_basis_XY0_entry (x 0) (y 0)]

private theorem fig2b_out_apply (z : Bool) (j : Fin 4) (x : Reg 3) :
    rbFig2bOutFrame z j x =
      (if x 0 = z then (1 : ℂ) else 0) *
        (if x 1 = (bitVecEquiv 2).symm j 0 then 1 else 0) *
        (if x 2 = (bitVecEquiv 2).symm j 1 then 1 else 0) := rfl

private theorem fig2b_frame_apply (x : Reg 3) (i : Fin 2) :
    rbFig2bFrame x i =
      if x 0 = boolEquivFin2.symm i then (Real.sqrt 2 : ℂ)⁻¹ else 0 := rfl

private theorem fig2b_outmg_apply (z : Bool) (j : Fin 4) (v : Reg 3) :
    (rbFig2bOutFrame z * rbFig2bMeasureGate false) j v =
      (2 : ℂ)⁻¹ *
        (if v 1 = (bitVecEquiv 2).symm j 0 then 1 else 0) *
        (if v 2 = (bitVecEquiv 2).symm j 1 then 1 else 0) := by
  rw [Matrix.mul_apply]
  simp only [fig2b_out_apply, fig2b_mg_entry]
  rw [Finset.sum_eq_single ![z, v 1, v 2]]
  · have hprod : (∏ x ∈ Finset.univ.erase 0,
          (if (![z, v 1, v 2] : Reg 3) x = v x then (1 : ℂ) else 0)) = 1 := by
      refine Finset.prod_eq_one fun x hx => ?_
      have hne : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have : x = 1 ∨ x = 2 := by fin_cases x <;> simp_all
      rcases this with rfl | rfl <;> simp
    rw [hprod, mul_one]
    simp
  · intro y _ hy
    by_cases hk0 : y 0 = z
    · by_cases hk1 : y 1 = v 1
      · by_cases hk2 : y 2 = v 2
        · exact absurd (funext fun k => by fin_cases k <;> simp [hk0, hk1, hk2]) hy
        · rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨by fin_cases y <;> omega,
              Finset.mem_univ 2⟩) (by rw [if_neg hk2])]
          ring
      · rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨by fin_cases y <;> omega,
              Finset.mem_univ 1⟩) (by rw [if_neg hk1])]
        ring
    · rw [if_neg hk0]
      ring
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem fig2b_outmgpulse_apply (z : Bool) (j : Fin 4) (w : Reg 3) :
    ((rbFig2bOutFrame z * rbFig2bMeasureGate false) * rbFig2bPulse) j w =
      (2 : ℂ)⁻¹ *
        (if w 1 = (bitVecEquiv 2).symm j 0 then 1 else 0) *
        (if w 2 = (bitVecEquiv 2).symm j 1 then 1 else 0) *
        (bitPhase (w 1) * bitPhase (w 2) * bitPhase (w 0 && w 1) * bitPhase (w 0 && w 2)) := by
  rw [Matrix.mul_apply]
  simp only [fig2b_pulse_apply]
  rw [Finset.sum_eq_single w]
  · rw [if_pos rfl, fig2b_outmg_apply]
  · intro v _ hv
    rw [if_neg hv, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem fig2b_corr_mul {α : Type*} (M : Matrix (Fin 4) α ℂ) :
    rbFig2bCorrection false * M = M := by
  ext j x
  have h1 : (rbFig2bCorrection false) = (1 : Operator 4) := rfl
  rw [h1, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro v _ hv
    have hz : (1 : Operator 4) j v = 0 := by rw [Matrix.one_apply_ne (Ne.symm hv)]
    rw [hz, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem fig2b_kraus_false_entry (z : Bool) (j : Fin 4) (i : Fin 2) :
    rbFig2bKraus false z j i =
      ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ *
        (if i = 0 then
          (if (bitVecEquiv 2).symm j 0 = (bitVecEquiv 2).symm j 1 then 1 else -1)
        else 1) := by
  rw [rbFig2bKraus, fig2b_corr_mul, Matrix.mul_apply]
  simp only [fig2b_frame_apply]
  rw [Finset.sum_eq_single ![boolEquivFin2.symm i, (bitVecEquiv 2).symm j 0,
    (bitVecEquiv 2).symm j 1]]
  · rw [fig2b_outmgpulse_apply]
    have hb0 : (![boolEquivFin2.symm i, (bitVecEquiv 2).symm j 0,
        (bitVecEquiv 2).symm j 1] : Reg 3) 0 = boolEquivFin2.symm i := rfl
    have hb1 : (![boolEquivFin2.symm i, (bitVecEquiv 2).symm j 0,
        (bitVecEquiv 2).symm j 1] : Reg 3) 1 = (bitVecEquiv 2).symm j 0 := rfl
    have hb2 : (![boolEquivFin2.symm i, (bitVecEquiv 2).symm j 0,
        (bitVecEquiv 2).symm j 1] : Reg 3) 2 = (bitVecEquiv 2).symm j 1 := rfl
    rw [hb0, hb1, hb2, if_pos rfl, if_pos rfl, if_pos rfl]
    have hph : (bitPhase ((bitVecEquiv 2).symm j 0) * bitPhase ((bitVecEquiv 2).symm j 1) *
        bitPhase (boolEquivFin2.symm i && (bitVecEquiv 2).symm j 0) *
        bitPhase (boolEquivFin2.symm i && (bitVecEquiv 2).symm j 1)) =
        (if i = 0 then
          (if (bitVecEquiv 2).symm j 0 = (bitVecEquiv 2).symm j 1 then 1 else -1)
        else 1) := by
      fin_cases i <;>
        rcases hc0 : (bitVecEquiv 2).symm j 0 <;> rcases hc1 : (bitVecEquiv 2).symm j 1 <;>
          simp_all [bitPhase, boolEquivFin2]
    rw [hph, mul_inv]
    ring
  · intro w _ hw
    rw [fig2b_outmgpulse_apply]
    by_cases hw0 : w 0 = boolEquivFin2.symm i
    · rw [if_pos hw0]
      by_cases hw1 : w 1 = (bitVecEquiv 2).symm j 0
      · by_cases hw2 : w 2 = (bitVecEquiv 2).symm j 1
        · exact absurd (funext fun k => by fin_cases k <;> simp [hw0, hw1, hw2]) hw
        · rw [if_neg hw2]; ring
      · rw [if_neg hw1]; ring
    · rw [if_neg hw0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem fig2b_kraus_false_eq (z : Bool) :
    rbFig2bKraus false z = rbFig2bTransferOp := by
  ext j i
  rw [fig2b_kraus_false_entry]
  simp only [rbFig2bTransferOp, Matrix.of_apply, smul_eq_mul]

theorem fig2b_branch_false_eq (ρ : Operator 2) :
    rbFig2bBranch false ρ =
      (2 : ℂ) • (rbFig2bTransferOp * ρ * (rbFig2bTransferOp).conjTranspose) := by
  rw [rbFig2bBranch, rbFig2bBranchMap, LinearMap.sum_apply, Fintype.sum_bool,
    fig2b_kraus_false_eq false, fig2b_kraus_false_eq true]
  simp only [conjBranch_apply]
  module

theorem g2 : Clause21Claim :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled.g2

theorem g3 : Clause22Claim := by
  refine ⟨clause3_clause1, clause3_clause2, ?_, clause3_counter_clause3, clause3_clause4,
      clause3_clause5⟩
  intro ρ
  exact fig2b_branch_false_eq ρ

end Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowExt
