/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# Explicit measurement branches and counterexamples

This module computes measurement branches and finite gate decompositions for wire and cluster
constructions in the one-way computation setting of [RaussendorfBriegel2001]. The wire branch
`rbWireBranch` is independent of the corrected measurement outcome and equals one half of the
corresponding unitary conjugation.

The module also exhibits a factor-of-two discrepancy in the stated unscaled three-qubit transfer
formula and proves that `mbqcCounterexampleGraph`, with empty boundary sets and XY measurements
at angle `π / 2`, is not strongly deterministic. Explicit Pauli conjugation and branch
calculations make the outcome dependence precise.

## Main statements

* `clause3_clause1`: the corrected wire branch identity.
* `clause3_clause4`: the finite gate decomposition implements the wire pulse.
* `clause3_counter_clause3`: the unscaled three-qubit branch formula fails.
* `c5_branch_value`: the two-vertex branch value determined by corrected outcome labels.
* `clause6_clause5`: failure of strong determinism for the two-vertex example.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.FlowExtended

/-- For two-bit registers, the product of coordinate equality indicators away from coordinate
one is the equality indicator at coordinate zero. -/
private theorem wire_prod_erase_one (x y : Reg 2) :
    (∏ i ∈ Finset.univ.erase (1 : Fin 2), (if x i = y i then (1 : ℂ) else 0))
      = (if x 0 = y 0 then (1 : ℂ) else 0) := by
  have h : Finset.univ.erase (1 : Fin 2) = ({0} : Finset (Fin 2)) := by decide
  rw [h, Finset.prod_singleton]

/-- For two-bit registers, the product of coordinate equality indicators away from coordinate
zero is the equality indicator at coordinate one. -/
private theorem wire_prod_erase_zero (x y : Reg 2) :
    (∏ i ∈ Finset.univ.erase (0 : Fin 2), (if x i = y i then (1 : ℂ) else 0))
      = (if x 1 = y 1 then (1 : ℂ) else 0) := by
  have h : Finset.univ.erase (0 : Fin 2) = ({1} : Finset (Fin 2)) := by decide
  rw [h, Finset.prod_singleton]

/-- The wire pulse is diagonal, with phase equal to the product of the second-bit phase and the
two-bit controlled phase. -/
private theorem wire_pulse_entry (x y : Reg 2) :
    rbWirePulse x y = if x = y then bitPhase (x 1) * bitPhase (x 0 && x 1) else 0 := by
  have h0 : incomingOdd rbWireEdges 0 = false := by decide +kernel
  have h1 : incomingOdd rbWireEdges 1 = true := by decide +kernel
  rw [rbWirePulse, sourcePulse_eq_frame_cz, frameMatrix, czMatrix,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
    have hfr : (∏ v : Fin 2, if (incomingOdd rbWireEdges v && x v) = true then (-1 : ℂ) else 1)
        = bitPhase (x 1) := by
      rw [Fin.prod_univ_two, h0, h1]
      cases x 0 <;> cases x 1 <;> simp [bitPhase]
    have hcz : (∏ e ∈ rbWireEdges, if (x e.1 && x e.2) = true then (-1 : ℂ) else 1)
        = bitPhase (x 0 && x 1) := by
      rw [rbWireEdges, Finset.prod_singleton]
      cases x 0 <;> cases x 1 <;> simp [bitPhase]
    rw [hfr, hcz]
  · rw [if_neg hxy, if_neg hxy]

/-- The wire input frame has amplitude `1 / √2` when the first register bit matches the logical
input label, and zero otherwise. -/
private theorem wire_frame_apply (x : Reg 2) (j : Fin 2) :
    rbWireFrame x j = if x 0 = boolEquivFin2.symm j then (Real.sqrt 2 : ℂ)⁻¹ else 0 := rfl

/-- The wire output frame selects the measured first bit and the logical second-bit label. -/
private theorem wire_out_apply (z : Bool) (j : Fin 2) (x : Reg 2) :
    rbWireOutFrame z j x =
      if x 0 = z ∧ x 1 = boolEquivFin2.symm j then (1 : ℂ) else 0 := rfl

/-- The wire correction acts on the second qubit while preserving the first register bit. -/
private theorem wire_corr_gate_apply (b : Bool) (x y : Reg 2) :
    rbWireCorrectorGate b x y =
      rbWireCorrector b (boolEquivFin2 (x 1)) (boolEquivFin2 (y 1)) *
        (if x 0 = y 0 then (1 : ℂ) else 0) := by
  rw [rbWireCorrectorGate, mbqcRegWireGate]
  simp only [Matrix.of_apply]
  rw [wire_prod_erase_one]

/-- The wire measurement gate applies the XY-plane measurement matrix to the first qubit and
preserves the second register bit. -/
private theorem wire_mg_apply (a : ℝ) (b : Bool) (x y : Reg 2) :
    rbWireMeasureGate a b x y =
      MbqcPlaneBasis MbqcPlane.XY a b (boolEquivFin2 (x 0)) (boolEquivFin2 (y 0)) *
        (if x 1 = y 1 then (1 : ℂ) else 0) := by
  rw [rbWireMeasureGate, mbqcRegWireGate]
  simp only [Matrix.of_apply]
  rw [wire_prod_erase_zero]

/-- The XY-plane measurement matrix has diagonal entries one half and the stated signed
trigonometric off-diagonal entries. -/
private theorem plane_XY_entry (a : ℝ) (b : Bool) (u v : Fin 2) :
    MbqcPlaneBasis MbqcPlane.XY a b u v =
      if u = v then (2 : ℂ)⁻¹
      else if u = 0 then
        (2 : ℂ)⁻¹ * (if b then (-1 : ℂ) else 1) *
          (Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I)
      else
        (2 : ℂ)⁻¹ * (if b then (-1 : ℂ) else 1) *
          (Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I) := by
  fin_cases u <;> fin_cases v <;> cases b <;>
    simp [MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB, pauliX, pauliY] <;>
    ring

/-- The equivalence identifying a two-bit register with the pair of its coordinate values. -/
private def reg2ProdEquiv : Reg 2 ≃ Bool × Bool where
  toFun y := (y 0, y 1)
  invFun p := ![p.1, p.2]
  left_inv y := funext fun k => by fin_cases k <;> rfl
  right_inv p := by cases p with | mk a b => rfl

/-- A sum over two-bit registers expands into the four possible Boolean assignments. -/
private theorem sum_reg2_eq (F : Reg 2 → ℂ) :
    (∑ y : Reg 2, F y)
      = F ![false, false] + F ![false, true] + F ![true, false] + F ![true, true] := by
  rw [← Equiv.sum_comp reg2ProdEquiv.symm F, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have e00 : reg2ProdEquiv.symm (false, false) = (![false, false] : Reg 2) := rfl
  have e01 : reg2ProdEquiv.symm (false, true) = (![false, true] : Reg 2) := rfl
  have e10 : reg2ProdEquiv.symm (true, false) = (![true, false] : Reg 2) := rfl
  have e11 : reg2ProdEquiv.symm (true, true) = (![true, true] : Reg 2) := rfl
  rw [e00, e01, e10, e11]
  ring

/-- Fixing the first register bit by an equality indicator reduces a two-bit sum to its two
second-bit assignments. -/
private theorem sum_reg2_delta (x0 : Bool) (g : Reg 2 → ℂ) :
    (∑ y : Reg 2, (if x0 = y 0 then (1 : ℂ) else 0) * g y)
      = g ![x0, false] + g ![x0, true] := by
  have h := sum_reg2_eq (fun y : Reg 2 => (if x0 = y 0 then (1 : ℂ) else 0) * g y)

  have a00 : ((![false, false] : Reg 2) 0) = false := rfl
  have a01 : ((![false, true] : Reg 2) 0) = false := rfl
  have a10 : ((![true, false] : Reg 2) 0) = true := rfl
  have a11 : ((![true, true] : Reg 2) 0) = true := rfl
  rw [h, a00, a01, a10, a11]
  by_cases hx : x0 = false
  · subst hx
    simp
  · have hxt : x0 = true := by cases x0 <;> simp_all
    subst hxt
    simp

/-- The pulse applied to the wire input frame has the stated matching-input amplitude and
Boolean phase factors. -/
private theorem wire_pulse_frame (x : Reg 2) (j : Fin 2) :
    (rbWirePulse * rbWireFrame) x j =
      if x 0 = boolEquivFin2.symm j then
        (Real.sqrt 2 : ℂ)⁻¹ * (bitPhase (x 1) * bitPhase (boolEquivFin2.symm j && x 1))
      else 0 := by
  rw [Matrix.mul_apply]
  simp only [wire_pulse_entry, wire_frame_apply]
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl]
    by_cases h : x 0 = boolEquivFin2.symm j
    · rw [if_pos h, if_pos h, h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  · intro y _ hy
    rw [if_neg (fun he => hy he.symm)]
    ring
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- After the wire pulse and measurement, the input-frame amplitude is the measurement entry
times the pulse phase, scaled by `1 / √2`. -/
private theorem wire_stage1 (a : ℝ) (b : Bool) (x : Reg 2) (j : Fin 2) :
    (rbWireMeasureGate a b * (rbWirePulse * rbWireFrame)) x j =
      (Real.sqrt 2 : ℂ)⁻¹ *
        MbqcPlaneBasis MbqcPlane.XY a b (boolEquivFin2 (x 0)) j *
        (bitPhase (x 1) * bitPhase (boolEquivFin2.symm j && x 1)) := by
  rw [Matrix.mul_apply]
  simp only [wire_mg_apply, wire_pulse_frame]
  rw [Finset.sum_eq_single ![boolEquivFin2.symm j, x 1]]
  · have h0 : (![boolEquivFin2.symm j, x 1] : Reg 2) 0 = boolEquivFin2.symm j := rfl
    have h1 : (![boolEquivFin2.symm j, x 1] : Reg 2) 1 = x 1 := rfl
    rw [h0, h1, if_pos rfl]
    have hz : boolEquivFin2 (boolEquivFin2.symm j) = j := by rw [Equiv.apply_symm_apply]
    rw [hz, if_pos rfl]
    ring
  · intro y _ hy
    by_cases hy1 : y 1 = x 1
    · by_cases hy0 : y 0 = boolEquivFin2.symm j
      · exact absurd (funext fun k => by fin_cases k <;> simp [hy0, hy1]) hy
      · have hf : (if y 0 = boolEquivFin2.symm j then
            (Real.sqrt 2 : ℂ)⁻¹ * (bitPhase (y 1) * bitPhase (boolEquivFin2.symm j && y 1))
          else 0) = 0 := if_neg hy0
        rw [hf]
        ring
    · have hd : (if x 1 = y 1 then (1 : ℂ) else 0) = 0 := if_neg (fun he => hy1 he.symm)
      rw [hd]
      ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- After correction, the wire amplitude is the measurement entry times a sum over the
second-bit correction and pulse phases. -/
private theorem wire_stage2 (a : ℝ) (b : Bool) (x : Reg 2) (j : Fin 2) :
    (rbWireCorrectorGate b * (rbWireMeasureGate a b * (rbWirePulse * rbWireFrame))) x j =
      (Real.sqrt 2 : ℂ)⁻¹ *
        MbqcPlaneBasis MbqcPlane.XY a b (boolEquivFin2 (x 0)) j *
        (∑ t : Bool, rbWireCorrector b (boolEquivFin2 (x 1)) (boolEquivFin2 t) * bitPhase t *
          bitPhase (boolEquivFin2.symm j && t)) := by
  rw [Matrix.mul_apply]
  simp only [wire_corr_gate_apply, wire_stage1]
  have hre : (∑ y : Reg 2,
        (rbWireCorrector b (boolEquivFin2 (x 1)) (boolEquivFin2 (y 1)) *
          (if x 0 = y 0 then (1 : ℂ) else 0)) *
          ((Real.sqrt 2 : ℂ)⁻¹ * MbqcPlaneBasis MbqcPlane.XY a b (boolEquivFin2 (y 0)) j *
            (bitPhase (y 1) * bitPhase (boolEquivFin2.symm j && y 1))))
      = (∑ y : Reg 2, (if x 0 = y 0 then (1 : ℂ) else 0) *
          (rbWireCorrector b (boolEquivFin2 (x 1)) (boolEquivFin2 (y 1)) *
            ((Real.sqrt 2 : ℂ)⁻¹ * MbqcPlaneBasis MbqcPlane.XY a b (boolEquivFin2 (y 0)) j *
              (bitPhase (y 1) * bitPhase (boolEquivFin2.symm j && y 1))))) := by
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hre, sum_reg2_delta]
  have a0 : ((![x 0, false] : Reg 2) 1) = false := rfl
  have a1 : ((![x 0, true] : Reg 2) 1) = true := rfl
  simp only [a0, a1]
  rw [Fintype.sum_bool]
  have b0 : ((![x 0, false] : Reg 2) 0) = x 0 := rfl
  have b1 : ((![x 0, true] : Reg 2) 0) = x 0 := rfl
  rw [b0, b1]
  ring

/-- The sum of the wire correction entries against the pulse phases is the stated controlled
phase, with the output bit flipped for outcome true. -/
private theorem wire_corr_sum (b : Bool) (j j' : Fin 2) :
    (∑ t : Bool, rbWireCorrector b j' (boolEquivFin2 t) *
      bitPhase t * bitPhase (boolEquivFin2.symm j && t))
      = if b then bitPhase (boolEquivFin2.symm j && !(boolEquivFin2.symm j'))
      else bitPhase (boolEquivFin2.symm j && boolEquivFin2.symm j') := by
  cases b
  · simp only [rbWireCorrector]
    rw [Fintype.sum_bool]
    fin_cases j' <;> fin_cases j <;>
      simp [bitPhase, boolEquivFin2, pauliZ]
  · simp only [rbWireCorrector]
    rw [Fintype.sum_bool]
    fin_cases j' <;> fin_cases j <;>
      simp [bitPhase, boolEquivFin2, pauliX, pauliZ]

/-- Each wire Kraus entry is the scaled XY-plane measurement entry multiplied by the
outcome-dependent controlled phase. -/
private theorem wire_kraus_entry (a : ℝ) (b z : Bool) (j' j : Fin 2) :
    rbWireKraus a b z j' j =
      (Real.sqrt 2 : ℂ)⁻¹ *
        MbqcPlaneBasis MbqcPlane.XY a b (boolEquivFin2 z) j *
        (if b then bitPhase (boolEquivFin2.symm j && !(boolEquivFin2.symm j'))
          else bitPhase (boolEquivFin2.symm j && boolEquivFin2.symm j')) := by
  rw [rbWireKraus]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_apply]
  simp only [wire_out_apply, wire_stage2]
  rw [Finset.sum_eq_single ![z, boolEquivFin2.symm j']]
  · have h0 : (![z, boolEquivFin2.symm j'] : Reg 2) 0 = z := rfl
    have h1 : (![z, boolEquivFin2.symm j'] : Reg 2) 1 = boolEquivFin2.symm j' := rfl
    rw [h0, h1]
    rw [show (if z = z ∧ boolEquivFin2.symm j' = boolEquivFin2.symm j' then (1 : ℂ) else 0) = 1
        from if_pos ⟨rfl, rfl⟩, one_mul]
    have hz : boolEquivFin2 (boolEquivFin2.symm j') = j' := by rw [Equiv.apply_symm_apply]
    rw [hz, wire_corr_sum]
  · intro y _ hy
    by_cases hy0 : y 0 = z
    · by_cases hy1 : y 1 = boolEquivFin2.symm j'
      · exact absurd (funext fun k => by fin_cases k <;> simp [hy0, hy1]) hy
      · have hd : (if y 0 = z ∧ y 1 = boolEquivFin2.symm j' then (1 : ℂ) else 0) = 0 :=
          if_neg (fun he => hy1 he.2)
        rw [hd]
        ring
    · have hd : (if y 0 = z ∧ y 1 = boolEquivFin2.symm j' then (1 : ℂ) else 0) = 0 :=
        if_neg (fun he => hy0 he.1)
      rw [hd]
      ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The exponential of `a * I` is `cos a + I * sin a` for real `a`. -/
private theorem exp_ofReal_I (a : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I)
      = Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I :=
  (Complex.cos_add_sin_I (a : ℂ)).symm

/-- The exponential of `-(a * I)` is `cos a - I * sin a` for real `a`. -/
private theorem exp_neg_ofReal_I (a : ℝ) :
    Complex.exp (-(a : ℂ) * Complex.I)
      = Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I := by
  have h := Complex.cos_add_sin_I (-(a : ℂ))
  rw [Complex.cos_neg, Complex.sin_neg] at h
  have h3 : Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I
      = Complex.cos (a : ℂ) + -Complex.sin (a : ℂ) * Complex.I := by ring
  rw [h3, ← h]

/-- For real `a`, the product of `exp (a * I)` with its complex conjugate is one. -/
private theorem mul_star_exp_one (a : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * star (Complex.exp ((a : ℂ) * Complex.I)) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- Two scalar factors in a Kraus matrix contribute their squared moduli to its conjugation
branch. -/
private theorem conjBranch_phase {D : ℕ} (c d : ℂ) (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Operator D) :
    conjBranch (c • (d • M)) ρ
      = (c * star c * (d * star d)) • (M * ρ * M.conjTranspose) := by
  rw [conjBranch_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- Complex conjugation fixes the reciprocal of two. -/
private theorem star_inv_two : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  show star (((2 : ℝ) : ℂ)⁻¹) = (((2 : ℝ) : ℂ)⁻¹)
  rw [← starRingEnd_apply]
  have h : (((2 : ℝ) : ℂ)⁻¹) = Complex.ofReal (2 : ℝ)⁻¹ := (Complex.ofReal_inv 2).symm
  rw [h, Complex.conj_ofReal]

/-- The exponential of `I * a` is `cos a + I * sin a` for real `a`. -/
private theorem exp_ofReal_I' (a : ℝ) :
    Complex.exp (Complex.I * (a : ℂ))
      = Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I := by
  have h : Complex.I * (a : ℂ) = (a : ℂ) * Complex.I := by ring
  rw [h]
  exact exp_ofReal_I a

/-- The exponential of `-(I * a)` is `cos a - I * sin a` for real `a`. -/
private theorem exp_neg_ofReal_I' (a : ℝ) :
    Complex.exp (-(Complex.I * (a : ℂ)))
      = Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I := by
  have h : -(Complex.I * (a : ℂ)) = (-(a : ℂ)) * Complex.I := by ring
  rw [h]
  exact exp_neg_ofReal_I a

/-- Each wire Kraus matrix is one half of `rbWireUnitary a`, multiplied by the stated
outcome-dependent phase. -/
private theorem wire_kraus_eq (a : ℝ) (b z : Bool) :
    rbWireKraus a b z
      = (if z then (if b then (-1 : ℂ) else 1) * Complex.exp ((a : ℂ) * Complex.I)
          else (1 : ℂ)) • ((2 : ℂ)⁻¹ • rbWireUnitary a) := by
  ext j' j
  rw [wire_kraus_entry, Matrix.smul_apply, Matrix.smul_apply]
  have hU : rbWireUnitary a j' j = (Real.sqrt 2 : ℂ)⁻¹ *
      (if j = 0 then (1 : ℂ)
        else if j' = 0 then (Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I)
        else -(Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I)) := by
    rw [rbWireUnitary]
    simp only [Matrix.of_apply, Matrix.smul_apply]
    rw [exp_neg_ofReal_I]
    ring
  rw [hU]
  cases z <;> cases b <;> fin_cases j' <;> fin_cases j <;>
    simp [plane_XY_entry, wire_corr_sum, boolEquivFin2, bitPhase, exp_ofReal_I, exp_neg_ofReal_I,
      exp_ofReal_I', exp_neg_ofReal_I'] <;>
    try ring
  all_goals simp only [Complex.I_sq]
  all_goals try ring
  all_goals
    try linear_combination (Complex.cos_sq_add_sin_sq a) * ((Real.sqrt 2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
  all_goals
    try linear_combination -(Complex.cos_sq_add_sin_sq a) * ((Real.sqrt 2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)

/-- Every corrected wire branch is independent of the Boolean measurement outcome and equals one
half of conjugation by `rbWireUnitary a`. -/
theorem clause3_clause1 :
    ∀ (a : ℝ) (ρ : Operator 2) (b b' : Bool),
      rbWireBranch a b ρ = rbWireBranch a b' ρ
        ∧ rbWireBranch a b ρ
            = ((2 : ℂ)⁻¹) • (rbWireUnitary a * ρ * (rbWireUnitary a).conjTranspose) := by
  intro a ρ b b'
  have hphase : ∀ (bb zz : Bool),
      ((if zz then (if bb then (-1 : ℂ) else 1) * Complex.exp ((a : ℂ) * Complex.I)
          else (1 : ℂ))
        * star (if zz then (if bb then (-1 : ℂ) else 1) * Complex.exp ((a : ℂ) * Complex.I)
          else (1 : ℂ))) = 1 := by
    intro bb zz
    cases zz
    · have hz : (if false = true then (if bb = true then (-1 : ℂ) else 1) *
          Complex.exp ((a : ℂ) * Complex.I) else (1 : ℂ)) = 1 := if_neg (by decide)
      rw [hz, star_one, mul_one]
    · have hz : (if true = true then (if bb = true then (-1 : ℂ) else 1) *
          Complex.exp ((a : ℂ) * Complex.I) else (1 : ℂ))
          = (if bb = true then (-1 : ℂ) else 1) * Complex.exp ((a : ℂ) * Complex.I) :=
          if_pos rfl
      rw [hz]
      by_cases hb : bb
      · rw [if_pos hb]
        have h2 : ((-1 : ℂ) * Complex.exp ((a : ℂ) * Complex.I))
            * star ((-1 : ℂ) * Complex.exp ((a : ℂ) * Complex.I))
            = Complex.exp ((a : ℂ) * Complex.I) * star (Complex.exp ((a : ℂ) * Complex.I)) := by
          rw [star_mul, star_neg, star_one]
          ring
        rw [h2]
        exact mul_star_exp_one a
      · rw [if_neg hb, one_mul]
        exact mul_star_exp_one a
  have htwo : ((2 : ℂ)⁻¹) * star ((2 : ℂ)⁻¹) = ((2 : ℂ)⁻¹) ^ 2 := by
    rw [star_inv_two]
    ring
  have hk : ∀ (bb zz : Bool),
      conjBranch (rbWireKraus a bb zz) ρ
        = (((2 : ℂ)⁻¹) ^ 2) • (rbWireUnitary a * ρ * (rbWireUnitary a).conjTranspose) := by
    intro bb zz
    rw [wire_kraus_eq, conjBranch_phase, hphase, one_mul, htwo]
  have hbb : ∀ bb : Bool, rbWireBranch a bb ρ
      = ((2 : ℂ)⁻¹) • (rbWireUnitary a * ρ * (rbWireUnitary a).conjTranspose) := by
    intro bb
    rw [rbWireBranch, rbWireBranchMap, LinearMap.sum_apply, Fintype.sum_bool,
      hk bb true, hk bb false]
    have hhalf : (((2 : ℂ)⁻¹) ^ 2 + ((2 : ℂ)⁻¹) ^ 2 : ℂ) = (2 : ℂ)⁻¹ := by
      field_simp
      ring
    rw [← add_smul, hhalf]
  refine ⟨?_, hbb b⟩
  rw [hbb b, hbb b']

/-- The wire, CNOT, and three-qubit examples have declared communication counts one, two, and
one, and every source pulse factors as its frame matrix times its CZ matrix. -/
theorem clause3_clause5 :
    rbWireCommBits = 1 ∧ rbCnotCommBits = 2 ∧ rbFig2bCommBits = 1
      ∧ ∀ (n : ℕ) (edges : Finset (Fin n × Fin n)),
          Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse edges
            = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix edges
              * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix edges :=
  ⟨rfl, rfl, rfl, fun _n edges => sourcePulse_eq_frame_cz edges⟩

/-- The three-qubit pulse is diagonal with the stated two local phases and two controlled
phases. -/
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

/-- A product of coordinate equality indicators selects one register assignment in a finite sum. -/
private theorem sum_reg_single {n : ℕ} (F : Reg n → ℂ) (b : Reg n) :
    ∑ x : Reg n, (∏ k : Fin n, if x k = b k then (1 : ℂ) else 0) * F x = F b := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    have hkb : ∃ k : Fin n, x k ≠ b k := by
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    rcases hkb with ⟨k, hk⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [if_neg hk])]
    simp
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- The false-outcome XY-plane measurement matrix at angle zero has every entry equal to one
half. -/
private theorem plane_basis_XY0_entry (z d : Bool) :
    MbqcPlaneBasis MbqcPlane.XY 0 false (boolEquivFin2 z) (boolEquivFin2 d) = (2 : ℂ)⁻¹ := by
  cases z <;> cases d <;>
    simp [MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB, pauliX, pauliY,
      Real.cos_zero, Real.sin_zero, boolEquivFin2]

/-- The false-outcome measurement gate in the three-qubit example has amplitude one half and
preserves all coordinates except the measured coordinate zero. -/
private theorem fig2b_mg_entry (x y : Reg 3) :
    rbFig2bMeasureGate false x y =
      (2 : ℂ)⁻¹ *
        (∏ k ∈ Finset.univ.erase 0, if x k = y k then (1 : ℂ) else 0) := by
  rw [rbFig2bMeasureGate, mbqcRegWireGate]
  simp only [Matrix.of_apply]
  rw [plane_basis_XY0_entry (x 0) (y 0)]

/-- The three-qubit output frame selects the first-bit outcome and the two remaining bits
encoded by the logical output label. -/
private theorem fig2b_out_apply (z : Bool) (j : Fin 4) (x : Reg 3) :
    rbFig2bOutFrame z j x =
      (if x 0 = z then (1 : ℂ) else 0) *
        (if x 1 = (bitVecEquiv 2).symm j 0 then 1 else 0) *
        (if x 2 = (bitVecEquiv 2).symm j 1 then 1 else 0) := rfl

/-- The three-qubit input frame has amplitude `1 / √2` when its first bit matches the logical
input label, and zero otherwise. -/
private theorem fig2b_frame_apply (x : Reg 3) (i : Fin 2) :
    rbFig2bFrame x i =
      if x 0 = boolEquivFin2.symm i then (Real.sqrt 2 : ℂ)⁻¹ else 0 := rfl

/-- Composing the false-outcome measurement with the output frame gives one half times the
equality indicators for the two retained bits. -/
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

/-- Composing the output frame, false-outcome measurement, and pulse gives the retained-bit
indicators times the explicit pulse phases, scaled by one half. -/
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

/-- The false-outcome correction in the three-qubit example acts as the identity on any matrix
with four rows. -/
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

/-- For false outcome, each three-qubit Kraus entry has scale `1 / (2 * √2)` and the stated sign
determined by the input label and equality of the output bits. -/
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

/-- For false measurement outcome, both output-labeled Kraus matrices equal `rbFig2bTransferOp`. -/
private theorem fig2b_kraus_false_eq (z : Bool) :
    rbFig2bKraus false z = rbFig2bTransferOp := by
  ext j i
  rw [fig2b_kraus_false_entry]
  simp only [rbFig2bTransferOp, Matrix.of_apply, smul_eq_mul]

/-- The false-outcome branch is twice conjugation by `rbFig2bTransferOp`. -/
private theorem fig2b_branch_false_eq (ρ : Operator 2) :
    rbFig2bBranch false ρ =
      (2 : ℂ) • (rbFig2bTransferOp * ρ * (rbFig2bTransferOp).conjTranspose) := by
  rw [rbFig2bBranch, rbFig2bBranchMap, LinearMap.sum_apply, Fintype.sum_bool,
    fig2b_kraus_false_eq false, fig2b_kraus_false_eq true]
  simp only [conjBranch_apply]
  module

/-- Conjugating the identity by `rbFig2bTransferOp` gives a matrix with nonzero entry at `(0,
0)`. -/
private theorem fig2b_transfer_nonsingular :
    (rbFig2bTransferOp * (1 : Operator 2) * (rbFig2bTransferOp).conjTranspose) 0 0 ≠ 0 := by
  have hc : rbFig2bTransferOp 0 0 = ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
    have h0 : (bitVecEquiv 2).symm 0 0 = (bitVecEquiv 2).symm 0 1 := by decide +kernel
    simp [rbFig2bTransferOp]
    intro hne; exact absurd h0 hne
  have hc1 : rbFig2bTransferOp 0 1 = ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
    simp [rbFig2bTransferOp]
  have hne : ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [mul_ne_zero_iff]
    exact ⟨by norm_num, by exact_mod_cast (by norm_num : (Real.sqrt (2 : ℝ)) ≠ 0)⟩
  have hcc : (((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹) *
      star (((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹) ≠ 0 := by
    rw [mul_comm]
    show (starRingEnd ℂ) (((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹)
      * ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ ≠ 0
    rw [← Complex.normSq_eq_conj_mul_self]
    intro h0
    exact hne (Complex.normSq_eq_zero.mp (Complex.ofReal_injective h0))
  have h1 : ∀ j : Fin 2,
      (rbFig2bTransferOp * (1 : Operator 2)) 0 j = rbFig2bTransferOp 0 j := by
    intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (by
      intro m _ hm
      rw [Matrix.one_apply_ne hm, mul_zero])]
    rw [Matrix.one_apply, if_pos rfl, mul_one]
  intro h0
  rw [Matrix.mul_apply] at h0
  simp only [h1] at h0
  rw [Fin.sum_univ_two] at h0
  simp only [Matrix.conjTranspose_apply, hc, hc1] at h0
  exact hcc (by linear_combination (1 / 2) * h0)

/-- The universal formula equating every three-qubit branch with unscaled conjugation by
`rbFig2bTransferOp` is false. -/
theorem clause3_counter_clause3 :
    ¬ (∀ (ρ : Operator 2) (s : Bool),
        rbFig2bBranch s ρ
          = rbFig2bTransferOp * ρ * (rbFig2bTransferOp).conjTranspose) := by
  intro h
  have h1 := h (1 : Operator 2) false
  rw [fig2b_branch_false_eq] at h1
  have hX : rbFig2bTransferOp * (1 : Operator 2) * (rbFig2bTransferOp).conjTranspose = 0 := by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul] at h1
    simp only [one_smul] at h1
    exact add_left_cancel (h1.trans (add_zero _).symm)
  exact fig2b_transfer_nonsingular (by rw [hX]; rfl)

/-- Four successive T gates multiply to Pauli Z. -/
private theorem tGate_fold : ((tGate * tGate) * tGate) * tGate = PauliZ := by
  rw [tGate, Rz, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, PauliZ]
  congr 1
  funext a
  cases a
  · simp
  · show ((Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I))
        * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I))
        * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) = -1
    have h1 : Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)
        = Complex.exp (((2 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h2 : Complex.exp (((2 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)))
        * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)
        = Complex.exp (((3 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h3 : Complex.exp (((3 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)))
        * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)
        = Complex.exp (((4 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h4 : Complex.exp (((4 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)))
        = Complex.exp (((Real.pi : ℝ) * Complex.I)) := by
      congr 1
      push_cast; ring
    rw [h1, h2, h3, h4, Complex.exp_pi_mul_I]

/-- Pauli Z on the second qubit is diagonal with sign determined by that register bit. -/
private theorem wire_pauliZ_entry (x y : Reg 2) :
    wireGate 2 1 PauliZ x y = if x = y then (if x 1 then (-1 : ℂ) else 1) else 0 := by
  rw [wireGate_apply]
  by_cases h0 : x 0 = y 0
  · have hsupp : ∀ k : Fin 2, k ≠ (1 : Fin 2) → x k = y k := by
      intro k hk
      fin_cases k
      · exact h0
      · exact absurd rfl hk
    rw [if_pos hsupp]
    by_cases h1 : x 1 = y 1
    · have hxy : x = y := by
        funext k
        fin_cases k
        · exact h0
        · exact h1
      subst hxy
      rw [if_pos rfl, PauliZ, Matrix.diagonal_apply, if_pos rfl]
    · have hxy : ¬ x = y := by
        intro he
        exact h1 (congrFun he 1)
      rw [if_neg hxy, PauliZ, Matrix.diagonal_apply, if_neg h1]
  · have hnsupp : ¬ ∀ k : Fin 2, k ≠ (1 : Fin 2) → x k = y k := by
      intro hh
      exact h0 (hh 0 (by decide))
    have hxy : ¬ x = y := by
      intro he
      exact h0 (congrFun he 0)
    rw [if_neg hnsupp, if_neg hxy]

/-- The wire frame matrix is diagonal with sign determined by the second register bit. -/
private theorem frame_rb_entry (x y : Reg 2) :
    frameMatrix rbWireEdges x y = if x = y then (if x 1 then (-1 : ℂ) else 1) else 0 := by
  rw [frameMatrix, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Fin.prod_univ_two]
    have i0 : incomingOdd (rbWireEdges : Finset (Fin 2 × Fin 2)) 0 = false := by decide
    have i1 : incomingOdd (rbWireEdges : Finset (Fin 2 × Fin 2)) 1 = true := by decide
    rw [i0, i1]
    cases x 0 <;> cases x 1 <;> simp
  · rw [if_neg hxy, if_neg hxy]

/-- Pauli Z on the second qubit equals the wire frame matrix. -/
private theorem wire_pauliZ_frame : wireGate 2 1 PauliZ = frameMatrix rbWireEdges := by
  ext x y
  rw [wire_pauliZ_entry, frame_rb_entry]

/-- Four T gates on the second qubit multiply to the wire frame matrix. -/
private theorem t4_frame : ((wireGate 2 1 tGate * wireGate 2 1 tGate)
    * wireGate 2 1 tGate) * wireGate 2 1 tGate = frameMatrix rbWireEdges := by
  rw [wireGate_mul, wireGate_mul, wireGate_mul, tGate_fold, wire_pauliZ_frame]

/-- The Hadamard gate on the second qubit preserves the first bit and has the corresponding
Hadamard matrix entry on the second. -/
private theorem wire_hadamard_sep (x k : Reg 2) :
    wireGate 2 1 Hadamard x k
      = (if x 0 = k 0 then (1 : ℂ) else 0) * Hadamard (x 1) (k 1) := by
  rw [wireGate_apply]
  by_cases h : x 0 = k 0
  · have hsupp : ∀ l : Fin 2, l ≠ (1 : Fin 2) → x l = k l := by
      intro l hl
      fin_cases l
      · exact h
      · exact absurd rfl hl
    rw [if_pos hsupp, if_pos h, one_mul]
  · have hnsupp : ¬ ∀ l : Fin 2, l ≠ (1 : Fin 2) → x l = k l := by
      intro hh
      exact h (hh 0 (by decide))
    rw [if_neg hnsupp, if_neg h]
    ring

/-- The CNOT matrix from coordinate zero to coordinate one is the equality indicator for the
target-bit XOR update. -/
private theorem cnot01_apply (k j : Reg 2) :
    cnotGate 2 0 1 k j
      = if k = Function.update j 1 (j 1 ^^ j 0) then (1 : ℂ) else 0 := by
  rw [cnotGate, permMatrix]
  simp only [Matrix.of_apply]

/-- The CNOT target update preserves the control bit at coordinate zero. -/
private theorem cnot_update01_0 (j : Reg 2) :
    (Function.update j 1 (j 1 ^^ j 0)) 0 = j 0 :=
  Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1) _ _

/-- The CNOT target update sets coordinate one to the XOR of target and control. -/
private theorem cnot_update01_1 (j : Reg 2) :
    (Function.update j 1 (j 1 ^^ j 0)) 1 = (j 1 ^^ j 0) :=
  Function.update_self 1 _ _

/-- Applying the CNOT target-bit update twice restores the original register. -/
private theorem cnot_update01_inv (k : Reg 2) :
    Function.update (Function.update k 1 (k 1 ^^ k 0)) 1
        ((Function.update k 1 (k 1 ^^ k 0)) 1 ^^ (Function.update k 1 (k 1 ^^ k 0)) 0) = k :=
  cnotUpdate_involutive 2 (0 : Fin 2) (1 : Fin 2) (by decide) k

/-- The product of CNOT with a second-qubit Hadamard has the stated first-bit equality indicator
and XOR-indexed Hadamard entry. -/
private theorem cnot_hadamard_sep (k y : Reg 2) :
    (cnotGate 2 0 1 * wireGate 2 1 Hadamard) k y
      = (if k 0 = y 0 then (1 : ℂ) else 0) * Hadamard (k 1 ^^ k 0) (y 1) := by
  rw [Matrix.mul_apply]
  simp only [cnot01_apply]
  rw [Finset.sum_eq_single (Function.update k 1 (k 1 ^^ k 0))]
  · rw [if_pos (cnot_update01_inv k).symm, one_mul, wire_hadamard_sep,
      cnot_update01_0, cnot_update01_1]
  · intro j _ hj
    have hne : ¬ k = Function.update j 1 (j 1 ^^ j 0) := by
      intro he
      have h2 := congrArg (fun z : Reg 2 => Function.update z 1 (z 1 ^^ z 0)) he
      simp only [cnot_update01_inv] at h2
      exact hj h2.symm
    rw [if_neg hne]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The two-term Hadamard sum implementing a controlled-X conjugation equals the
controlled-phase equality indicator. -/
private theorem hcxh_scalar (c x1 y1 : Bool) :
    (Hadamard x1 false) * (Hadamard (false ^^ c) y1)
      + (Hadamard x1 true) * (Hadamard (true ^^ c) y1)
      = if x1 = y1 then (if c && x1 then (-1 : ℂ) else 1) else 0 := by
  cases c <;> cases x1 <;> cases y1 <;>
    simp [Hadamard, Bool.xor, Qatlib.Concepts.QuditTeleport.TeleportCore.sqrt2_inv_sq] <;> norm_num

/-- Conjugating CNOT by a Hadamard on the target gives the diagonal two-bit controlled phase. -/
private theorem hcxh_entry (x y : Reg 2) :
    (wireGate 2 1 Hadamard * (cnotGate 2 0 1 * wireGate 2 1 Hadamard)) x y
      = if x = y then (if x 0 && x 1 then (-1 : ℂ) else 1) else 0 := by
  rw [Matrix.mul_apply]
  simp only [wire_hadamard_sep, cnot_hadamard_sep]
  have hre : ∀ k : Reg 2,
      ((if x 0 = k 0 then (1 : ℂ) else 0) * Hadamard (x 1) (k 1))
        * ((if k 0 = y 0 then (1 : ℂ) else 0) * Hadamard (k 1 ^^ k 0) (y 1))
        = (if x 0 = k 0 then (1 : ℂ) else 0) * (if k 0 = y 0 then (1 : ℂ) else 0)
            * (Hadamard (x 1) (k 1) * Hadamard (k 1 ^^ k 0) (y 1)) := by
    intro k
    ring
  simp only [hre]
  by_cases hxy : x 0 = y 0
  · have hit : ∀ k : Reg 2,
        (if x 0 = k 0 then (1 : ℂ) else 0) * (if k 0 = y 0 then (1 : ℂ) else 0)
          = (if x 0 = k 0 then (1 : ℂ) else 0) := by
      intro k
      by_cases h : x 0 = k 0
      · have h2 : k 0 = y 0 := h.symm.trans hxy
        rw [if_pos h, if_pos h2, one_mul]
      · by_cases h2 : k 0 = y 0
        · exact absurd (hxy.trans h2.symm) h
        · rw [if_neg h, if_neg h2]
          ring
    simp only [hit]
    rw [sum_reg2_delta]
    have a0 : ((![x 0, false] : Reg 2) 1) = false := rfl
    have a1 : ((![x 0, true] : Reg 2) 1) = true := rfl
    have b0 : ((![x 0, false] : Reg 2) 0) = x 0 := rfl
    have b1 : ((![x 0, true] : Reg 2) 0) = x 0 := rfl
    simp only [a0, a1, b0, b1]
    rw [hcxh_scalar]
    by_cases h1 : x 1 = y 1
    · have hxy' : x = y := by
        funext k
        fin_cases k
        · exact hxy
        · exact h1
      rw [if_pos h1, if_pos hxy']
    · have hn : ¬ x = y := by
        intro he
        exact h1 (congrFun he 1)
      rw [if_neg h1, if_neg hn]
  · have hz : ∀ k : Reg 2,
        (if x 0 = k 0 then (1 : ℂ) else 0) * (if k 0 = y 0 then (1 : ℂ) else 0) = 0 := by
      intro k
      by_cases h : x 0 = k 0
      · have h2 : ¬ k 0 = y 0 := fun he => hxy (h.trans he)
        rw [if_pos h, if_neg h2]
        ring
      · rw [if_neg h]
        ring
    simp only [hz, zero_mul]
    rw [Finset.sum_const_zero]
    rw [if_neg (fun he : x = y => hxy (congrFun he 0))]

/-- Conjugating CNOT by a Hadamard on the target gives `networkCzGateB 0 1`. -/
private theorem hcxh : wireGate 2 1 Hadamard * (cnotGate 2 0 1 * wireGate 2 1 Hadamard)
    = networkCzGateB 0 1 := by
  ext x y
  rw [hcxh_entry, networkCzGateB, Matrix.diagonal_apply]

/-- The CZ matrix of the wire edge set is `networkCzGateB 0 1`. -/
private theorem cz_rb : czMatrix rbWireEdges = networkCzGateB 0 1 := by
  rw [czMatrix, networkCzGateB, rbWireEdges]
  congr 1
  funext x
  rw [Finset.prod_eq_single (0, 1)]
  · intro b _ hb
    exact absurd (Finset.mem_singleton.1 ‹_›) hb
  · intro h
    exact absurd (Finset.mem_singleton_self (0, 1)) h

/-- Conjugating CNOT by a Hadamard on the target gives the CZ matrix of the wire edge set. -/
private theorem hcxh_cz : wireGate 2 1 Hadamard * (cnotGate 2 0 1 * wireGate 2 1 Hadamard)
    = czMatrix rbWireEdges := by
  rw [hcxh, cz_rb]

/-- The finite code for a Hadamard on wire one denotes the corresponding embedded Hadamard gate. -/
private theorem code_h : finiteCodeMatrix 2 (.h 1) = wireGate 2 1 Hadamard := by
  rw [finiteCodeMatrix, dif_pos (by decide : (1 : ℕ) < 2)]
  rfl

/-- The finite code for CNOT from wire zero to wire one denotes the corresponding CNOT matrix. -/
private theorem code_cx : finiteCodeMatrix 2 (.cx 0 1) = cnotGate 2 0 1 := by
  rw [finiteCodeMatrix, dif_pos (by decide : (0 : ℕ) < 2 ∧ 1 < 2 ∧ 0 ≠ 1)]
  rfl

/-- The finite code for a T gate on wire one denotes the corresponding embedded T gate. -/
private theorem code_t : finiteCodeMatrix 2 (.t 1) = wireGate 2 1 tGate := by
  rw [finiteCodeMatrix, dif_pos (by decide : (1 : ℕ) < 2)]
  rfl

/-- The matrix denoted by the finite gate decomposition `rbFiniteGateDecomp` equals the wire
pulse. -/
private theorem codeWord_rb : finiteCodeWordMatrix 2 rbFiniteGateDecomp = rbWirePulse := by
  show finiteCodeWordMatrix 2 [.h 1, .cx 0 1, .h 1, .t 1, .t 1, .t 1, .t 1] = rbWirePulse
  rw [finite_phase_word_cons, finite_phase_word_cons, finite_phase_word_cons,
    finite_phase_word_cons, finite_phase_word_cons, finite_phase_word_cons,
    finite_phase_word_cons]
  have h0 : finiteCodeWordMatrix 2 [] = (1 : Matrix (Reg 2) (Reg 2) ℂ) := by
    simp [finiteCodeWordMatrix]
  rw [h0, code_t, code_h, code_cx, one_mul]
  rw [t4_frame]
  simp only [Matrix.mul_assoc]
  rw [hcxh_cz]
  show frameMatrix rbWireEdges * czMatrix rbWireEdges = sourcePulse rbWireEdges
  rw [sourcePulse_eq_frame_cz]

/-- Running the finite gate decomposition succeeds on every two-qubit state and applies the wire
pulse. -/
theorem clause3_clause4 :
    ∀ ψ : QState (Reg 2),
      finiteWordRun 2 rbFiniteGateDecomp ψ = some (ApplyGate rbWirePulse ψ) := by
  intro ψ
  have hlegal : finiteWordLegal 2 rbFiniteGateDecomp = true := rbFiniteGateDecomp_legal
  simp only [finiteWordRun, hlegal, if_true]
  rw [finite_phase_word_run, codeWord_rb]

/-- The conjunction of the listed wire, CNOT, three-qubit branch, finite decomposition, and
communication assertions is false because its three-qubit branch formula fails. -/
theorem clause3_counter :
    ¬ ((∀ (a : ℝ) (ρ : Operator 2) (b b' : Bool),
          rbWireBranch a b ρ = rbWireBranch a b' ρ
            ∧ rbWireBranch a b ρ
                = ((2 : ℂ)⁻¹) • (rbWireUnitary a * ρ * (rbWireUnitary a).conjTranspose))
      ∧ (∃ κ : (Bool × Bool) → Fin 2 → Operator 2,
          (∀ s : Bool × Bool, ∀ v : Fin 2, MbqcPauliWire (κ s v)) ∧
          ∀ (ρ : Operator 4) (s : Bool × Bool),
            rbCnotBranch s ρ
              = ((2 : ℂ)⁻¹) ^ 2 •
                  ((relabelGate (bitVecEquiv 2) (pauliProductDensity (κ s)) * rbCnotOp) * ρ
                    * (relabelGate (bitVecEquiv 2) (pauliProductDensity (κ s)) * rbCnotOp).conjTranspose))
      ∧ (∀ (ρ : Operator 2) (s : Bool),
          rbFig2bBranch s ρ
            = rbFig2bTransferOp * ρ * (rbFig2bTransferOp).conjTranspose)
      ∧ (∀ ψ : QState (Reg 2),
          finiteWordRun 2 rbFiniteGateDecomp ψ = some (ApplyGate rbWirePulse ψ))
      ∧ (rbWireCommBits = 1 ∧ rbCnotCommBits = 2 ∧ rbFig2bCommBits = 1
          ∧ ∀ (n : ℕ) (edges : Finset (Fin n × Fin n)),
              Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse edges
                = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix edges
                  * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix edges)) :=
  fun h => clause3_counter_clause3 h.2.2.1
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The Boolean-outcome XY-plane measurement matrix at angle `π / 2`. -/
private noncomputable def c5P (b : Bool) : Operator 2 :=
  MbqcPlaneBasis MbqcPlane.XY (Real.pi / 2) b

/-- The two-qubit state with amplitude `1 / 2` at every register value except `true, true`,
where it is `-1 / 2`. -/
private noncomputable def c5ψ : Reg 2 → ℂ :=
  fun y => if y 0 && y 1 then -(1 / 2 : ℂ) else 1 / 2

/-- The Boolean flag that is true exactly when the supplied matrix equals Pauli X or Pauli Z. -/
private noncomputable def c5flip (W : Operator 2) : Bool :=
  if W = pauliX then true else if W = pauliZ then true else false

/-- The measurement matrix `c5P b` is one half of the identity plus the outcome-signed Pauli Y. -/
theorem c5P_eq (b : Bool) :
    c5P b = (2 : ℂ)⁻¹ • ((1 : Operator 2) + (if b then (-1 : ℂ) else 1) • pauliY) := by
  unfold c5P MbqcPlaneBasis
  simp [mbqcPlaneAxisA, mbqcPlaneAxisB, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The expectation of the product of two single-qubit operators in the state `c5ψ`, expressed
as a double coordinate sum. -/
private noncomputable def c5E (A B : Operator 2) : ℂ :=
  ∑ u : Reg 2, ∑ v : Reg 2,
    star (c5ψ u) *
      A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
      B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) *
      c5ψ v

/-- The expectation of the two identity operators in `c5ψ` is one. -/
theorem c5E_one_one : c5E 1 1 = 1 := by
  unfold c5E
  simp only [sum_reg2_eq]
  simp [c5ψ, boolEquivFin2, Matrix.one_apply]
  norm_num

/-- The expectation of Pauli Y on the first qubit and identity on the second in `c5ψ` is zero. -/
theorem c5E_Y_one : c5E pauliY 1 = 0 := by
  unfold c5E
  simp only [sum_reg2_eq]
  simp [c5ψ, boolEquivFin2, pauliY, Matrix.one_apply]

/-- The expectation of identity on the first qubit and Pauli Y on the second in `c5ψ` is zero. -/
theorem c5E_one_Y : c5E 1 pauliY = 0 := by
  unfold c5E
  simp only [sum_reg2_eq]
  simp [c5ψ, boolEquivFin2, pauliY, Matrix.one_apply]

/-- The expectation of Pauli Y on both qubits in `c5ψ` is one. -/
theorem c5E_Y_Y : c5E pauliY pauliY = 1 := by
  unfold c5E
  simp only [sum_reg2_eq]
  simp [c5ψ, boolEquivFin2, pauliY]
  ring_nf
  norm_num [Complex.I_sq]

/-- The summand defining `c5E` distributes over addition in its first operator. -/
private theorem c5E_term_add_left (A₁ A₂ B : Operator 2) (u v : Reg 2) :
    star (c5ψ u) * (A₁ + A₂) (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
        B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v
      = star (c5ψ u) * A₁ (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
          B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v
        + star (c5ψ u) * A₂ (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
          B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v := by
  simp only [Matrix.add_apply]
  ring

/-- The expectation `c5E` is additive in its first operator. -/
theorem c5E_add_left (A₁ A₂ B : Operator 2) :
    c5E (A₁ + A₂) B = c5E A₁ B + c5E A₂ B := by
  unfold c5E
  simp only [c5E_term_add_left]
  simp only [Finset.sum_add_distrib]

/-- The summand defining `c5E` distributes over addition in its second operator. -/
private theorem c5E_term_add_right (A B₁ B₂ : Operator 2) (u v : Reg 2) :
    star (c5ψ u) * A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
        (B₁ + B₂) (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v
      = star (c5ψ u) * A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
          B₁ (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v
        + star (c5ψ u) * A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
          B₂ (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v := by
  simp only [Matrix.add_apply]
  ring

/-- The expectation `c5E` is additive in its second operator. -/
theorem c5E_add_right (A B₁ B₂ : Operator 2) :
    c5E A (B₁ + B₂) = c5E A B₁ + c5E A B₂ := by
  unfold c5E
  simp only [c5E_term_add_right]
  simp only [Finset.sum_add_distrib]

/-- A complex scalar multiplying the first operator factors out of `c5E`. -/
theorem c5E_smul_left (c : ℂ) (A B : Operator 2) :
    c5E (c • A) B = c * c5E A B := by
  unfold c5E
  have h : ∀ u v : Reg 2,
      star (c5ψ u) * (c • A) (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
          B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v
        = c * (star (c5ψ u) * A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
            B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v) := by
    intro u v
    simp only [Matrix.smul_apply]
    ring
  simp only [h, Finset.mul_sum]

/-- A complex scalar multiplying the second operator factors out of `c5E`. -/
theorem c5E_smul_right (c : ℂ) (A B : Operator 2) :
    c5E A (c • B) = c * c5E A B := by
  unfold c5E
  have h : ∀ u v : Reg 2,
      star (c5ψ u) * A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
          (c • B) (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v
        = c * (star (c5ψ u) * A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0)) *
            B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) * c5ψ v) := by
    intro u v
    simp only [Matrix.smul_apply]
    ring
  simp only [h, Finset.mul_sum]

/-- The joint `c5P` expectation is one half for equal Boolean outcomes and zero for unequal
outcomes. -/
theorem c5base (x y : Bool) :
    c5E (c5P x) (c5P y) = if x = y then (1 / 2 : ℂ) else 0 := by
  rw [c5P_eq, c5P_eq, c5E_smul_left, c5E_smul_right]
  cases x <;> cases y <;>
    simp only [if_true, c5E_add_left, c5E_add_right, c5E_smul_left, c5E_smul_right,
      c5E_one_one, c5E_Y_one, c5E_one_Y, c5E_Y_Y]
  all_goals norm_num

/-- The entries of `c5P b` have diagonal value one half and the stated outcome-dependent
imaginary off-diagonal values. -/
theorem c5P_apply (b : Bool) (i j : Fin 2) :
    c5P b i j =
      if i = j then (2 : ℂ)⁻¹
      else if i = 0 then -(if b then (-1 : ℂ) else 1) * (2 : ℂ)⁻¹ * Complex.I
      else (if b then (-1 : ℂ) else 1) * (2 : ℂ)⁻¹ * Complex.I := by
  fin_cases i <;> fin_cases j <;> cases b <;>
    simp [c5P, MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB, pauliX, pauliY,
      Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The identity matrix differs from Pauli X. -/
private theorem ne_one_pauliX : (1 : Operator 2) ≠ pauliX := by
  intro h
  have e := congrArg (fun M : Operator 2 => M 0 0) h
  simp [pauliX] at e

/-- The identity matrix differs from Pauli Z. -/
private theorem ne_one_pauliZ : (1 : Operator 2) ≠ pauliZ := by
  intro h
  have e := congrArg (fun M : Operator 2 => M 1 1) h
  simp [pauliZ] at e
  norm_num at e

/-- Pauli X differs from Pauli Z. -/
private theorem ne_pauliX_pauliZ : pauliX ≠ pauliZ := by
  intro h
  have e := congrArg (fun M : Operator 2 => M 0 0) h
  simp [pauliX, pauliZ] at e

/-- Pauli X differs from the product of Pauli X and Pauli Z. -/
private theorem ne_pauliX_pauliXZ : pauliX ≠ pauliX * pauliZ := by
  intro h
  have e := congrArg (fun M : Operator 2 => M 0 1) h
  simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at e
  norm_num at e

/-- Pauli Z differs from the product of Pauli X and Pauli Z. -/
private theorem ne_pauliZ_pauliXZ : pauliZ ≠ pauliX * pauliZ := by
  intro h
  have e := congrArg (fun M : Operator 2 => M 0 0) h
  simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at e

/-- The outcome-flip flag of the identity is false. -/
private theorem c5flip_one : c5flip (1 : Operator 2) = false := by
  simp [c5flip, ne_one_pauliX, ne_one_pauliZ]

/-- The outcome-flip flag of Pauli X is true. -/
private theorem c5flip_X : c5flip pauliX = true := by
  simp [c5flip]

/-- The outcome-flip flag of Pauli Z is true. -/
private theorem c5flip_Z : c5flip pauliZ = true := by
  simp [c5flip]

/-- The outcome-flip flag of the product of Pauli X and Pauli Z is false. -/
private theorem c5flip_XZ : c5flip (pauliX * pauliZ) = false := by
  have h1 : pauliX * pauliZ ≠ pauliX := fun h => ne_pauliX_pauliXZ h.symm
  have h2 : pauliX * pauliZ ≠ pauliZ := fun h => ne_pauliZ_pauliXZ h.symm
  simp [c5flip, h1, h2]

/-- Conjugating `c5P b` by Pauli X flips its Boolean outcome label. -/
private theorem c5_conj_X (b : Bool) :
    pauliX * c5P b * pauliX = c5P (b.xor true) := by
  ext i j; fin_cases i <;> fin_cases j <;> cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [c5P_apply, pauliX, Bool.xor]

/-- Conjugating `c5P b` by Pauli Z flips its Boolean outcome label. -/
private theorem c5_conj_Z (b : Bool) :
    pauliZ * c5P b * pauliZ = c5P (b.xor true) := by
  ext i j; fin_cases i <;> fin_cases j <;> cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [c5P_apply, pauliZ, Bool.xor]

/-- Conjugation by a permitted Pauli wire matrix changes the `c5P` outcome by XOR with its
`c5flip` flag. -/
theorem c5_conj (W : Operator 2) (hW : MbqcPauliWire W) (b : Bool) :
    W.conjTranspose * c5P b * W = c5P (b.xor (c5flip W)) := by
  rcases hW with rfl | rfl | rfl | rfl
  · rw [c5flip_one, Bool.xor_false]
    have h1 : ((1 : Operator 2)).conjTranspose = 1 := by simp
    rw [h1, Matrix.one_mul, Matrix.mul_one]
  · rw [c5flip_X]
    have hx : (pauliX : Operator 2).conjTranspose = pauliX := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
    rw [hx]
    exact c5_conj_X b
  · rw [c5flip_Z]
    have hz : (pauliZ : Operator 2).conjTranspose = pauliZ := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]
    rw [hz]
    exact c5_conj_Z b
  · rw [c5flip_XZ, Bool.xor_false]
    have hconj : ((pauliX * pauliZ : Operator 2)).conjTranspose = pauliZ * pauliX := by
      rw [Matrix.conjTranspose_mul]
      have hx : (pauliX : Operator 2).conjTranspose = pauliX := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
      have hz : (pauliZ : Operator 2).conjTranspose = pauliZ := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]
      rw [hx, hz]
    rw [hconj]
    have reassoc : (pauliZ * pauliX) * c5P b * (pauliX * pauliZ)
        = pauliZ * (pauliX * c5P b * pauliX) * pauliZ := by
      simp only [mul_assoc]
    rw [reassoc, c5_conj_X, c5_conj_Z]
    simp [Bool.xor]

/-- The product of two complex reciprocals of `√2` is one half. -/
theorem c5_sqrt2_inv_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The square of `√2`, embedded into `ℂ`, is two. -/
theorem c5_sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The input frame for the empty two-vertex input set has every entry equal to one half. -/
theorem c5_inFrame (x : Fin 4) (y : Fin 1) :
    (mbqcInputFrame (∅ : Finset (Fin 2))) x y = (1 / 2 : ℂ) := by
  simp only [mbqcInputFrame]
  simp
  exact c5_sqrt2_sq

/-- The output frame for the empty two-vertex output set selects the register label specified by
`z`. -/
theorem c5_outFrame (z : Reg 2) (y : Fin 1) (x : Fin 4) :
    (mbqcOutputFrame (∅ : Finset (Fin 2)) z) y x
      = if x = bitVecEquiv 2 z then (1 : ℂ) else 0 := by
  simp only [mbqcOutputFrame]
  simp
  show (if (bitVecEquiv 2).symm x 1 = z 1 then
      (if (bitVecEquiv 2).symm x 0 = z 0 then (1 : ℂ) else 0) else 0)
    = if x = bitVecEquiv 2 z then (1 : ℂ) else 0
  by_cases he : x = bitVecEquiv 2 z
  · rw [if_pos he]
    have hs : (bitVecEquiv 2).symm x = z := (Equiv.symm_apply_eq (bitVecEquiv 2)).mpr he
    have h0 : (bitVecEquiv 2).symm x 0 = z 0 := by rw [hs]
    have h1 : (bitVecEquiv 2).symm x 1 = z 1 := by rw [hs]
    rw [if_pos h1, if_pos h0]
  · rw [if_neg he]
    have hs : ¬((bitVecEquiv 2).symm x = z) :=
        fun h => he ((Equiv.symm_apply_eq (bitVecEquiv 2)).mp h)
    by_cases h1 : (bitVecEquiv 2).symm x 1 = z 1
    · rw [if_pos h1]
      by_cases h0 : (bitVecEquiv 2).symm x 0 = z 0
      · rw [if_pos h0]
        exact absurd (funext fun k => by fin_cases k; exact h0; exact h1) hs
      · rw [if_neg h0]
    · rw [if_neg h1]

/-- The single-edge two-qubit CZ matrix is diagonal, with negative sign exactly when both bits
are true. -/
theorem c5_czDiag (y w : Reg 2) :
    czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2)) y w
      = if y = w then (if y 0 && y 1 then (-1 : ℂ) else 1) else 0 := by
  rw [czMatrix, Matrix.diagonal_apply]
  by_cases he : y = w
  · rw [if_pos he]
    subst w
    rw [Finset.prod_singleton]
    simp
  · rw [if_neg he]
    simp [he]

/-- The two-bit controlled phase is twice the corresponding amplitude of `c5ψ`. -/
theorem c5_phase_eq (y : Reg 2) :
    (if y 0 && y 1 then (-1 : ℂ) else 1) = 2 * c5ψ y := by
  by_cases h0 : y 0 <;> by_cases h1 : y 1 <;> simp [c5ψ, h0, h1]

/-- For two-bit registers, the coordinate equality product excluding zero is the equality
indicator at coordinate one. -/
private theorem prod_erase_zero (x y : Reg 2) :
    (∏ i ∈ Finset.univ.erase (0 : Fin 2), (if x i = y i then (1 : ℂ) else 0))
      = (if x 1 = y 1 then (1 : ℂ) else 0) := by
  have h : Finset.univ.erase (0 : Fin 2) = ({1} : Finset (Fin 2)) := by decide
  rw [h, Finset.prod_singleton]

/-- For two-bit registers, the coordinate equality product excluding one is the equality
indicator at coordinate zero. -/
private theorem prod_erase_one (x y : Reg 2) :
    (∏ i ∈ Finset.univ.erase (1 : Fin 2), (if x i = y i then (1 : ℂ) else 0))
      = (if x 0 = y 0 then (1 : ℂ) else 0) := by
  have h : Finset.univ.erase (1 : Fin 2) = ({0} : Finset (Fin 2)) := by decide
  rw [h, Finset.prod_singleton]

/-- Embedding an operator at coordinate zero preserves coordinate one and uses the operator's
entries on coordinate zero. -/
theorem regWire_zero (A : Operator 2) (x y : Reg 2) :
    mbqcRegWireGate 0 A x y
      = A (boolEquivFin2 (x 0)) (boolEquivFin2 (y 0)) * (if x 1 = y 1 then (1 : ℂ) else 0) := by
  rw [mbqcRegWireGate, Matrix.of_apply, prod_erase_zero]

/-- Embedding an operator at coordinate one preserves coordinate zero and uses the operator's
entries on coordinate one. -/
theorem regWire_one (A : Operator 2) (x y : Reg 2) :
    mbqcRegWireGate 1 A x y
      = A (boolEquivFin2 (x 1)) (boolEquivFin2 (y 1)) * (if x 0 = y 0 then (1 : ℂ) else 0) := by
  rw [mbqcRegWireGate, Matrix.of_apply, prod_erase_one]

/-- Embedding single-qubit operators at the same register coordinate preserves multiplication. -/
theorem regWire_mul (v : Fin 2) (A B : Operator 2) :
    mbqcRegWireGate v A * mbqcRegWireGate v B = mbqcRegWireGate v (A * B) := by
  have hval : (v : ℕ) = 0 ∨ (v : ℕ) = 1 := by have := v.isLt; omega
  rcases hval with h | h
  · have hv : v = (0 : Fin 2) := Fin.ext h
    subst v
    ext x y
    rw [Matrix.mul_apply]
    simp only [regWire_zero]
    rw [sum_reg2_eq]
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;>
      simp [boolEquivFin2, Matrix.mul_apply, Fin.sum_univ_two]
  · have hv : v = (1 : Fin 2) := Fin.ext h
    subst v
    ext x y
    rw [Matrix.mul_apply]
    simp only [regWire_one]
    rw [sum_reg2_eq]
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;>
      simp [boolEquivFin2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Embedding a single-qubit operator commutes with conjugate transpose. -/
theorem regWire_adj (v : Fin 2) (A : Operator 2) :
    (mbqcRegWireGate v A).conjTranspose = mbqcRegWireGate v A.conjTranspose := by
  have hv : v = (0 : Fin 2) ∨ v = (1 : Fin 2) := by have := v.isLt; omega
  rcases hv with rfl | rfl
  · ext x y
    rw [Matrix.conjTranspose_apply, regWire_zero, regWire_zero]
    by_cases h : x 1 = y 1
    · simp [h, Matrix.conjTranspose_apply]
    · simp [h, Matrix.conjTranspose_apply]
      intro he
      exact absurd he.symm h
  · ext x y
    rw [Matrix.conjTranspose_apply, regWire_one, regWire_one]
    by_cases h : x 0 = y 0
    · simp [h, Matrix.conjTranspose_apply]
    · simp [h, Matrix.conjTranspose_apply]
      intro he
      exact absurd he.symm h

/-- Operators embedded on the two distinct register coordinates commute. -/
theorem regWire_comm (A B : Operator 2) :
    mbqcRegWireGate (0 : Fin 2) A * mbqcRegWireGate (1 : Fin 2) B
      = mbqcRegWireGate (1 : Fin 2) B * mbqcRegWireGate (0 : Fin 2) A := by
  ext x y
  simp only [Matrix.mul_apply, regWire_zero, regWire_one]
  rw [sum_reg2_eq, sum_reg2_eq]
  cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;>
    simp [boolEquivFin2] <;> ring

/-- Relabeling register matrices by `bitVecEquiv` preserves matrix multiplication. -/
private theorem relabelGate_mul_local {n : ℕ} (A B : Matrix (Reg n) (Reg n) ℂ) :
    relabelGate (bitVecEquiv n) A * relabelGate (bitVecEquiv n) B
      = relabelGate (bitVecEquiv n) (A * B) := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact Equiv.sum_comp (bitVecEquiv n).symm
    (fun k => A ((bitVecEquiv n).symm i) k * B k ((bitVecEquiv n).symm j))

/-- The execution precedence relation never places a vertex strictly before itself. -/
theorem c5_not_prec_self (r : Fin 2 → Fin 2) (u : Fin 2) : ¬ mbqcExecPrec r u u := by
  intro hp
  simp only [mbqcExecPrec] at hp
  omega

/-- If one vertex is at most another in execution order, the latter does not strictly precede
the former. -/
theorem c5_not_prec_of_le (r : Fin 2 → Fin 2) (v w : Fin 2)
    (hle : mbqcExecLe r v w) : ¬ mbqcExecPrec r w v := by
  intro hp
  simp only [mbqcExecLe, mbqcExecPrec] at hle hp
  omega

/-- Pairwise execution-order comparison of a two-element list implies that its first element is
at most its second. -/
theorem c5_pairwise_two (r : Fin 2 → Fin 2) (a b : Fin 2)
    (hp : List.Pairwise (mbqcExecLe r) [a, b]) : mbqcExecLe r a b := by
  cases hp with
  | cons h _ => exact h b (List.mem_singleton_self b)

/-- With empty output set, the two-vertex execution order is either `[0, 1]` or `[1, 0]`. -/
theorem c5_execOrder_dichotomy (r : Fin 2 → Fin 2) :
    mbqcExecOrder (∅ : Finset (Fin 2)) r = [(0 : Fin 2), 1]
      ∨ mbqcExecOrder (∅ : Finset (Fin 2)) r = [1, 0] := by
  have hsort : mbqcExecOrder (∅ : Finset (Fin 2)) r
      = ({0, 1} : Finset (Fin 2)).sort (mbqcExecLe r) := by
    unfold mbqcExecOrder
    rw [Finset.sdiff_empty]
    have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [h]
  have hlen : (mbqcExecOrder (∅ : Finset (Fin 2)) r).length = 2 := by
    rw [hsort, Finset.length_sort]
    decide
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin 2,
      mbqcExecOrder (∅ : Finset (Fin 2)) r = [a, b] := List.length_eq_two.mp hlen
  have ha : a = (0 : Fin 2) ∨ a = (1 : Fin 2) := by
    have h : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by have := a.isLt; omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hb : b = (0 : Fin 2) ∨ b = (1 : Fin 2) := by
    have h : (b : ℕ) = 0 ∨ (b : ℕ) = 1 := by have := b.isLt; omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hperm : ([a, b] : List (Fin 2)).Perm [(0 : Fin 2), 1] := by
    rw [← hab]
    apply Multiset.coe_eq_coe.mp
    rw [hsort, Finset.sort_eq]
    exact (by decide : (([(0 : Fin 2), 1] : List (Fin 2)) : Multiset (Fin 2))
      = ({0, 1} : Finset (Fin 2)).val).symm
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb
  · have h1 : (1 : Fin 2) ∈ ([0, 0] : List (Fin 2)) := hperm.mem_iff.mpr (by simp)
    simp at h1
  · exact Or.inl hab
  · exact Or.inr hab
  · have h0 : (0 : Fin 2) ∈ ([1, 1] : List (Fin 2)) := hperm.mem_iff.mpr (by simp)
    simp at h0

/-- The two possible execution orders each satisfy the corresponding comparison of their first
and second vertices. -/
theorem c5_execLe_of_order (r : Fin 2 → Fin 2) :
    (mbqcExecOrder (∅ : Finset (Fin 2)) r = [(0 : Fin 2), 1] ∧ mbqcExecLe r 0 1)
      ∨ (mbqcExecOrder (∅ : Finset (Fin 2)) r = [1, 0] ∧ mbqcExecLe r 1 0) := by
  have hp : List.Pairwise (mbqcExecLe r) (mbqcExecOrder (∅ : Finset (Fin 2)) r) :=
    Finset.pairwise_sort _ _
  rcases c5_execOrder_dichotomy r with h | h
  · exact Or.inl ⟨h, c5_pairwise_two r _ _ (by rwa [h] at hp)⟩
  · exact Or.inr ⟨h, c5_pairwise_two r _ _ (by rwa [h] at hp)⟩

/-- The Pauli product matrix formed from identity operators on both wires is the identity. -/
theorem c5_ppd_one : pauliProductDensity (fun _ : Fin 2 => (1 : Operator 2)) = 1 := by
  ext x y
  show (∏ i : Fin 2, ((1 : Operator 2) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))))
      = (1 : Matrix (Reg 2) (Reg 2) ℂ) x y
  have hterm : ∀ i : Fin 2,
      ((1 : Operator 2) (boolEquivFin2 (x i)) (boolEquivFin2 (y i)))
        = (if x i = y i then (1 : ℂ) else 0) := by
    intro i
    simp only [Matrix.one_apply]
    by_cases h : x i = y i
    · simp [h]
    · have hne : boolEquivFin2 (x i) ≠ boolEquivFin2 (y i) :=
        fun he => h (boolEquivFin2.injective he)
      simp [hne, h]
  simp only [hterm, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    simp
  · have hex : ∃ i : Fin 2, x i ≠ y i := by
      by_contra hc
      apply h
      funext i
      by_contra hi
      exact hc ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

/-- Relabeling the two-qubit identity matrix by `bitVecEquiv 2` gives the identity. -/
theorem c5_relabel_one : relabelGate (bitVecEquiv 2) (1 : Matrix (Reg 2) (Reg 2) ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]

/-- With empty input set, the initial correction product is the identity, regardless of the
supplied corrections. -/
theorem c5_init_one (corr : (Fin 2 → Bool) → Fin 2 → Operator 2) (s : Fin 2 → Bool) :
    relabelGate (bitVecEquiv 2)
        (pauliProductDensity fun v => if v ∈ (∅ : Finset (Fin 2)) then corr s v else 1)
      = 1 := by
  have hfun : (fun v : Fin 2 => if v ∈ (∅ : Finset (Fin 2)) then corr s v else (1 : Operator 2))
      = fun _ : Fin 2 => (1 : Operator 2) := by
    funext v
    simp
  rw [hfun, c5_ppd_one, c5_relabel_one]

/-- Each measurement matrix `c5P b` satisfies `Pᴴ * P = P`. -/
theorem c5P_proj (b : Bool) : (c5P b).conjTranspose * c5P b = c5P b := by
  ext i j
  fin_cases i <;> fin_cases j <;> cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, c5P_apply] <;>
    simp [Complex.conj_I] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The two-qubit register matrix obtained by applying each correction and its `c5P` measurement
on the corresponding wire. -/
noncomputable def c5Ureg (corr : (Fin 2 → Bool) → Fin 2 → Operator 2) (s : Fin 2 → Bool) :
    Matrix (Reg 2) (Reg 2) ℂ :=
  mbqcRegWireGate 0 (c5P (s 0) * corr s 0) * mbqcRegWireGate 1 (c5P (s 1) * corr s 1)

/-- Embedding single-qubit operators into the finite-index wire representation preserves
multiplication. -/
theorem c5_wireGate_mul (v : Fin 2) (A B : Operator 2) :
    mbqcWireGate v A * mbqcWireGate v B = mbqcWireGate v (A * B) := by
  unfold mbqcWireGate
  rw [relabelGate_mul_local, regWire_mul]

/-- Single-qubit operators on wires zero and one commute in the finite-index representation. -/
theorem c5_wireGate_comm (A B : Operator 2) :
    mbqcWireGate (0 : Fin 2) A * mbqcWireGate (1 : Fin 2) B
      = mbqcWireGate (1 : Fin 2) B * mbqcWireGate (0 : Fin 2) A := by
  unfold mbqcWireGate
  rw [relabelGate_mul_local, relabelGate_mul_local, regWire_comm]

/-- For empty outputs and XY measurements at angle `π / 2`, the interleaved two-vertex gate is
the relabeling of `c5Ureg`, independently of the rank function. -/
theorem c5_interleaved (r : Fin 2 → Fin 2) (corr : (Fin 2 → Bool) → Fin 2 → Operator 2)
    (s : Fin 2 → Bool) :
    mbqcInterleavedGate (∅ : Finset (Fin 2)) r (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s
      = relabelGate (bitVecEquiv 2) (c5Ureg corr s) := by
  rcases c5_execOrder_dichotomy r with h | h
  · rw [mbqcInterleavedGate, h, c5_init_one]
    show (mbqcWireGate (1 : Fin 2) (c5P (s 1)) * mbqcWireGate 1 (corr s 1))
        * (mbqcWireGate (0 : Fin 2) (c5P (s 0)) * mbqcWireGate 0 (corr s 0) * 1)
        = relabelGate (bitVecEquiv 2) (c5Ureg corr s)
    rw [mul_one, c5_wireGate_mul, c5_wireGate_mul, ← c5_wireGate_comm]
    unfold mbqcWireGate
    rw [relabelGate_mul_local]
    rfl
  · rw [mbqcInterleavedGate, h, c5_init_one]
    show (mbqcWireGate (0 : Fin 2) (c5P (s 0)) * mbqcWireGate 0 (corr s 0))
        * (mbqcWireGate (1 : Fin 2) (c5P (s 1)) * mbqcWireGate 1 (corr s 1) * 1)
        = relabelGate (bitVecEquiv 2) (c5Ureg corr s)
    rw [mul_one, c5_wireGate_mul, c5_wireGate_mul]
    unfold mbqcWireGate
    rw [relabelGate_mul_local]
    rfl

/-- The row sum of the single-edge CZ matrix equals its controlled phase at that row. -/
theorem c5_czRow_sum (w : Reg 2) :
    ∑ y : Reg 2, czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2)) w y
      = (if w 0 && w 1 then (-1 : ℂ) else 1) := by
  have h : ∀ y : Reg 2, czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2)) w y
      = (if w = y then (if w 0 && w 1 then (-1 : ℂ) else 1) else 0) := by
    intro y
    rw [c5_czDiag]
  simp only [h]
  rw [Fintype.sum_eq_single w]
  · rw [if_pos rfl]
  · intro y hy
    rw [if_neg (fun he => hy he.symm)]

/-- Entries of a matrix relabeled by `bitVecEquiv 2` are obtained by applying the inverse
equivalence to both indices. -/
theorem c5_relabel_apply (M : Matrix (Reg 2) (Reg 2) ℂ) (i j : Fin 4) :
    relabelGate (bitVecEquiv 2) M i j = M ((bitVecEquiv 2).symm i) ((bitVecEquiv 2).symm j) := by
  simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]

/-- A double sum over four-element indices reindexes to a double sum over two-bit registers. -/
theorem c5_reindex_double (F : Reg 2 → Reg 2 → ℂ) :
    (∑ x : Fin 4, ∑ x_1 : Fin 4, F ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x))
      = ∑ w : Reg 2, ∑ y : Reg 2, F y w := by
  have hinner : ∀ x : Fin 4,
      (∑ x_1 : Fin 4, F ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x))
        = ∑ y : Reg 2, F y ((bitVecEquiv 2).symm x) := by
    intro x
    exact Equiv.sum_comp (bitVecEquiv 2).symm
      (fun y : Reg 2 => F y ((bitVecEquiv 2).symm x))
  simp only [hinner]
  exact Equiv.sum_comp (bitVecEquiv 2).symm (fun w : Reg 2 => ∑ y : Reg 2, F y w)

/-- The scalar Kraus entry of the empty-boundary counterexample is one half of the row sum of
`c5Ureg` weighted by the CZ phase. -/
theorem c5_kraus_raw (r : Fin 2 → Fin 2) (corr : (Fin 2 → Bool) → Fin 2 → Operator 2)
    (s z : Fin 2 → Bool) :
    mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
        (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z 0 0
      = (1 / 2 : ℂ) * ∑ w : Reg 2, c5Ureg corr s z w * (if w 0 && w 1 then (-1 : ℂ) else 1) := by
  have hent : mbqcEntangler mbqcCounterexampleGraph
      = relabelGate (bitVecEquiv 2) (czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))) := rfl
  have hout : ∀ x : Fin 4, mbqcOutputFrame (∅ : Finset (Fin 2)) z 0 x
      = (if x = bitVecEquiv 2 z then (1 : ℂ) else 0) := fun x => c5_outFrame z 0 x
  have hin : ∀ x : Fin 4, mbqcInputFrame (∅ : Finset (Fin 2)) x 0 = (1 / 2 : ℂ) :=
    fun x => c5_inFrame x 0
  have hpick : ∀ x_1 : Fin 4,
      (∑ j : Fin 4, (if j = bitVecEquiv 2 z then (1 : ℂ) else 0)
          * relabelGate (bitVecEquiv 2) (c5Ureg corr s) j x_1)
        = relabelGate (bitVecEquiv 2) (c5Ureg corr s) (bitVecEquiv 2 z) x_1 := by
    intro x_1
    have hite : ∀ j : Fin 4,
        (if j = bitVecEquiv 2 z then (1 : ℂ) else 0)
            * relabelGate (bitVecEquiv 2) (c5Ureg corr s) j x_1
          = (if j = bitVecEquiv 2 z
              then relabelGate (bitVecEquiv 2) (c5Ureg corr s) j x_1 else 0) := by
      intro j
      by_cases h : j = bitVecEquiv 2 z <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => hite j)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin 4)) (bitVecEquiv 2 z)
        (fun j => relabelGate (bitVecEquiv 2) (c5Ureg corr s) j x_1)]
    rw [if_pos (Finset.mem_univ _)]
  have hpoint : ∀ x x_1 : Fin 4,
      relabelGate (bitVecEquiv 2) (c5Ureg corr s) (bitVecEquiv 2 z) x_1
          * relabelGate (bitVecEquiv 2) (czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))) x_1 x
        = c5Ureg corr s z ((bitVecEquiv 2).symm x_1)
          * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))
              ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x) := by
    intro x x_1
    rw [c5_relabel_apply, c5_relabel_apply, Equiv.symm_apply_apply]
  have hre :
      (∑ x : Fin 4, (∑ x_1 : Fin 4,
            c5Ureg corr s z ((bitVecEquiv 2).symm x_1)
              * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))
                  ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x))
          * (1 / 2 : ℂ))
      = (1 / 2 : ℂ) * ∑ w : Reg 2,
          c5Ureg corr s z w * (if w 0 && w 1 then (-1 : ℂ) else 1) := by
    have hmul : ∀ x : Fin 4,
        (∑ x_1 : Fin 4,
            c5Ureg corr s z ((bitVecEquiv 2).symm x_1)
              * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))
                  ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x))
          * (1 / 2 : ℂ)
          = (1 / 2 : ℂ) * (∑ x_1 : Fin 4,
            c5Ureg corr s z ((bitVecEquiv 2).symm x_1)
              * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))
                  ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x)) := by
      intro x
      ring
    rw [Finset.sum_congr rfl (fun x _ => hmul x), ← Finset.mul_sum]
    congr 1
    have hri := c5_reindex_double
      (fun y w : Reg 2 => c5Ureg corr s z y * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2)) y w)
    have hswap : (∑ w : Reg 2, ∑ y : Reg 2,
            c5Ureg corr s z y * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2)) y w)
        = ∑ y : Reg 2, c5Ureg corr s z y
            * (if y 0 && y 1 then (-1 : ℂ) else 1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      exact c5_czRow_sum y
    exact hri.trans hswap
  have hcoll :
      (∑ x : Fin 4, (∑ x_1 : Fin 4,
            relabelGate (bitVecEquiv 2) (c5Ureg corr s) (bitVecEquiv 2 z) x_1
              * relabelGate (bitVecEquiv 2) (czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))) x_1 x)
          * (1 / 2 : ℂ))
      = (∑ x : Fin 4, (∑ x_1 : Fin 4,
            c5Ureg corr s z ((bitVecEquiv 2).symm x_1)
              * czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))
                  ((bitVecEquiv 2).symm x_1) ((bitVecEquiv 2).symm x))
          * (1 / 2 : ℂ)) :=
    Finset.sum_congr rfl (fun x _ =>
      congrArg (fun t : ℂ => t * (1 / 2 : ℂ))
        (Finset.sum_congr rfl (fun x_1 _ => hpoint x x_1)))
  have hexp :
      (∑ x : Fin 4, (∑ x_1 : Fin 4, (∑ j : Fin 4, (if j = bitVecEquiv 2 z then (1 : ℂ) else 0)
              * relabelGate (bitVecEquiv 2) (c5Ureg corr s) j x_1)
            * relabelGate (bitVecEquiv 2) (czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))) x_1 x)
          * (1 / 2 : ℂ))
      = (∑ x : Fin 4, (∑ x_1 : Fin 4,
            relabelGate (bitVecEquiv 2) (c5Ureg corr s) (bitVecEquiv 2 z) x_1
              * relabelGate (bitVecEquiv 2) (czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))) x_1 x)
          * (1 / 2 : ℂ)) :=
    Finset.sum_congr rfl (fun x _ =>
      congrArg (fun t : ℂ => t * (1 / 2 : ℂ))
        (Finset.sum_congr rfl (fun x_1 _ =>
          congrArg (fun t : ℂ =>
            t * relabelGate (bitVecEquiv 2) (czMatrix ({(0, 1)} : Finset (Fin 2 × Fin 2))) x_1 x)
            (hpick x_1))))
  unfold mbqcPatternKraus
  rw [c5_interleaved, hent]
  simp only [Matrix.mul_apply]
  simp only [hout, hin]
  exact hexp.trans (hcoll.trans hre)

/-- The scalar Kraus entry of the empty-boundary counterexample equals the corresponding
coordinate of `c5Ureg corr s` applied to `c5ψ`. -/
theorem c5_kraus (r : Fin 2 → Fin 2) (corr : (Fin 2 → Bool) → Fin 2 → Operator 2)
    (s z : Fin 2 → Bool) :
    mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
        (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z 0 0
      = (c5Ureg corr s *ᵥ c5ψ) z := by
  rw [c5_kraus_raw]
  have hphase : ∀ w : Reg 2, (if w 0 && w 1 then (-1 : ℂ) else 1) = 2 * c5ψ w := c5_phase_eq
  simp only [hphase]
  have h2 : ∀ w : Reg 2, c5Ureg corr s z w * (2 * c5ψ w)
      = 2 * (c5Ureg corr s z w * c5ψ w) := by
    intro w
    ring
  simp only [h2, Finset.mul_sum]
  have h3 : ∀ w : Reg 2, (1 / 2 : ℂ) * (2 * (c5Ureg corr s z w * c5ψ w))
      = c5Ureg corr s z w * c5ψ w := by
    intro w
    ring
  simp only [h3]
  rfl

/-- For a product of operators on separate wires, its adjoint product factors into the embedded
single-qubit adjoint products. -/
theorem c5_UdagU (A B : Operator 2) :
    ((mbqcRegWireGate (0 : Fin 2) A * mbqcRegWireGate (1 : Fin 2) B :
        Matrix (Reg 2) (Reg 2) ℂ)).conjTranspose
        * (mbqcRegWireGate (0 : Fin 2) A * mbqcRegWireGate (1 : Fin 2) B)
      = mbqcRegWireGate (0 : Fin 2) (A.conjTranspose * A)
          * mbqcRegWireGate (1 : Fin 2) (B.conjTranspose * B) := by
  rw [Matrix.conjTranspose_mul, regWire_adj, regWire_adj]
  have hassoc : (mbqcRegWireGate (1 : Fin 2) B.conjTranspose
        * mbqcRegWireGate (0 : Fin 2) A.conjTranspose)
      * (mbqcRegWireGate (0 : Fin 2) A * mbqcRegWireGate (1 : Fin 2) B)
      = mbqcRegWireGate (1 : Fin 2) B.conjTranspose
          * (mbqcRegWireGate (0 : Fin 2) (A.conjTranspose * A)
              * mbqcRegWireGate (1 : Fin 2) B) := by
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, regWire_mul]
  rw [hassoc]
  have hcomm : mbqcRegWireGate (1 : Fin 2) B.conjTranspose
        * (mbqcRegWireGate (0 : Fin 2) (A.conjTranspose * A)
            * mbqcRegWireGate (1 : Fin 2) B)
      = mbqcRegWireGate (0 : Fin 2) (A.conjTranspose * A)
          * (mbqcRegWireGate (1 : Fin 2) B.conjTranspose
              * mbqcRegWireGate (1 : Fin 2) B) := by
    rw [← mul_assoc, ← regWire_comm, mul_assoc]
  rw [hcomm]
  congr 1
  rw [regWire_mul]

/-- The sum of squared output moduli of `M` applied to `c5ψ` equals the quadratic form of `Mᴴ *
M` in `c5ψ`. -/
theorem c5_norm_form (M : Matrix (Reg 2) (Reg 2) ℂ) :
    (∑ z : Reg 2, (M *ᵥ c5ψ) z * star ((M *ᵥ c5ψ) z))
      = ∑ u : Reg 2, ∑ v : Reg 2,
          star (c5ψ u) * (M.conjTranspose * M) u v * c5ψ v := by
  have hvec : ∀ z : Reg 2, (M *ᵥ c5ψ) z = ∑ y : Reg 2, M z y * c5ψ y := fun _ => rfl
  have hconj : ∀ w y : Reg 2, (M.conjTranspose * M) w y
      = ∑ z : Reg 2, star (M z w) * M z y := by
    intro w y
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
  have hstar : ∀ z : Reg 2, star (∑ w : Reg 2, M z w * c5ψ w)
      = ∑ w : Reg 2, star (M z w) * star (c5ψ w) := by
    intro z
    rw [← starRingEnd_apply]
    rw [map_sum (starRingEnd ℂ)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply]
  have hexp :
      (∑ z : Reg 2, (M *ᵥ c5ψ) z * star ((M *ᵥ c5ψ) z))
        = ∑ y : Reg 2, ∑ w : Reg 2,
            star (c5ψ w) * (M.conjTranspose * M) w y * c5ψ y := by
    have hz : ∀ z : Reg 2, (M *ᵥ c5ψ) z * star ((M *ᵥ c5ψ) z)
        = (∑ y : Reg 2, M z y * c5ψ y) * (∑ w : Reg 2, star (M z w) * star (c5ψ w)) := by
      intro z
      rw [hvec z]
      congr 1
      exact hstar z
    rw [Finset.sum_congr rfl (fun z _ => hz z)]
    have hyz : ∀ z : Reg 2,
        (∑ y : Reg 2, M z y * c5ψ y) * (∑ w : Reg 2, star (M z w) * star (c5ψ w))
          = ∑ y : Reg 2, ∑ w : Reg 2,
              (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y := by
      intro z
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hm := Finset.mul_sum Finset.univ
        (fun w : Reg 2 => star (M z w) * star (c5ψ w)) (M z y * c5ψ y)
      rw [hm]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    rw [Finset.sum_congr rfl (fun z _ => hyz z)]
    have hswap1 : (∑ z : Reg 2, ∑ y : Reg 2, ∑ w : Reg 2,
            (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y)
        = ∑ y : Reg 2, ∑ z : Reg 2, ∑ w : Reg 2,
            (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y :=
      Finset.sum_comm
    rw [hswap1]
    have hswap2 : (∑ y : Reg 2, ∑ z : Reg 2, ∑ w : Reg 2,
            (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y)
        = ∑ y : Reg 2, ∑ w : Reg 2, ∑ z : Reg 2,
            (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y := by
      refine Finset.sum_congr rfl fun y _ => ?_
      exact Finset.sum_comm
    rw [hswap2]
    have hpull : ∀ y w : Reg 2,
        (∑ z : Reg 2, (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y)
          = star (c5ψ w) * (∑ z : Reg 2, star (M z w) * M z y) * c5ψ y := by
      intro y w
      have hh : ∀ z : Reg 2, (star (c5ψ w) * (star (M z w) * M z y)) * c5ψ y
          = star (c5ψ w) * ((star (M z w) * M z y) * c5ψ y) := by
        intro z
        ring
      rw [Finset.sum_congr rfl (fun z _ => hh z)]
      have h1 := Finset.mul_sum Finset.univ
        (fun z : Reg 2 => (star (M z w) * M z y) * c5ψ y) (star (c5ψ w))
      rw [← h1]
      have h2 := Finset.sum_mul Finset.univ
        (fun z : Reg 2 => star (M z w) * M z y) (c5ψ y)
      rw [← h2]
      ring
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun w _ => hpull y w))]
    have hfinal : (∑ y : Reg 2, ∑ w : Reg 2,
            star (c5ψ w) * (∑ z : Reg 2, star (M z w) * M z y) * c5ψ y)
        = ∑ y : Reg 2, ∑ w : Reg 2,
            star (c5ψ w) * (M.conjTranspose * M) w y * c5ψ y :=
      Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun w _ =>
        congrArg (fun t : ℂ => star (c5ψ w) * t * c5ψ y) (hconj w y)))
    rw [hfinal]
  rw [hexp]
  exact Finset.sum_comm

/-- An entry of the product of operators on separate register wires is the product of their
corresponding single-qubit entries. -/
theorem c5_regWire01 (A B : Operator 2) (u v : Reg 2) :
    (mbqcRegWireGate (0 : Fin 2) A * mbqcRegWireGate (1 : Fin 2) B) u v
      = A (boolEquivFin2 (u 0)) (boolEquivFin2 (v 0))
          * B (boolEquivFin2 (u 1)) (boolEquivFin2 (v 1)) := by
  rw [Matrix.mul_apply]
  simp only [regWire_zero, regWire_one]
  rw [sum_reg2_eq]
  cases u 0 <;> cases u 1 <;> cases v 0 <;> cases v 1 <;>
    simp [boolEquivFin2]

/-- The expectation `c5E A B` equals the quadratic form of the corresponding product of embedded
wire operators in `c5ψ`. -/
theorem c5E_eq_quad (A B : Operator 2) :
    c5E A B
      = ∑ u : Reg 2, ∑ v : Reg 2,
          star (c5ψ u) * (mbqcRegWireGate (0 : Fin 2) A
            * mbqcRegWireGate (1 : Fin 2) B) u v * c5ψ v := by
  unfold c5E
  exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => by
    rw [c5_regWire01]
    ring))

/-- For permitted Pauli corrections, the adjoint product of `c5Ureg` is the product of
measurement matrices with outcome labels changed by the correction flip flags. -/
theorem c5_UdagU_reg (corr : (Fin 2 → Bool) → Fin 2 → Operator 2) (s : Fin 2 → Bool)
    (h0 : MbqcPauliWire (corr s 0)) (h1 : MbqcPauliWire (corr s 1)) :
    (c5Ureg corr s).conjTranspose * c5Ureg corr s
      = mbqcRegWireGate (0 : Fin 2) (c5P ((s 0).xor (c5flip (corr s 0))))
        * mbqcRegWireGate (1 : Fin 2) (c5P ((s 1).xor (c5flip (corr s 1)))) := by
  unfold c5Ureg
  rw [c5_UdagU]
  have hA : ((c5P (s 0) * corr s 0 : Operator 2)).conjTranspose * (c5P (s 0) * corr s 0)
      = c5P ((s 0).xor (c5flip (corr s 0))) := by
    rw [Matrix.conjTranspose_mul]
    have hassoc : (corr s 0).conjTranspose * (c5P (s 0)).conjTranspose
        * (c5P (s 0) * corr s 0)
        = ((corr s 0).conjTranspose * c5P (s 0)) * corr s 0 := by
      simp only [mul_assoc]
      congr 1
      rw [← mul_assoc, c5P_proj]
    rw [hassoc]
    exact c5_conj (corr s 0) h0 (s 0)
  have hB : ((c5P (s 1) * corr s 1 : Operator 2)).conjTranspose * (c5P (s 1) * corr s 1)
      = c5P ((s 1).xor (c5flip (corr s 1))) := by
    rw [Matrix.conjTranspose_mul]
    have hassoc : (corr s 1).conjTranspose * (c5P (s 1)).conjTranspose
        * (c5P (s 1) * corr s 1)
        = ((corr s 1).conjTranspose * c5P (s 1)) * corr s 1 := by
      simp only [mul_assoc]
      congr 1
      rw [← mul_assoc, c5P_proj]
    rw [hassoc]
    exact c5_conj (corr s 1) h1 (s 1)
  rw [hA, hB]

/-- Multiplication of one-dimensional operators is multiplication of their sole entries. -/
theorem c5_mul_1x1 (P Q : Operator 1) : (P * Q) 0 0 = P 0 0 * Q 0 0 := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single (0 : Fin 1) ?_
  intro x hx
  fin_cases x
  exact absurd rfl hx

/-- The sole entry of a finite sum of one-dimensional matrices is the sum of their sole entries. -/
theorem c5_sum_entry {ι : Type} [Fintype ι] (F : ι → Matrix (Fin 1) (Fin 1) ℂ) :
    (∑ d : ι, F d) 0 0 = ∑ d : ι, F d 0 0 := by
  have h1 : (∑ d : ι, F d) 0 = (∑ d : ι, F d 0) :=
    Finset.sum_apply (0 : Fin 1) Finset.univ (fun d : ι => F d)
  rw [h1]
  have h2 : (∑ d : ι, F d 0) 0 = (∑ d : ι, F d 0 0) :=
    Finset.sum_apply (0 : Fin 1) Finset.univ (fun d : ι => F d 0)
  rw [h2]

/-- Conjugating the one-dimensional identity by `M` gives the product of its sole entry with its
conjugate. -/
theorem c5_conj_entry (M : Matrix (Fin 1) (Fin 1) ℂ) :
    (conjBranch M (1 : Operator 1)) 0 0 = M 0 0 * star (M 0 0) := by
  rw [conjBranch_apply]
  rw [Matrix.mul_one]
  rw [c5_mul_1x1]
  rw [Matrix.conjTranspose_apply]

/-- For permitted Pauli corrections, the counterexample branch on the scalar identity is one
half when the corrected outcome labels agree and zero otherwise. -/
theorem c5_branch_value (r : Fin 2 → Fin 2) (corr : (Fin 2 → Bool) → Fin 2 → Operator 2)
    (s : Fin 2 → Bool) (h0 : MbqcPauliWire (corr s 0)) (h1 : MbqcPauliWire (corr s 1)) :
    mbqcPatternBranch mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
        (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s (1 : Operator 1) 0 0
      = (if ((s 0).xor (c5flip (corr s 0))) = ((s 1).xor (c5flip (corr s 1)))
          then (1 / 2 : ℂ) else 0) := by
  have hkey :
      mbqcPatternBranch mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
          (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s (1 : Operator 1) 0 0
        = c5E (c5P ((s 0).xor (c5flip (corr s 0))))
            (c5P ((s 1).xor (c5flip (corr s 1)))) := by
    have hK : ∀ z : Fin 2 → Bool,
        (conjBranch (mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2))
            (∅ : Finset (Fin 2)) r (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z)
            (1 : Operator 1)) 0 0
          = (mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
              (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z 0 0)
            * star (mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2))
              (∅ : Finset (Fin 2)) r (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z 0 0) := by
      intro z
      exact c5_conj_entry _
    have hpush :
        mbqcPatternBranch mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
            (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s (1 : Operator 1) 0 0
          = ∑ z : Fin 2 → Bool,
              (conjBranch (mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2))
                (∅ : Finset (Fin 2)) r (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z)
                  (1 : Operator 1)) 0 0 := by
      unfold mbqcPatternBranch mbqcPatternBranchMap
      rw [LinearMap.sum_apply Finset.univ]
      exact c5_sum_entry _
    rw [hpush, Finset.sum_congr rfl (fun z _ => hK z)]
    have hk2 : ∀ z : Fin 2 → Bool,
        (mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
            (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z 0 0)
          * star (mbqcPatternKraus mbqcCounterexampleGraph (∅ : Finset (Fin 2))
            (∅ : Finset (Fin 2)) r (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s z 0 0)
        = (c5Ureg corr s *ᵥ c5ψ) z * star ((c5Ureg corr s *ᵥ c5ψ) z) := by
      intro z
      rw [c5_kraus r corr s z]
    rw [Finset.sum_congr rfl (fun z _ => hk2 z)]
    have hnorm := c5_norm_form (c5Ureg corr s)
    rw [hnorm]
    rw [c5_UdagU_reg corr s h0 h1]
    rw [← c5E_eq_quad]
  rw [hkey]
  rw [c5base]

/-- The equality-conditioned values one half and zero change when the second Boolean argument is
negated. -/
theorem c5_if_ne_right (x y : Bool) :
    (if x = y then (1 / 2 : ℂ) else 0) ≠ (if x = y.not then (1 / 2 : ℂ) else 0) := by
  cases x <;> cases y <;> simp

/-- The equality-conditioned values one half and zero change when the first Boolean argument is
negated. -/
theorem c5_if_ne_left (x y : Bool) :
    (if x = y then (1 / 2 : ℂ) else 0) ≠ (if x.not = y then (1 / 2 : ℂ) else 0) := by
  cases x <;> cases y <;> simp

/-- The two-vertex counterexample graph with empty input and output sets and XY measurements at
angle `π / 2` is not strongly deterministic. -/
theorem clause6_clause5 :
    ¬ MbqcStronglyDeterministic mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2))
      (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) := by
  intro hex
  obtain ⟨r, corr, hpauli, hcausal, hall⟩ := hex
  have hρ : IsDensityOperator (1 : Operator 1) :=
    ⟨(Matrix.PosSemidef.one : (1 : Operator 1).PosSemidef), by simp⟩
  have hall' : ∀ s s' : Fin 2 → Bool,
      (mbqcPatternBranch mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
          (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s (1 : Operator 1)) 0 0
        = (mbqcPatternBranch mbqcCounterexampleGraph (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) r
          (fun _ => MbqcPlane.XY) (fun _ => Real.pi / 2) corr s' (1 : Operator 1)) 0 0 := by
    intro s s'
    exact congrArg (fun M => M 0 0) (hall (1 : Operator 1) hρ s s')
  have hu01 : ∀ u : Fin 2, u = (0 : Fin 2) ∨ u = (1 : Fin 2) := by
    intro u
    have h : (u : ℕ) = 0 ∨ (u : ℕ) = 1 := by have := u.isLt; omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases c5_execLe_of_order r with h | h
  · obtain ⟨horder, hle⟩ := h
    have hprec00 : ¬ mbqcExecPrec r 0 0 := c5_not_prec_self r 0
    have hprec11 : ¬ mbqcExecPrec r 1 1 := c5_not_prec_self r 1
    have hprec10 : ¬ mbqcExecPrec r 1 0 := c5_not_prec_of_le r 0 1 hle
    set sA : Fin 2 → Bool := fun _ => false with hsA
    set sB : Fin 2 → Bool := fun i => if i = (1 : Fin 2) then true else false with hsB
    have hvalA : sA 0 = false ∧ sA 1 = false := by
      rw [hsA]; constructor <;> rfl
    have hvalB : sB 0 = false ∧ sB 1 = true := by
      rw [hsB]
      constructor
      · exact if_neg (by decide)
      · exact if_pos rfl
    have hcorr : corr sA 0 = corr sB 0 ∧ corr sA 1 = corr sB 1 := by
      constructor
      · apply hcausal sA sB 0
        intro u hu
        rcases hu01 u with hu | hu
        · subst hu; exact absurd hu hprec00
        · subst hu; exact absurd hu hprec10
      · apply hcausal sA sB 1
        intro u hu
        rcases hu01 u with hu | hu
        · subst hu; rw [hvalA.1, hvalB.1]
        · subst hu; exact absurd hu hprec11
    have hbranch := hall' sA sB
    rw [c5_branch_value r corr sA (hpauli sA 0) (hpauli sA 1)] at hbranch
    rw [c5_branch_value r corr sB (hpauli sB 0) (hpauli sB 1)] at hbranch
    simp only [hvalA, hvalB] at hbranch
    rw [← hcorr.1, ← hcorr.2] at hbranch
    simp only [Bool.false_xor, Bool.true_xor] at hbranch
    exact c5_if_ne_right (c5flip (corr sA 0)) (c5flip (corr sA 1)) hbranch
  · obtain ⟨horder, hle⟩ := h
    have hprec00 : ¬ mbqcExecPrec r 0 0 := c5_not_prec_self r 0
    have hprec11 : ¬ mbqcExecPrec r 1 1 := c5_not_prec_self r 1
    have hprec01 : ¬ mbqcExecPrec r 0 1 := c5_not_prec_of_le r 1 0 hle
    set sA : Fin 2 → Bool := fun _ => false with hsA
    set sB : Fin 2 → Bool := fun i => if i = (0 : Fin 2) then true else false with hsB
    have hvalA : sA 0 = false ∧ sA 1 = false := by
      rw [hsA]; constructor <;> rfl
    have hvalB : sB 0 = true ∧ sB 1 = false := by
      rw [hsB]
      constructor
      · exact if_pos rfl
      · exact if_neg (by decide)
    have hcorr : corr sA 0 = corr sB 0 ∧ corr sA 1 = corr sB 1 := by
      constructor
      · apply hcausal sA sB 0
        intro u hu
        rcases hu01 u with hu | hu
        · subst hu; exact absurd hu hprec00
        · subst hu; rw [hvalA.2, hvalB.2]
      · apply hcausal sA sB 1
        intro u hu
        rcases hu01 u with hu | hu
        · subst hu; exact absurd hu hprec01
        · subst hu; exact absurd hu hprec11
    have hbranch := hall' sA sB
    rw [c5_branch_value r corr sA (hpauli sA 0) (hpauli sA 1)] at hbranch
    rw [c5_branch_value r corr sB (hpauli sB 0) (hpauli sB 1)] at hbranch
    simp only [hvalA, hvalB] at hbranch
    rw [← hcorr.1, ← hcorr.2] at hbranch
    simp only [Bool.false_xor, Bool.true_xor] at hbranch
    exact c5_if_ne_left (c5flip (corr sA 0)) (c5flip (corr sA 1)) hbranch
end Qatlib.Concepts.MbqcFlow.FlowDecision.FlowExtended
