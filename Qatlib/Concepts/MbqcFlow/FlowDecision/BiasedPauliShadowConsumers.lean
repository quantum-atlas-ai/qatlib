/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleShadows
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem ensembleProjector_pauliBasis (a : Fin 3) (b : Fin 2) :
    ensembleProjector pauliBasisMatrix (a, b) = PauliProjector a (decide (b = 0)) := by
  fin_cases b
  · exact axis_leaf_operator a true
  · exact axis_leaf_operator a false

theorem pauli_expansion (B : Operator 2) :
    B = (1 / 2 : ℂ) • (Matrix.trace B • (1 : Operator 2)
      + ∑ a : Fin 3, Matrix.trace (pauliMatrix a * B) • pauliMatrix a) := by
  simpa only [Qatlib.Concepts.GateVocabulary.GateVocab.pauliAxis_legacy] using
      Qatlib.Concepts.GateVocabulary.GateVocab.pauli_axis_expansion B

theorem pauliProjector_sub (a : Fin 3) :
    PauliProjector a true - PauliProjector a false = pauliMatrix a := by
  simp only [PauliProjector, if_true, Bool.false_eq_true, if_false]
  module

theorem ensembleProjector_sum_pauli (a : Fin 3) (B : Operator 2) :
    ∑ b : Fin 2, Matrix.trace (ensembleProjector pauliBasisMatrix (a, b) * B)
        • ensembleProjector pauliBasisMatrix (a, b)
      = (1 / 2 : ℂ) • (Matrix.trace B • (1 : Operator 2)
          + Matrix.trace (pauliMatrix a * B) • pauliMatrix a) := by
  have h0 : ensembleProjector pauliBasisMatrix (a, 0) = PauliProjector a true := by
    rw [ensembleProjector_pauliBasis]; rfl
  have h1 : ensembleProjector pauliBasisMatrix (a, 1) = PauliProjector a false := by
    rw [ensembleProjector_pauliBasis]; rfl
  have hPP : ∀ b : Bool, PauliProjector a b
      = (1 / 2 : ℂ) • (1 : Operator 2)
        + ((if b then 1 else -1 : ℂ) / 2) • pauliMatrix a := by
    intro b
    simp only [PauliProjector]
    module
  have htr : ∀ b : Bool, Matrix.trace (PauliProjector a b * B)
      = (1 / 2 : ℂ) * Matrix.trace B
        + ((if b then 1 else -1 : ℂ) / 2) * Matrix.trace (pauliMatrix a * B) := by
    intro b
    rw [hPP b, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, Matrix.one_mul]
  rw [Fin.sum_univ_two, h0, h1, htr true, htr false, hPP true, hPP false]
  simp only [if_true, Bool.false_eq_true, if_false]
  module

local instance : HMul ℂ (Operator 2) (Operator 2) := ⟨fun c M => c • M⟩

theorem complex_mul_operator (c : ℂ) (M : Operator 2) : c * M = c • M := rfl

theorem ensembleMeasurementMap_pauli (p : FinDist (Fin 3)) (B : Operator 2) :
    ensembleMeasurementMap p pauliBasisMatrix B
      = ((1 / 2 : ℂ) * Matrix.trace B) • (1 : Operator 2)
        + ∑ a : Fin 3, ((p.prob a / 2 : ℂ) * Matrix.trace (pauliMatrix a * B))
            • pauliMatrix a := by
  have key : ∀ a : Fin 3,
      ∑ b : Fin 2, ((p.prob a : ℂ)
          * Matrix.trace (ensembleProjector pauliBasisMatrix (a, b) * B))
          • ensembleProjector pauliBasisMatrix (a, b)
        = ((p.prob a / 2 : ℂ) * Matrix.trace B) • (1 : Operator 2)
          + ((p.prob a / 2 : ℂ) * Matrix.trace (pauliMatrix a * B)) • pauliMatrix a := by
    intro a
    have hsm : ∀ b : Fin 2, ((p.prob a : ℂ)
        * Matrix.trace (ensembleProjector pauliBasisMatrix (a, b) * B))
        • ensembleProjector pauliBasisMatrix (a, b)
        = (p.prob a : ℂ)
          • Matrix.trace (ensembleProjector pauliBasisMatrix (a, b) * B)
            • ensembleProjector pauliBasisMatrix (a, b) := fun b => (smul_smul _ _ _).symm
    rw [Finset.sum_congr rfl fun b _ => hsm b, ← Finset.smul_sum,
      ensembleProjector_sum_pauli a B, smul_smul, smul_add, smul_smul, smul_smul]
    module
  rw [ensembleMeasurementMap_apply,
    Fintype.sum_prod_type'
      (fun a b => ((p.prob a : ℂ)
        * Matrix.trace (ensembleProjector pauliBasisMatrix (a, b) * B))
        • ensembleProjector pauliBasisMatrix (a, b)),
    Finset.sum_congr rfl fun a _ => key a, Finset.sum_add_distrib, ← Finset.sum_smul,
    show (∑ a : Fin 3, ((p.prob a / 2 : ℂ) * Matrix.trace B))
        = (1 / 2 : ℂ) * Matrix.trace B from by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← Complex.ofReal_sum, p.sum_one]
      norm_num]

theorem ensembleMeasurementMap_pauliMatrix (p : FinDist (Fin 3)) (c : Fin 3) :
    ensembleMeasurementMap p pauliBasisMatrix (pauliMatrix c)
      = (p.prob c : ℂ) • pauliMatrix c := by
  rw [ensembleMeasurementMap_pauli, trace_pauliMatrix,
    mul_zero, zero_smul, zero_add, Finset.sum_eq_single c]
  · rw [trace_pauliMatrix_mul, if_pos rfl]
    congr 1
    ring
  · intro a _ ha
    rw [trace_pauliMatrix_mul, if_neg ha, mul_zero, zero_smul]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

noncomputable def pauliInverseMap (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a) :
    Operator 2 → Operator 2 :=
  fun B => (1 / 2 : ℂ) • (Matrix.trace B • (1 : Operator 2)
    + ∑ a : Fin 3, ((p.prob a : ℂ)⁻¹ * Matrix.trace (pauliMatrix a * B))
        • pauliMatrix a)

theorem ensembleMeasurementMap_pauli_apply_pauli (p : FinDist (Fin 3)) (c : Fin 3)
    (B : Operator 2) :
    Matrix.trace (pauliMatrix c * ensembleMeasurementMap p pauliBasisMatrix B)
      = (p.prob c : ℂ) * Matrix.trace (pauliMatrix c * B) := by
  have h := ensembleMeasurementMap_trace_adjoint p pauliBasisMatrix (pauliMatrix c) B
  rw [ensembleMeasurementMap_pauliMatrix, Matrix.smul_mul, Matrix.trace_smul] at h
  exact h

theorem trace_one_fin_two : Matrix.trace (1 : Operator 2) = 2 := by
  rw [Matrix.trace_fin_two]
  norm_num

theorem pauliInverseMap_inverse (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a) :
    Function.LeftInverse (pauliInverseMap p hp) (ensembleMeasurementMap p pauliBasisMatrix) ∧
      Function.RightInverse (pauliInverseMap p hp)
        (ensembleMeasurementMap p pauliBasisMatrix) := by
  constructor
  · intro B
    have htr : Matrix.trace (ensembleMeasurementMap p pauliBasisMatrix B)
        = Matrix.trace B :=
      ensembleMeasurementMap_trace p pauliBasisMatrix pauliBasisMatrix_unitary B
    have key : ∀ a : Fin 3,
        ((p.prob a : ℂ)⁻¹
            * Matrix.trace (pauliMatrix a * ensembleMeasurementMap p pauliBasisMatrix B))
            • pauliMatrix a
      = Matrix.trace (pauliMatrix a * B) • pauliMatrix a := by
      intro a
      have hne : (p.prob a : ℂ) ≠ 0 := fun h =>
        (Complex.ofReal_eq_zero.mp h).symm.not_lt (hp a)
      rw [ensembleMeasurementMap_pauli_apply_pauli, inv_mul_cancel_left₀ hne]
    show (1 / 2 : ℂ) • (Matrix.trace (ensembleMeasurementMap p pauliBasisMatrix B)
          • (1 : Operator 2)
        + ∑ a : Fin 3, ((p.prob a : ℂ)⁻¹
            * Matrix.trace (pauliMatrix a * ensembleMeasurementMap p pauliBasisMatrix B))
            • pauliMatrix a) = B
    rw [htr, Finset.sum_congr rfl fun a _ => key a]
    exact (pauli_expansion B).symm
  · intro B
    have htrNB : Matrix.trace (pauliInverseMap p hp B) = Matrix.trace B := by
      rw [pauliInverseMap, Matrix.trace_smul, Matrix.trace_add]
      have h1 : Matrix.trace (Matrix.trace B • (1 : Operator 2))
          = Matrix.trace B * 2 := by
        rw [Matrix.trace_smul, smul_eq_mul, trace_one_fin_two]
      have h2 : Matrix.trace (∑ a : Fin 3, ((p.prob a : ℂ)⁻¹
            * Matrix.trace (pauliMatrix a * B)) • pauliMatrix a) = 0 := by
        rw [Matrix.trace_sum]
        have hzero : ∀ a : Fin 3,
            Matrix.trace (((p.prob a : ℂ)⁻¹ * Matrix.trace (pauliMatrix a * B))
              • pauliMatrix a) = 0 := by
          intro a
          rw [Matrix.trace_smul, smul_eq_mul, trace_pauliMatrix, mul_zero]
        rw [Finset.sum_congr rfl fun a _ => hzero a, Finset.sum_const_zero]
      rw [h1, h2, smul_eq_mul]
      ring
    have hσNB : ∀ c : Fin 3,
        Matrix.trace (pauliMatrix c * pauliInverseMap p hp B)
          = Matrix.trace (pauliMatrix c * B) / (p.prob c : ℂ) := by
      intro c
      have hne : (p.prob c : ℂ) ≠ 0 := fun h =>
        (Complex.ofReal_eq_zero.mp h).symm.not_lt (hp c)
      have h1 : Matrix.trace (pauliMatrix c * (Matrix.trace B • (1 : Operator 2))) = 0 := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
          trace_pauliMatrix, mul_zero]
      have h2 : Matrix.trace (pauliMatrix c * ∑ a : Fin 3, ((p.prob a : ℂ)⁻¹
            * Matrix.trace (pauliMatrix a * B)) • pauliMatrix a)
          = 2 * ((p.prob c : ℂ)⁻¹ * Matrix.trace (pauliMatrix c * B)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
        have hterm : ∀ a : Fin 3,
            Matrix.trace (pauliMatrix c * (((p.prob a : ℂ)⁻¹
                * Matrix.trace (pauliMatrix a * B)) • pauliMatrix a))
            = if c = a then ((p.prob a : ℂ)⁻¹ * Matrix.trace (pauliMatrix a * B)) * 2
              else 0 := by
          intro a
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_pauliMatrix_mul]
          by_cases hca : c = a
          · rw [if_pos hca, if_pos hca]
          · rw [if_neg hca, if_neg hca, mul_zero]
        rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_eq_single c]
        · rw [if_pos rfl]
          ring
        · intro a _ ha
          rw [if_neg (Ne.symm ha)]
        · intro hc
          exact absurd (Finset.mem_univ c) hc
      rw [pauliInverseMap, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add,
        Matrix.trace_add, h1, zero_add, h2, smul_eq_mul]
      field_simp
    rw [ensembleMeasurementMap_pauli, htrNB]
    have hsumσ : ∑ a : Fin 3, ((p.prob a / 2 : ℂ)
        * Matrix.trace (pauliMatrix a * pauliInverseMap p hp B)) • pauliMatrix a
      = ∑ a : Fin 3, ((p.prob a / 2 : ℂ)
        * (Matrix.trace (pauliMatrix a * B) / (p.prob a : ℂ))) • pauliMatrix a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hσNB a]
    have hcancel : ∀ a : Fin 3,
        ((p.prob a / 2 : ℂ) * (Matrix.trace (pauliMatrix a * B) / (p.prob a : ℂ)))
            • pauliMatrix a
        = ((1 / 2 : ℂ) * Matrix.trace (pauliMatrix a * B)) • pauliMatrix a := by
      intro a
      have hne : (p.prob a : ℂ) ≠ 0 := fun h =>
        (Complex.ofReal_eq_zero.mp h).symm.not_lt (hp a)
      congr 1
      field_simp
    have hcombine : ((1 / 2 : ℂ) * Matrix.trace B) • (1 : Operator 2)
          + ∑ a : Fin 3, ((1 / 2 : ℂ) * Matrix.trace (pauliMatrix a * B)) • pauliMatrix a
        = (1 / 2 : ℂ) • (Matrix.trace B • (1 : Operator 2)
          + ∑ a : Fin 3, Matrix.trace (pauliMatrix a * B) • pauliMatrix a) := by
      rw [smul_add, Finset.smul_sum, smul_smul,
        Finset.sum_congr rfl fun a _ => smul_smul _ _ _]
    rw [hsumσ, Finset.sum_congr rfl fun a _ => hcancel a, hcombine, ← pauli_expansion B]

noncomputable def biasedPauliSnapshot (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (o : Fin 3 × Bool) : Operator 2 :=
  (1 / 2 : ℂ) • (1 : Operator 2)
    + ((if o.2 then 1 else -1 : ℂ) / (2 * (p.prob o.1 : ℂ))) • pauliMatrix o.1

theorem biasedPauliSnapshot_eq (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (a : Fin 3) (b : Bool) :
    biasedPauliSnapshot p hp (a, b)
      = (1 / 2 : ℂ) • (1 : Operator 2)
        + ((if b then 1 else -1 : ℂ) / (2 * (p.prob a : ℂ))) • pauliMatrix a :=
  rfl

theorem trace_biasedSnapshot (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (a : Fin 3) (b : Bool) :
    Matrix.trace (biasedPauliSnapshot p hp (a, b)) = 1 := by
  rw [biasedPauliSnapshot_eq, Matrix.trace_add, Matrix.trace_smul, trace_one_fin_two,
    Matrix.trace_smul, trace_pauliMatrix, smul_zero, add_zero, smul_eq_mul]
  norm_num

theorem trace_pauliMatrix_mul_biasedSnapshot (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (c a : Fin 3) (b : Bool) :
    Matrix.trace (pauliMatrix c * biasedPauliSnapshot p hp (a, b))
      = if c = a then ((if b then 1 else -1 : ℂ) / (p.prob a : ℂ)) else 0 := by
  have hne : (p.prob a : ℂ) ≠ 0 := fun h =>
    (Complex.ofReal_eq_zero.mp h).symm.not_lt (hp a)
  rw [biasedPauliSnapshot_eq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    trace_pauliMatrix, smul_zero, zero_add, trace_pauliMatrix_mul]
  by_cases h : c = a
  · rw [if_pos h, if_pos h, smul_eq_mul]
    field_simp
  · rw [if_neg h, smul_zero, if_neg h]

theorem ensembleMeasurementMap_biasedSnapshot (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (a : Fin 3) (b : Bool) :
    ensembleMeasurementMap p pauliBasisMatrix (biasedPauliSnapshot p hp (a, b))
      = PauliProjector a b := by
  have hne : (p.prob a : ℂ) ≠ 0 := fun h =>
    (Complex.ofReal_eq_zero.mp h).symm.not_lt (hp a)
  rw [ensembleMeasurementMap_pauli,
    trace_biasedSnapshot p hp a b, mul_one, Finset.sum_eq_single a]
  · rw [trace_pauliMatrix_mul_biasedSnapshot p hp a a b, if_pos rfl]
    have hcoeff : (p.prob a / 2 : ℂ) * ((if b then 1 else -1 : ℂ) / (p.prob a : ℂ))
        = (if b then 1 else -1 : ℂ) / 2 := by
      field_simp
    rw [hcoeff]
    simp only [PauliProjector]
    module
  · intro c _ hc
    rw [trace_pauliMatrix_mul_biasedSnapshot p hp c a b, if_neg hc, mul_zero, zero_smul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem biased_pauli_statistic_value (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (o : Fin 3 × Fin 2) :
    (Matrix.trace (pauliZ * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re
      = if o.1 = 2 then
          (if decide (o.2 = 0) then 1 else -1 : ℝ) / p.prob 2 else 0 := by
  have hp2 : p.prob 2 ≠ 0 := ne_of_gt (hp 2)
  rw [show pauliZ = pauliMatrix 2 from rfl,
    trace_pauliMatrix_mul_biasedSnapshot p hp 2 o.1 (decide (o.2 = 0))]
  by_cases h : o.1 = 2
  · rw [h, if_pos (rfl : (2 : Fin 3) = 2), if_pos (rfl : (2 : Fin 3) = 2)]
    by_cases hd : decide (o.2 = 0) = true
    · rw [if_pos hd, if_pos hd]
      norm_num [Complex.div_re, Complex.normSq_ofReal]
    · rw [if_neg hd, if_neg hd]
      norm_num [Complex.div_re, Complex.normSq_ofReal]
      field_simp
  · rw [if_neg (Ne.symm h), if_neg h]
    rfl

theorem pauliProjector_tr_sub (a : Fin 3) (ρ : Operator 2) :
    Matrix.trace (PauliProjector a true * ρ) - Matrix.trace (PauliProjector a false * ρ)
      = Matrix.trace (pauliMatrix a * ρ) := by
  rw [← Matrix.trace_sub, ← Matrix.sub_mul, pauliProjector_sub]

theorem pauliProjector_tr_add (a : Fin 3) (ρ : Operator 2) :
    Matrix.trace (PauliProjector a true * ρ) + Matrix.trace (PauliProjector a false * ρ)
      = Matrix.trace ρ := by
  rw [← Matrix.trace_add, ← Matrix.add_mul,
    show PauliProjector a true + PauliProjector a false = 1 from by
      rw [add_comm, ← sum_bool, ← pauliProjector_sum a],
    Matrix.one_mul]

theorem biased_pauli_z_moments (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).expect
        (fun o => (Matrix.trace (pauliZ
          * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re)
      = (Matrix.trace (pauliZ * ρ)).re ∧
      (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).expect
        (fun o => ((Matrix.trace (pauliZ
          * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re) ^ 2)
      = 1 / p.prob 2 := by
  have hp2 : p.prob 2 ≠ 0 := ne_of_gt (hp 2)
  have hb : ∀ (a : Fin 3) (b : Fin 2),
      (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob (a, b)
        = p.prob a * (Matrix.trace (PauliProjector a (decide (b = 0)) * ρ)).re := by
    intro a b
    rw [(finite_ensemble_actual_kraus_born (Fin 3) 2 p pauliBasisMatrix
      pauliBasisMatrix_unitary).2 ρ hρ (a, b), ensembleProjector_pauliBasis]
  have hz : ∀ (a : Fin 3) (b : Fin 2),
      (Matrix.trace (pauliZ * biasedPauliSnapshot p hp (a, decide (b = 0)))).re
        = if a = 2 then (if decide (b = 0) then (1 : ℝ) else -1) / p.prob 2 else 0 :=
    fun a b => biased_pauli_statistic_value p hp (a, b)
  have hs0 : (Matrix.trace (pauliZ
        * biasedPauliSnapshot p hp (2, decide ((0 : Fin 2) = 0)))).re
      = 1 / p.prob 2 := by
    rw [hz 2 0, if_pos rfl,
      if_pos (by decide : decide ((0 : Fin 2) = 0) = true)]
  have hs1 : (Matrix.trace (pauliZ
        * biasedPauliSnapshot p hp (2, decide ((1 : Fin 2) = 0)))).re
      = -1 / p.prob 2 := by
    rw [hz 2 1, if_pos rfl,
      if_neg (by decide : ¬ decide ((1 : Fin 2) = 0) = true)]
  have hp0 : (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob
        (2, (0 : Fin 2))
      = p.prob 2 * (Matrix.trace (PauliProjector 2 true * ρ)).re := by
    rw [hb 2 0]
    rfl
  have hp1 : (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob
        (2, (1 : Fin 2))
      = p.prob 2 * (Matrix.trace (PauliProjector 2 false * ρ)).re := by
    rw [hb 2 1]
    rfl
  have hsub : (Matrix.trace (pauliMatrix 2 * ρ)).re
      = (Matrix.trace (PauliProjector 2 true * ρ)).re
        - (Matrix.trace (PauliProjector 2 false * ρ)).re := by
    rw [← Complex.sub_re, ← pauliProjector_tr_sub]
  have hadd : (Matrix.trace ρ).re
      = (Matrix.trace (PauliProjector 2 true * ρ)).re
        + (Matrix.trace (PauliProjector 2 false * ρ)).re := by
    rw [← Complex.add_re, ← pauliProjector_tr_add]
  constructor
  · show ∑ o : Fin 3 × Fin 2,
        (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob o
          * (Matrix.trace (pauliZ
              * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re = _
    rw [Fintype.sum_prod_type' (fun a b =>
        (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob (a, b)
          * (Matrix.trace (pauliZ
              * biasedPauliSnapshot p hp (a, decide (b = 0)))).re),
      Finset.sum_eq_single (2 : Fin 3)]
    · rw [Fin.sum_univ_two, hp0, hp1, hs0, hs1,
        show pauliZ = pauliMatrix 2 from rfl, hsub]
      field_simp
      ring
    · intro a _ ha
      rw [Finset.sum_congr rfl fun b _ => by rw [hz a b, if_neg ha, mul_zero],
        Finset.sum_const_zero]
    · intro h2
      exact absurd (Finset.mem_univ 2) h2
  · show ∑ o : Fin 3 × Fin 2,
        (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob o
          * ((Matrix.trace (pauliZ
              * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re) ^ 2 = _
    rw [Fintype.sum_prod_type' (fun a b =>
        (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).prob (a, b)
          * ((Matrix.trace (pauliZ
              * biasedPauliSnapshot p hp (a, decide (b = 0)))).re) ^ 2),
      Finset.sum_eq_single (2 : Fin 3)]
    · rw [Fin.sum_univ_two, hp0, hp1, hs0, hs1]
      have hu : (Matrix.trace (PauliProjector 2 true * ρ)).re
          + (Matrix.trace (PauliProjector 2 false * ρ)).re = 1 := by
        rw [← hadd, hρ.2, Complex.one_re]
      have hsq : (-1 : ℝ) / p.prob 2 = -(1 / p.prob 2) := by ring
      rw [hsq, neg_sq, ← add_mul, ← mul_add, hu, mul_one]
      field_simp
    · intro a _ ha
      rw [Finset.sum_congr rfl fun b _ => by
          rw [hz a b, if_neg ha, zero_pow two_ne_zero, mul_zero],
        Finset.sum_const_zero]
    · intro h2
      exact absurd (Finset.mem_univ 2) h2

theorem biased_pauli_inverse_and_real_consumer (p : FinDist (Fin 3))
    (hp : ∀ a, 0 < p.prob a) :
    Function.Bijective (ensembleMeasurementMap p pauliBasisMatrix) ∧
      (∀ (hM : Function.Bijective (ensembleMeasurementMap p pauliBasisMatrix))
        (o : Fin 3 × Fin 2),
        ensembleSnapshot p pauliBasisMatrix hM o
          = biasedPauliSnapshot p hp (o.1, decide (o.2 = 0))) ∧
      (∀ (a : Fin 3) (b : Bool),
        biasedPauliSnapshot p hp (a, b)
          = (1 / 2 : ℂ) • (1 : Operator 2)
            + ((if b then 1 else -1 : ℂ) / (2 * (p.prob a : ℂ))) • pauliMatrix a) ∧
      (∀ (ρ : Operator 2) (hρ : IsDensityOperator ρ),
        (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).variance
          (fun o => (Matrix.trace (pauliZ
            * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re)
          = 1 / p.prob 2 - (Matrix.trace (pauliZ * ρ)).re ^ 2) := by
  obtain ⟨hli, hri⟩ := pauliInverseMap_inverse p hp
  refine ⟨⟨hli.injective, hri.surjective⟩, ?_, fun a b => rfl, ?_⟩
  · intro hM o
    apply hM.1
    rw [ensembleMeasurementMap_snapshot p pauliBasisMatrix hM o,
      ensembleMeasurementMap_biasedSnapshot p hp o.1 (decide (o.2 = 0))]
    exact ensembleProjector_pauliBasis o.1 o.2
  · intro ρ hρ
    obtain ⟨hmean, hsecond⟩ := biased_pauli_z_moments p hp ρ hρ
    rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance_eq_expect_sq_sub
      (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ)
      (fun o => (Matrix.trace (pauliZ
        * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re), hsecond, hmean]

noncomputable def biasedPauliAxisWeights : FinDist (Fin 3) where
  prob a := if a = 0 then 1 / 2 else if a = 1 then 1 / 3 else 1 / 6
  nonneg a := by
    by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;> simp [h0, h1]
  sum_one := by
    simp [Fin.sum_univ_three]
    norm_num

theorem biasedPauliAxisWeights_prob (a : Fin 3) :
    biasedPauliAxisWeights.prob a
      = if a = 0 then 1 / 2 else if a = 1 then 1 / 3 else 1 / 6 := rfl

theorem biasedPauliAxisWeights_pos : ∀ a, 0 < biasedPauliAxisWeights.prob a := by
  intro a
  rw [biasedPauliAxisWeights_prob]
  by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;> simp [h0, h1]

theorem biased_pauli_z_actual_variance_six_consumer :
    biasedPauliAxisWeights.prob 0 = 1 / 2 ∧ biasedPauliAxisWeights.prob 1 = 1 / 3 ∧
      biasedPauliAxisWeights.prob 2 = 1 / 6 ∧
      ∀ (ρ : Operator 2) (hρ : IsDensityOperator ρ),
        ρ = (1 / 2 : ℂ) • (1 : Operator 2) →
          (ensembleRecordLaw biasedPauliAxisWeights pauliBasisMatrix
              pauliBasisMatrix_unitary ρ hρ).variance
              (fun o => (Matrix.trace (pauliZ * biasedPauliSnapshot biasedPauliAxisWeights
                biasedPauliAxisWeights_pos (o.1, decide (o.2 = 0)))).re) = 6 := by
  refine ⟨by simp [biasedPauliAxisWeights_prob], by simp [biasedPauliAxisWeights_prob],
    by simp [biasedPauliAxisWeights_prob], ?_⟩
  intro ρ hρ hρmix
  have hvar := (biased_pauli_inverse_and_real_consumer biasedPauliAxisWeights
    biasedPauliAxisWeights_pos).2.2.2 ρ hρ
  have htrZ : Matrix.trace (pauliZ * ρ) = 0 := by
    rw [hρmix, Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul,
      show pauliZ = pauliMatrix 2 from rfl, trace_pauliMatrix, mul_zero]
  have hw : biasedPauliAxisWeights.prob 2 = 1 / 6 := by
    simp [biasedPauliAxisWeights_prob]
  rw [hvar, hw, htrZ, Complex.zero_re, zero_pow (by norm_num), sub_zero]
  norm_num

theorem biased_pauli_fresh_records_are_ensemble_leaves (m : ℕ) (axes : Fin m → Fin 3) :
    pauliFreshResourceCounts axes = (m, 2 * m, m, 0) ∧
      ∀ i : Fin m, ∀ b : Bool,
        (observedLeaf 1 (pauliAxisProgram (axes i))
          (pauliLeafIndex (axes i) b)).operator
          = ensembleProjector pauliBasisMatrix (axes i, if b then 0 else 1) := by
  refine ⟨pauli_fresh_actual_resources axes, fun i b => ?_⟩
  rw [(pauli_axis_actual_leaf (axes i) b).1, ensembleProjector_pauliBasis]
  cases b <;> rfl

theorem biased_pauli_variance_le_effect (p : FinDist (Fin 3)) (hp : ∀ a, 0 < p.prob a)
    (hM : Function.Bijective (ensembleMeasurementMap p pauliBasisMatrix)) (ρ : Operator 2)
    (hρ : IsDensityOperator ρ) :
    (ensembleRecordLaw p pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).variance
        (fun o => (Matrix.trace (pauliZ
          * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re)
      ≤ ‖ensembleMomentEffect p pauliBasisMatrix hM pauliZ‖ := by
  have hZherm : pauliZ.IsHermitian := pauliMatrix_conjTranspose 2
  have hG4 := (finite_ensemble_computed_variance_bound (Fin 3) 2 p pauliBasisMatrix
    pauliBasisMatrix_unitary hM ρ pauliZ hρ hZherm).2
  have htrZ : Matrix.trace pauliZ = 0 := trace_pauliMatrix 2
  have hcenter : pauliZ - (Matrix.trace pauliZ / ((2 : ℕ) : ℂ)) • (1 : Operator 2)
      = pauliZ := by
    rw [htrZ, zero_div, zero_smul, sub_zero]
  rw [hcenter] at hG4
  have hfun : ensembleStatistic p pauliBasisMatrix hM pauliZ
      = fun o : Fin 3 × Fin 2 =>
        (Matrix.trace (pauliZ
          * biasedPauliSnapshot p hp (o.1, decide (o.2 = 0)))).re := by
    funext o
    rw [ensembleStatistic,
      (biased_pauli_inverse_and_real_consumer p hp).2.1 hM o]
  rw [hfun] at hG4
  exact hG4

theorem biased_pauli_variance_six_and_actual_work (ρ : Operator 2)
    (hρ : IsDensityOperator ρ) (hmix : ρ = (1/2 : ℂ) • (1 : Operator 2))
    {m : ℕ} (ω : Fin m → Fin 3 × Fin 2) :
    let hM :=
        (biased_pauli_inverse_and_real_consumer biasedPauliAxisWeights biasedPauliAxisWeights_pos).1
    (ensembleRecordLaw biasedPauliAxisWeights pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).variance
      (ensembleStatistic biasedPauliAxisWeights pauliBasisMatrix hM pauliZ) = 6 ∧
    (ensembleRecordLaw biasedPauliAxisWeights pauliBasisMatrix pauliBasisMatrix_unitary ρ hρ).variance
      (ensembleStatistic biasedPauliAxisWeights pauliBasisMatrix hM pauliZ) ≤
      ‖ensembleMomentEffect biasedPauliAxisWeights pauliBasisMatrix hM pauliZ‖ ∧
    ensembleFreshResourceCounts pauliBasisMatrix ω = (m,2*m,m,0) := by
  (try dsimp only)
  have hf : ensembleStatistic biasedPauliAxisWeights pauliBasisMatrix
      (biased_pauli_inverse_and_real_consumer biasedPauliAxisWeights biasedPauliAxisWeights_pos).1 pauliZ =
      fun o => (Matrix.trace (pauliZ * biasedPauliSnapshot biasedPauliAxisWeights
        biasedPauliAxisWeights_pos (o.1,decide (o.2=0)))).re := by
    funext o
    rw [ensembleStatistic, (biased_pauli_inverse_and_real_consumer biasedPauliAxisWeights
      biasedPauliAxisWeights_pos).2.1]
  rw [hf]
  exact ⟨biased_pauli_z_actual_variance_six_consumer.2.2.2 ρ hρ hmix,
    biased_pauli_variance_le_effect biasedPauliAxisWeights biasedPauliAxisWeights_pos _ ρ hρ,
    ensembleFreshResourceCounts_spec pauliBasisMatrix ω⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision
