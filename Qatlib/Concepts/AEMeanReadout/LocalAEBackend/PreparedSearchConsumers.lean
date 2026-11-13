/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch

/-!
# Concrete consumers of prepared quantum search

This module instantiates prepared amplitude amplification with a two-dimensional preparation
whose marked probability is one quarter and whose marked amplitude carries an arbitrary unit
complex phase. The examples make the amplification and sampling guarantees of [BrassardEtAl2002]
explicit at the level of executed states, success probabilities, and resource counts.

## Main statements

* `prepared_search_quarter_mass_consumer`: obtain the marked basis state, up to its unit phase,
  after one amplification query.
* `prepared_search_bit_sampled_consumer`: compute exact success mass and expected resources for
  a bit-sampled search instance.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped ENNReal Classical

/-- The two-dimensional rotation preparation composed with a diagonal phase on the marked basis
vector. -/
noncomputable def preparedQuarterA (ζ : ℂ) : Operator 2 :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else ζ) *
    ((!![((Real.sqrt 3 / 2 : ℝ) : ℂ), -(1/2 : ℂ); (1/2 : ℂ), ((Real.sqrt 3 / 2 : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

/-- The real two-dimensional rotation with cosine `√3/2` and sine `1/2`, viewed as a complex
matrix, is unitary. -/
private theorem rotation_unitary :
    (!![((Real.sqrt 3 / 2 : ℝ) : ℂ), -(1/2 : ℂ); (1/2 : ℂ), ((Real.sqrt 3 / 2 : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)
      ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h3 : (0:ℝ) ≤ 3 := by norm_num
  have hsqR : (Real.sqrt 3 / 2 : ℝ) * (Real.sqrt 3 / 2 : ℝ) = 3/4 := by
    rw [← sq, div_pow, Real.sq_sqrt h3]
    norm_num
  have haa : (((Real.sqrt 3 / 2 : ℝ) : ℂ)) * (((Real.sqrt 3 / 2 : ℝ) : ℂ)) = 3/4 := by
    rw [← Complex.ofReal_mul, hsqR]
    norm_num
  have hc12 : (starRingEnd ℂ) ((1/2 : ℂ)) = (1/2 : ℂ) := by
    rw [map_div₀ (starRingEnd ℂ), map_one, map_ofNat (starRingEnd ℂ) 2]
  have hcm : (starRingEnd ℂ) (-(1/2 : ℂ)) = -(1/2 : ℂ) := by
    rw [map_neg, hc12]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    show ((starRingEnd ℂ) (((Real.sqrt 3 / 2 : ℝ) : ℂ))) * (((Real.sqrt 3 / 2 : ℝ) : ℂ)) +
        ((starRingEnd ℂ) ((1/2 : ℂ))) * ((1/2 : ℂ)) = 1
    rw [Complex.conj_ofReal, haa, hc12]
    norm_num
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    show ((starRingEnd ℂ) (((Real.sqrt 3 / 2 : ℝ) : ℂ))) * (-(1/2 : ℂ)) +
        ((starRingEnd ℂ) ((1/2 : ℂ))) * (((Real.sqrt 3 / 2 : ℝ) : ℂ)) = 0
    rw [Complex.conj_ofReal, hc12]
    ring
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    show ((starRingEnd ℂ) (-(1/2 : ℂ))) * (((Real.sqrt 3 / 2 : ℝ) : ℂ)) +
        ((starRingEnd ℂ) (((Real.sqrt 3 / 2 : ℝ) : ℂ))) * ((1/2 : ℂ)) = 0
    rw [Complex.conj_ofReal, hcm]
    ring
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    show ((starRingEnd ℂ) (-(1/2 : ℂ))) * (-(1/2 : ℂ)) +
        ((starRingEnd ℂ) (((Real.sqrt 3 / 2 : ℝ) : ℂ))) * (((Real.sqrt 3 / 2 : ℝ) : ℂ)) = 1
    rw [Complex.conj_ofReal, hcm, haa]
    norm_num

/-- A two-dimensional diagonal matrix with entries one and a unit complex number `ζ` is unitary. -/
private theorem diagonal_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else ζ)
      ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    fin_cases i
    · simp
    · have hzz : (starRingEnd ℂ) ζ * ζ = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ, sq]
        norm_num
      simp [hzz]
  · simp [hij]

/-- The quarter-probability preparation is unitary when its phase parameter has norm one. -/
private theorem preparedQuarterA_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    preparedQuarterA ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (diagonal_unitary hζ) rotation_unitary

/-- The amplitude of basis label one in the prepared quarter-probability state equals `ζ / 2`. -/
private theorem preparedAAState_quarter_one (ζ : ℂ) :
    (preparedAAState (preparedQuarterA ζ) (0 : Fin 2)) 1 = ζ * (1/2 : ℂ) := by
  show (∑ j : Fin 2, (Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else ζ) *
      (!![((Real.sqrt 3 / 2 : ℝ) : ℂ), -(1/2 : ℂ); (1/2 : ℂ), ((Real.sqrt 3 / 2 : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)) 1 j * Ket (0 : Fin 2) j) = _
  rw [Fin.sum_univ_two]
  simp [Ket, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, Fin.isValue]

/-- For unit `ζ`, the preparation has marked mass `1/4`, and one prepared amplification step
returns `ζ • Ket 1` using one query and four gates [BrassardEtAl2002]. -/
theorem prepared_search_quarter_mass_consumer :
    ∀ ζ : ℂ, ‖ζ‖=1 →
    preparedQuarterA ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    MeasureProb (preparedAAState (preparedQuarterA ζ) 0) {1} = 1/4 ∧
    Run (preparedMark ({1} : Finset (Fin 2))) (preparedAACircuit (preparedQuarterA ζ) 0 1) (Ket (0 : Fin 2)) = ζ • Ket (1 : Fin 2) ∧
    QueryCount (preparedAACircuit (preparedQuarterA ζ) 0 1) = 1 ∧
    GateCount (preparedAACircuit (preparedQuarterA ζ) 0 1) = 4 := by
  intro ζ hζ
  have hA : preparedQuarterA ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ := preparedQuarterA_unitary hζ
  have hpsi1 : (preparedAAState (preparedQuarterA ζ) (0 : Fin 2)) 1 = ζ * (1/2 : ℂ) :=
    preparedAAState_quarter_one ζ
  have hmass : MeasureProb (preparedAAState (preparedQuarterA ζ) 0) {1} = 1/4 := by
    have h1 : MeasureProb (preparedAAState (preparedQuarterA ζ) 0) {1}
        = BornProb (preparedAAState (preparedQuarterA ζ) 0) 1 := by
      simp [MeasureProb]
    rw [h1, BornProb, hpsi1, norm_mul, mul_pow]
    rw [show ‖ζ‖ ^ 2 = 1 by rw [hζ]; norm_num]
    norm_num
  refine ⟨hA, hmass, ?_, ?_, ?_⟩
  · have hθ0 : (0:ℝ) < Real.pi / 6 := by positivity
    have hθ1 : Real.pi / 6 < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 6) (by positivity : (0:ℝ) < 2)]
      linarith [Real.pi_pos]
    have hprob : MeasureProb (preparedAAState (preparedQuarterA ζ) 0) {1}
        = (Real.sin (Real.pi / 6))^2 := by
      rw [hmass, Real.sin_pi_div_six]
      norm_num
    have hrun := prepared_aa_actual_rotation (preparedQuarterA ζ) (0 : Fin 2)
      ({1} : Finset (Fin 2)) (Real.pi / 6) 1 hA hθ0 hθ1 hprob
    have hang : (2*((1:ℕ):ℝ)+1)*(Real.pi/6) = Real.pi/2 := by
      field_simp
      ring
    have hc0 : (((Real.cos (Real.pi/2)) / Real.cos (Real.pi/6) : ℝ) : ℂ) = 0 := by
      rw [Real.cos_pi_div_two, zero_div, Complex.ofReal_zero]
    have hc2 : (((Real.sin (Real.pi/2)) / Real.sin (Real.pi/6) : ℝ) : ℂ) = 2 := by
      rw [Real.sin_pi_div_two, Real.sin_pi_div_six,
        show ((1:ℝ) / ((1/2:ℝ))) = 2 from by norm_num]
      norm_num
    rw [hang, hc0, hc2, zero_smul, zero_add] at hrun
    have hcol : Collapse (preparedAAState (preparedQuarterA ζ) 0) ({1} : Finset (Fin 2))
        = fun i => if i = 1 then ζ * (1/2 : ℂ) else 0 := by
      funext i
      rw [collapse_apply]
      by_cases h : i = 1 <;> simp [h, hpsi1]
    rw [hrun, hcol]
    funext i
    fin_cases i
    all_goals simp [Ket]
    all_goals (norm_num; ring)
  · exact (prepared_aa_actual_circuit (preparedQuarterA ζ) (0 : Fin 2)
      ({1} : Finset (Fin 2)) 1 hA).2.1
  · have hgc := (prepared_aa_actual_circuit (preparedQuarterA ζ) (0 : Fin 2)
      ({1} : Finset (Fin 2)) 1 hA).2.2.1
    rw [hgc]

/-- Evaluate `(15/16) / 3 * (3/2)` as `15/32` in the extended nonnegative reals. -/
private theorem num_event_fin :
    (((15/16 : ℝ≥0∞)) / (((3:ℕ):ℝ≥0∞))) * ((3/2 : ℝ≥0∞)) = 15/32 := by
  rw [show ((15/16:ℝ≥0∞)) = ENNReal.ofReal ((15/16:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num,
    show ((15/32:ℝ≥0∞)) = ENNReal.ofReal ((15/32:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 32)]
      norm_num,
    show ((3/2:ℝ≥0∞)) = ENNReal.ofReal ((3/2:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num,
    show (((3:ℕ):ℝ≥0∞)) = ENNReal.ofReal ((3:ℝ)) from by norm_num,
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 15/16/3)]
  congr 1
  norm_num

/-- Evaluate `2 * (1 + 1/4)` as `5/2` in the extended nonnegative reals. -/
private theorem num_bits_fin :
    (((2:ℕ):ℝ≥0∞)) * (1 + ((1/4:ℝ≥0∞))) = 5/2 := by
  rw [show ((1/4:ℝ≥0∞)) = ENNReal.ofReal ((1/4:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
      norm_num,
    show ((5/2:ℝ≥0∞)) = ENNReal.ofReal ((5/2:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num,
    show ((2:ℕ):ℝ≥0∞) = ENNReal.ofReal ((2:ℝ)) from by norm_num,
    show ((1:ℝ≥0∞)) = ENNReal.ofReal ((1:ℝ)) from by norm_num,
    ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1/4),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  norm_num

/-- The extended nonnegative real quotient of two by itself is one. -/
private theorem num_div_two_self : (((2:ℝ≥0∞)) / (((2:ℝ≥0∞)))) = 1 := by
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel (by norm_num : ((2:ℝ≥0∞)) ≠ 0)
    (by norm_num : ((2:ℝ≥0∞)) ≠ ⊤)]

/-- Evaluate `(15/16) * (2/2)` as `15/16` in the extended nonnegative reals. -/
private theorem num_query_fin :
    ((15/16:ℝ≥0∞)) * (((2:ℝ≥0∞)) / ((2:ℝ≥0∞))) = ((15/16:ℝ≥0∞)) := by
  rw [num_div_two_self, mul_one]

/-- Evaluate `(15/16) * (3 * (2/2) + 1)` as `15/4` in the extended nonnegative reals. -/
private theorem num_gates_fin :
    ((15/16:ℝ≥0∞)) * (((3:ℝ≥0∞)) * (((2:ℝ≥0∞)) / ((2:ℝ≥0∞))) + ((1:ℝ≥0∞))) = 15/4 := by
  rw [num_div_two_self,
    show ((3:ℝ≥0∞)) * ((1:ℝ≥0∞)) + ((1:ℝ≥0∞)) = ((4:ℝ≥0∞)) from by norm_num,
    show ((15/16:ℝ≥0∞)) = ENNReal.ofReal ((15/16:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num,
    show ((15/4:ℝ≥0∞)) = ENNReal.ofReal ((15/4:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
      norm_num,
    show ((4:ℝ≥0∞)) = ENNReal.ofReal ((4:ℝ)) from by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 15/16)]
  congr 1
  norm_num

/-- For the stated quarter-probability sampled search, success mass is `15/32`, expected
sampled-bit and query counts are `5/2` and `15/16`, and expected returned gate count is
`15/4`. -/
theorem prepared_search_bit_sampled_consumer :
    ∀ (ζ : ℂ) (_hζ : ‖ζ‖=1) (hA : preparedQuarterA ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ),
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (preparedQuarterA ζ) hA 0 {1} 2 3 2)
    (fun x => ∃ y gates, x.1=some (y,gates) ∧ y ∈ ({1} : Finset (Fin 2))) = 15/32 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (preparedQuarterA ζ) hA 0 {1} 2 3 2) (fun x => (x.2.1 : ℝ≥0∞)) = 5/2 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (preparedQuarterA ζ) hA 0 {1} 2 3 2) (fun x => (x.2.2 : ℝ≥0∞)) = 15/16 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (preparedQuarterA ζ) hA 0 {1} 2 3 2)
    (fun x => ((match x.1 with | none => 0 | some y => y.2 : ℕ) : ℝ≥0∞)) = 15/4 := by
  intro ζ hζ hA
  have hq : coinRejectMass 2 3 = 1/4 := by
    norm_num [coinRejectMass]
  have hq2 : coinRejectMass 2 3 ^ 2 = 1/16 := by
    rw [hq]
    have e1 : ((1/4 : ℝ≥0∞)) = ((4:ℝ≥0∞))⁻¹ := by
      rw [show ((1/4 : ℝ≥0∞)) = ((4:ℝ≥0∞))⁻¹ * 1 from
        ENNReal.div_eq_inv_mul (a := (1:ℝ≥0∞)) (b := (4:ℝ≥0∞)), mul_one]
    have e2 : ((1/16 : ℝ≥0∞)) = ((16:ℝ≥0∞))⁻¹ := by
      rw [show ((1/16 : ℝ≥0∞)) = ((16:ℝ≥0∞))⁻¹ * 1 from
        ENNReal.div_eq_inv_mul (a := (1:ℝ≥0∞)) (b := (16:ℝ≥0∞)), mul_one]
    rw [e1, e2, ← ENNReal.inv_pow]
    norm_num
  have h1 : 1 - coinRejectMass 2 3 ^ 2 = 15/16 := by
    have hsum : (15/16 : ℝ≥0∞) + (1/16 : ℝ≥0∞) = 1 := by
      have e1 : ((15/16 : ℝ≥0∞)) = ((16:ℝ≥0∞))⁻¹ * 15 :=
        ENNReal.div_eq_inv_mul (a := (15:ℝ≥0∞)) (b := (16:ℝ≥0∞))
      have e2 : ((1/16 : ℝ≥0∞)) = ((16:ℝ≥0∞))⁻¹ * 1 :=
        ENNReal.div_eq_inv_mul (a := (1:ℝ≥0∞)) (b := (16:ℝ≥0∞))
      rw [e1, e2, ← mul_add]
      norm_num
      rw [mul_comm]
      exact ENNReal.mul_inv_cancel (show ((16:ℝ≥0∞)) ≠ 0 by norm_num)
        (show ((16:ℝ≥0∞)) ≠ ⊤ by norm_num)
    have htop : ((1/16 : ℝ≥0∞)) ≠ ⊤ := by
      rw [show ((1/16 : ℝ≥0∞)) = ((16:ℝ≥0∞))⁻¹ from by
        rw [ENNReal.div_eq_inv_mul (a := (1:ℝ≥0∞)) (b := (16:ℝ≥0∞)), mul_one]]
      exact ENNReal.inv_ne_top.mpr (show ((16:ℝ≥0∞)) ≠ 0 by norm_num)
    rw [hq2]
    calc (1:ℝ≥0∞) - 1/16 = 15/16 + 1/16 - 1/16 := by rw [hsum]
      _ = 15/16 := ENNReal.add_sub_cancel_right htop
  have hmass : MeasureProb (preparedAAState (preparedQuarterA ζ) (0 : Fin 2)) {1} = 1/4 :=
    (prepared_search_quarter_mass_consumer ζ hζ).2.1
  have hrun1 : Run (preparedMark ({1} : Finset (Fin 2)))
      (preparedAACircuit (preparedQuarterA ζ) 0 1) (Ket (0 : Fin 2)) = ζ • Ket (1 : Fin 2) :=
    (prepared_search_quarter_mass_consumer ζ hζ).2.2.1
  have hp0 : MeasureProb (Run (preparedMark ({1} : Finset (Fin 2)))
      (preparedAACircuit (preparedQuarterA ζ) 0 0) (Ket (0 : Fin 2))) {1} = 1/4 := by
    rw [(prepared_aa_actual_circuit (preparedQuarterA ζ) (0 : Fin 2)
      ({1} : Finset (Fin 2)) 0 hA).2.2.2]
    show MeasureProb (ApplyGate 1 (preparedAAState (preparedQuarterA ζ) 0)) {1} = _
    rw [applyGate_one]
    exact hmass
  have hp1 : MeasureProb (Run (preparedMark ({1} : Finset (Fin 2)))
      (preparedAACircuit (preparedQuarterA ζ) 0 1) (Ket (0 : Fin 2))) {1} = 1 := by
    rw [hrun1, measureProb_smul]
    rw [show ‖ζ‖ ^ 2 = 1 by rw [hζ]; norm_num, one_mul]
    have : MeasureProb (Ket (1 : Fin 2)) ({1} : Finset (Fin 2)) = 1 := by
      simp [MeasureProb, BornProb]
    rw [this]
  have hp2 : MeasureProb (Run (preparedMark ({1} : Finset (Fin 2)))
      (preparedAACircuit (preparedQuarterA ζ) 0 2) (Ket (0 : Fin 2))) {1} = 1/4 := by
    have hθ0 : (0:ℝ) < Real.pi / 6 := by positivity
    have hθ1 : Real.pi / 6 < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 6) (by positivity : (0:ℝ) < 2)]
      linarith [Real.pi_pos]
    have hprob : MeasureProb (preparedAAState (preparedQuarterA ζ) 0) {1}
        = (Real.sin (Real.pi / 6))^2 := by
      rw [hmass, Real.sin_pi_div_six]
      norm_num
    rw [prepared_aa_born_success (preparedQuarterA ζ) (0 : Fin 2)
      ({1} : Finset (Fin 2)) (Real.pi / 6) 2 hA hθ0 hθ1 hprob]
    have hang : (2*((2:ℕ):ℝ)+1)*(Real.pi/6) = Real.pi - Real.pi/6 := by
      field_simp
      ring
    rw [hang, Real.sin_pi_sub, Real.sin_pi_div_six]
    norm_num
  have hsum : ∑ i : Fin 3, ENNReal.ofReal (MeasureProb
      (Run (preparedMark ({1} : Finset (Fin 2)))
        (preparedAACircuit (preparedQuarterA ζ) 0 i.val) (Ket (0 : Fin 2))) {1})
      = 3/2 := by
    rw [Fin.sum_univ_three]
    have e0 : (((0 : Fin 3) : ℕ)) = 0 := rfl
    have e1 : (((1 : Fin 3) : ℕ)) = 1 := rfl
    have e2 : (((2 : Fin 3) : ℕ)) = 2 := rfl
    rw [e0, e1, e2]
    rw [hp0, hp1, hp2,
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (0:ℝ) ≤ 1),
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/4 + 1) (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [show ((1/4:ℝ) + 1 + 1/4) = 3/2 from by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hE := prepared_aa_sampled_success (preparedQuarterA ζ) (0 : Fin 2)
    ({1} : Finset (Fin 2)) hA 2 3 2 (by norm_num : 0 < 3) (by norm_num : 3 ≤ 2 ^ 2)
  have hL := prepared_aa_sampled_three_ledgers (preparedQuarterA ζ) (0 : Fin 2)
    ({1} : Finset (Fin 2)) hA 2 3 2 (by norm_num : 0 < 3) (by norm_num : 3 ≤ 2 ^ 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE, hsum, h1, num_event_fin]

  · rw [hL.1, (finite_coin_actual_bit_cost 2 3 2 (by norm_num : 3 ≤ 2 ^ 2)).2, hq]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
      pow_one, zero_add]
    exact num_bits_fin

  · rw [hL.2.1, h1, show (((3-1 : ℕ) : ℝ≥0∞)) = ((2 : ℝ≥0∞)) from by norm_num,
      mul_div_assoc, num_query_fin]

  · have hstep : (1-(coinRejectMass 2 3)^2)*(3*((3-1:ℕ):ℝ≥0∞)/2+1) = 15/4 := by
      rw [h1, show (((3-1:ℕ):ℝ≥0∞)) = ((2 : ℝ≥0∞)) from by norm_num, mul_div_assoc,
        num_gates_fin]
    refine (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr ?hc).trans
        (Eq.trans hL.2.2 hstep)
    intro x
    cases hx : x.1 <;> simp

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
