/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.GridHHLSolutionOutput

/-!
# Finite grid HHL examples

This module evaluates finite grid HHL circuits on two dimensional inputs. It computes the
pseudoinverse response, success probability, normalized output, and gate count for a two
eigenvalue example and for an inconsistent rank one system. The mathematical background is
developed in [HarrowHassidimLloyd2009].

## Main statements

* `grid_hhl_two_eigenvalue_actual_consumer`: success probability `5 / 8`, the explicit solution
  state, and seven gates.
* `gridHHL_recovers_projected_system`: pseudoinversion recovers the range projection of the
  right hand side.
* `grid_hhl_low_rank_inconsistent_actual_consumer`: the rank one inconsistent example with
  probability `1 / 2`.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix
open scoped Classical
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The two eigenvalue labels one and two in a four point grid. -/
noncomputable def gridHHLLabel2 : Fin 2 → Fin 4 := fun i => if i = 0 then 1 else 2

/-- The equal superposition of the two coordinate basis states, scaled by `√2` inverse. -/
noncomputable def gridHHLb2 : QState (Fin 2) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (Ket (0 : Fin 2) + Ket (1 : Fin 2))

/-- The grid pseudoinverse sends the equal superposition to `√2` inverse times the vector with
coordinates four and two. -/
theorem gridHHLb2_pseudoinverse (hM : 0 < (4 : ℕ)) :
    matrixPseudoinverse (gridHHLMatrix gridHHLLabel2 (1 : Operator 2)) *ᵥ gridHHLb2
      = (Real.sqrt 2 : ℂ)⁻¹ • ((4 : ℂ) • Ket (0 : Fin 2) + (2 : ℂ) • Ket (1 : Fin 2)) := by
  have hV : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, one_conjTranspose]
    simp
  rw [← grid_hhl_spectral_reciprocal_eq_pseudoinverse hM gridHHLLabel2 _ hV,
    gridHHLReciprocal_mulVec hM gridHHLLabel2 _ gridHHLb2, Fin.sum_univ_two]
  have hone : (1 : Operator 2)ᴴ *ᵥ gridHHLb2 = gridHHLb2 := by
    rw [one_conjTranspose, Matrix.one_mulVec]
  have hket : ∀ i : Fin 2, (1 : Operator 2) *ᵥ Ket i = Ket i :=
    fun i => Matrix.one_mulVec _
  have hb0 : gridHHLb2 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
    simp [gridHHLb2, Pi.add_apply, Ket]
  have hb1 : gridHHLb2 1 = (Real.sqrt 2 : ℂ)⁻¹ := by
    simp [gridHHLb2, Pi.add_apply, Ket]
  have hs0 : gridHHLReciprocalScale 4 gridHHLLabel2 0 = 4 := by
    simp [gridHHLReciprocalScale, gridHHLLabel2]
  have hs1 : gridHHLReciprocalScale 4 gridHHLLabel2 1 = 2 := by
    simp [gridHHLReciprocalScale, gridHHLLabel2]
    norm_num
  rw [hone, hket 0, hket 1, hb0, hb1, hs0, hs1]
  funext q
  match q with
  | 0 => simp [Ket]
  | 1 => simp [Ket]

/-- The total measurement weight of the vector with coordinates four and two is twenty. -/
theorem gridHHLb2_block_measure :
    MeasureProb ((4 : ℂ) • Ket (0 : Fin 2) + (2 : ℂ) • Ket (1 : Fin 2))
      Finset.univ = 20 := by
  unfold MeasureProb BornProb
  rw [Fin.sum_univ_two]
  simp [smul_def', Pi.add_apply, Ket]
  ring_nf

/-- The total measurement weight of the inverse response to the equal superposition is ten. -/
theorem gridHHLb2_successBlock_measure :
    MeasureProb ((Real.sqrt 2 : ℂ)⁻¹
      • ((4 : ℂ) • Ket (0 : Fin 2) + (2 : ℂ) • Ket (1 : Fin 2))) Finset.univ = 10 := by
  rw [measureProb_smul]
  norm_num [gridHHLb2_block_measure, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The two eigenvalue grid HHL example with scale `1 / 4` succeeds with probability `5 / 8`. -/
theorem gridHHLb2_probability :
    gridHHLProbability gridHHLLabel2 (1 : Operator 2) (1 / 4) gridHHLb2 = 5 / 8 := by
  have hV : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, one_conjTranspose]
    simp
  rw [(grid_hhl_actual_probability_and_output gridHHLLabel2 _ (1 / 4) gridHHLb2
    (by norm_num) hV (by norm_num) (by norm_num)).1,
    gridHHLb2_pseudoinverse (by norm_num), gridHHLb2_successBlock_measure]
  norm_num

/-- The product `√10 * √2` equals `2 * √5`. -/
theorem gridHHLb2_sqrt_key : (Real.sqrt 10 : ℝ) * Real.sqrt 2 = 2 * Real.sqrt 5 := by
  calc Real.sqrt 10 * Real.sqrt 2 = Real.sqrt (10 * 2 : ℝ) :=
      (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10) 2).symm
    _ = Real.sqrt ((2 : ℝ) ^ 2 * 5) := by
      congr 1
      norm_num
    _ = Real.sqrt ((2 : ℝ) ^ 2) * Real.sqrt 5 := Real.sqrt_mul (sq_nonneg 2) 5
    _ = 2 * Real.sqrt 5 := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]

/-- The product of the complex inverses of two real numbers equals the complex inverse of their
real product. -/
theorem inv_cast_mul (a b : ℝ) :
    ((a : ℂ)⁻¹ * (b : ℂ)⁻¹) = ((a * b : ℝ) : ℂ)⁻¹ := by
  rw [← _root_.mul_inv_rev, ← Complex.ofReal_mul, mul_comm b a]

/-- The two eigenvalue grid HHL output is the normalized vector `√5` inverse times the vector
with coordinates two and one. -/
theorem gridHHLb2_output :
    gridHHLOutput gridHHLLabel2 (1 : Operator 2) (1 / 4) gridHHLb2
      = some ((Real.sqrt 5 : ℂ)⁻¹ • ((2 : ℂ) • Ket (0 : Fin 2) + Ket (1 : Fin 2))) := by
  have hV : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, one_conjTranspose]
    simp
  have hsq : (Real.sqrt 10 : ℝ) * Real.sqrt 2 = 2 * Real.sqrt 5 := gridHHLb2_sqrt_key
  have hinv : ((Real.sqrt 10 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      = ((2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ := by
    rw [inv_cast_mul, hsq]
    exact (inv_cast_mul 2 (Real.sqrt 5)).symm
  have h4 : (((2 : ℝ) : ℂ)⁻¹ * (4 : ℂ)) = 2 := by norm_num
  have hpoint : ∀ (a c : ℂ), (((2 : ℝ) : ℂ)⁻¹ * a) * c = a * (((2 : ℝ) : ℂ)⁻¹ * c) := by
    intro a c
    have hz : (((2 : ℝ) : ℂ)) = (2 : ℂ) := by norm_num
    rw [hz]
    ring
  have hmp : (0 : ℝ) < MeasureProb ((Real.sqrt 2 : ℂ)⁻¹
      • ((4 : ℂ) • Ket (0 : Fin 2) + (2 : ℂ) • Ket (1 : Fin 2))) Finset.univ := by
    rw [gridHHLb2_successBlock_measure]
    norm_num
  rw [((grid_hhl_actual_probability_and_output gridHHLLabel2 _ (1 / 4) gridHHLb2
      (by norm_num) hV (by norm_num) (by norm_num)).2.1 (by norm_num : (0 : ℝ) < 1 / 4)),
    gridHHLb2_pseudoinverse (by norm_num), ConditionalState, ite_eq_left hmp]
  congr 1
  funext i
  show (Real.sqrt (MeasureProb ((Real.sqrt 2 : ℂ)⁻¹
      • ((4 : ℂ) • Ket (0 : Fin 2) + (2 : ℂ) • Ket (1 : Fin 2))) Finset.univ) : ℂ)⁻¹
      * Collapse ((Real.sqrt 2 : ℂ)⁻¹
        • ((4 : ℂ) • Ket (0 : Fin 2) + (2 : ℂ) • Ket (1 : Fin 2))) Finset.univ i
      = ((Real.sqrt 5 : ℂ)⁻¹ • ((2 : ℂ) • Ket (0 : Fin 2) + Ket (1 : Fin 2))) i
  rw [gridHHLb2_successBlock_measure, collapse_apply]
  simp only [Finset.mem_univ, ite_eq_left]
  match i with
  | 0 => simp [Ket]; rw [← mul_assoc, hinv, hpoint, h4]
  | 1 => simp [Ket]; rw [← mul_assoc, hinv, hpoint]; norm_num

/-- The two eigenvalue example has probability `5 / 8`, normalized output proportional to the
vector with coordinates two and one, and gate count seven. -/
theorem grid_hhl_two_eigenvalue_actual_consumer :
    gridHHLProbability gridHHLLabel2 (1 : Operator 2) (1 / 4) gridHHLb2 = 5 / 8 ∧
    gridHHLOutput gridHHLLabel2 (1 : Operator 2) (1 / 4) gridHHLb2
      = some ((Real.sqrt 5 : ℂ)⁻¹ • ((2 : ℂ) • Ket (0 : Fin 2) + Ket (1 : Fin 2))) ∧
    GateCount (gridHHLCircuit (D := 2) (M := 4) gridHHLLabel2 (1 : Operator 2) (1 / 4)) = 7 := by
  refine ⟨gridHHLb2_probability, gridHHLb2_output, ?_⟩
  simp [gridHHLCircuit, gridHHLQPEBlock, gridHHLQPEBlockInv]

/-- For a unitary eigenbasis and positive grid size, applying the grid matrix to its
pseudoinverse response gives the range projection of the input. -/
theorem gridHHL_recovers_projected_system {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (b : QState (Fin D)) :
    gridHHLMatrix label V *ᵥ (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)
      = gridHHLRangeProjector label V *ᵥ b := by
  rw [← grid_hhl_spectral_reciprocal_eq_pseudoinverse hM label V hV,
    Matrix.mulVec_mulVec, gridHHLMatrix_mul_reciprocal hM label V hV]

/-- The labels zero and one in a four point grid, defining the rank one example. -/
def gridHHLRankOneLabel : Fin 2 → Fin 4 := fun i => if i = 0 then 0 else 1

/-- The rank one grid pseudoinverse sends the equal superposition to `4 / √2` times the second
basis state. -/
theorem gridHHL_rank_one_inverse_input :
    matrixPseudoinverse (gridHHLMatrix gridHHLRankOneLabel (1 : Operator 2)) *ᵥ gridHHLb2
      = ((4 / Real.sqrt 2 : ℝ) : ℂ) • Ket (1 : Fin 2) := by
  rw [← grid_hhl_spectral_reciprocal_eq_pseudoinverse (by norm_num)
      gridHHLRankOneLabel (1 : Operator 2) (by simp), gridHHLReciprocal]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, gridHHLReciprocalScale,
      gridHHLRankOneLabel, gridHHLb2, Ket, div_eq_mul_inv, mul_comm]

/-- The rank one example has a normalized inconsistent right hand side, success probability `1 /
2`, output the second basis state, and seven gates. -/
theorem grid_hhl_low_rank_inconsistent_actual_consumer :
    Normalized gridHHLb2 ∧
    (¬ ∃ x : QState (Fin 2), gridHHLMatrix gridHHLRankOneLabel (1 : Operator 2) *ᵥ x
        = gridHHLb2) ∧
    gridHHLProbability gridHHLRankOneLabel (1 : Operator 2) (1 / 4) gridHHLb2 = 1 / 2 ∧
    gridHHLOutput gridHHLRankOneLabel (1 : Operator 2) (1 / 4) gridHHLb2
        = some (Ket (1 : Fin 2)) ∧
    GateCount (gridHHLCircuit gridHHLRankOneLabel (1 : Operator 2) (1 / 4)) = 7 := by
  have hv : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by simp
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hk : MeasureProb (Ket (1 : Fin 2)) Finset.univ = 1 := normalized_ket 1
  have hb0 : gridHHLb2 0 = (Real.sqrt 2 : ℂ)⁻¹ := by simp [gridHHLb2, Ket]
  have hg5 := grid_hhl_actual_probability_and_output gridHHLRankOneLabel
    (1 : Operator 2) (1 / 4) gridHHLb2 (by norm_num) hv (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Normalized, gridHHLb2, Fin.sum_univ_two, Ket, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · rintro ⟨x, hx⟩
    have hzero : (gridHHLMatrix gridHHLRankOneLabel (1 : Operator 2) *ᵥ x) 0 = 0 := by
      simp [gridHHLMatrix, gridHHLRankOneLabel, Matrix.mulVec, dotProduct]
    have h := congrFun hx 0
    rw [hzero, hb0] at h
    exact (inv_ne_zero (by exact_mod_cast hs.ne' : (Real.sqrt 2 : ℂ) ≠ 0)) h.symm
  · rw [hg5.1, gridHHL_rank_one_inverse_input, measureProb_smul_real, hk]
    norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [hg5.2.1 (by norm_num), gridHHL_rank_one_inverse_input,
      conditionalState_smul (by positivity : (0 : ℝ) < 4 / Real.sqrt 2)]
    simp only [ConditionalState, hk, zero_lt_one, ↓reduceIte]
    congr 1
    funext i
    simp [Qatlib.Foundations.InstrumentCore.Measurement.PostMeasure, hk, collapse_apply]
  · exact (grid_hhl_actual_program_legality_and_macro_counts 2 4 gridHHLRankOneLabel
      (1 : Operator 2) (1 / 4) (by norm_num) hv (by norm_num) (by norm_num)).2.2

end Qatlib.Concepts.QsvtCore.LinearSystems
