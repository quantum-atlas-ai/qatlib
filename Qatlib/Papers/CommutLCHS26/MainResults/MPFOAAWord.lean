/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAPadding
import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAASine
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAWord

open Matrix
open scoped Classical Matrix.Norms.L2Operator
open MPFOAAChoice MPFOAASine
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
set_option warningAsError false

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def word (A : ℝ) (R : Matrix H I ℂ) : List (AdjointStep H) :=
  compileQSVT (rangeProjector R) (rangeProjector R) (-Complex.I) (List.replicate (queries A) Complex.I)

omit [Fintype H] [DecidableEq I] in

theorem word_counts (A : ℝ) (R : Matrix H I ℂ) :
    adjointQueryCount (word A R) = queries A ∧ adjointGateCount (word A R) = queries A + 1 := by
  simp [word, queryCount_compileQSVT, gateCount_compileQSVT]

theorem word_wellFormed (A : ℝ) (R : Matrix H I ℂ) (hR : IsIsometry R) :
    WellFormedAdjointCircuit (word A R) := by
  apply compileQSVT_wellFormed (rangeProjector_isOrthogonalProjector hR)
    (rangeProjector_isOrthogonalProjector hR) (by norm_num [IsPhase])
  intro z hz
  have he : z = Complex.I := (List.mem_replicate.mp hz).2
  rw [he]
  norm_num [IsPhase]

theorem response_exact (A : ℝ) :
    (responseP (-Complex.I) (List.replicate (queries A) Complex.I)).eval
      (Real.sin (angle (queries A)) : ℂ) = 1 := by
  have h := (sine_response (rounds A) (angle (queries A))).1
  have ha : (queries A : ℝ) * angle (queries A) = Real.pi / 2 := by
    have hn : (queries A : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (queries_pos A))
    unfold angle
    field_simp
  change _ = (Real.sin ((queries A : ℝ) * angle (queries A)) : ℂ) at h
  simpa only [ha, Real.sin_pi_div_two, Complex.ofReal_one] using! h

theorem word_encoding (A : ℝ) (V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ)
    (hV : V ∈ unitaryGroup I ℂ)
    (h : ProjectedUnitaryEncoding ((Real.sin (angle (queries A)) : ℂ) • V) U R R) :
    ProjectedUnitaryEncoding V (evaluate U (word A R)) R R := by
  have hv : Vᴴ * V = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hav : ((Real.sin (angle (queries A)) : ℂ) • V) * (1 : Matrix I I ℂ) =
      (Real.sin (angle (queries A)) : ℂ) • V := by simp
  have haw : ((Real.sin (angle (queries A)) : ℂ) • V)ᴴ * V =
      (Real.sin (angle (queries A)) : ℂ) • (1 : Matrix I I ℂ) := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, hv, Complex.star_def,
        Complex.conj_ofReal]
  have he := qsvt_odd h hav haw (-Complex.I) (List.replicate (queries A) Complex.I)
    (by simp only [List.length_replicate, queries]; omega)
  rw [response_exact, one_smul, Matrix.mul_one] at he
  refine ⟨(word_wellFormed A R h.left_isometry).evaluate_unitary h.unitary,
    h.left_isometry, h.right_isometry, ?_⟩
  simpa only [word, evaluate_compileQSVT] using! he

def expanded (A : ℝ) (R : Matrix H I ℂ) (cs : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  substituteAdjointCircuit (MPFOAAPadding.body A cs) (word A (scaleEightFrame R))

omit [DecidableEq I] in

theorem expanded_counts (A : ℝ) (R : Matrix H I ℂ) (cs : List (AdjointStep H)) :
    adjointQueryCount (expanded A R cs) = queries A * adjointQueryCount cs ∧
    adjointGateCount (expanded A R cs) = queries A + 1 + queries A * (adjointGateCount cs + 1) := by
  have h := substitute_adjoint_evaluate_cost (1 : Matrix (Bool × H) (Bool × H) ℂ)
    (MPFOAAPadding.body A cs) (word A (scaleEightFrame R))
  exact ⟨by simpa only [expanded, (word_counts A (scaleEightFrame R)).1,
    (MPFOAAPadding.body_counts A cs).1] using! h.2.1,
    by simpa only [expanded, (word_counts A (scaleEightFrame R)).1,
      (word_counts A (scaleEightFrame R)).2, (MPFOAAPadding.body_counts A cs).2] using! h.2.2.1⟩

omit [DecidableEq I] in

theorem expanded_queries_linear (A : ℝ) (hA : 1 ≤ A) (R : Matrix H I ℂ) (cs : List (AdjointStep H)) :
    (adjointQueryCount (expanded A R cs) : ℝ) ≤
      (Real.pi / 2 + 3) * A * (adjointQueryCount cs : ℝ) := by
  rw [(expanded_counts A R cs).1, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (queries_linear A hA).2 (Nat.cast_nonneg _)

theorem expanded_wellFormed (A : ℝ) (hA : 1 ≤ A) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (cs : List (AdjointStep H)) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (expanded A R cs) :=
  (substitute_adjoint_evaluate_cost (1 : Matrix (Bool × H) (Bool × H) ℂ)
    (MPFOAAPadding.body A cs) (word A (scaleEightFrame R))).2.2.2
      (MPFOAAPadding.body_wellFormed A hA cs hcs)
      (word_wellFormed A _ (scaleEightFrame_isometry R hR))

theorem expanded_encoding (O : Matrix H H ℂ) (A : ℝ) (hA : 1 ≤ A) (V : Matrix I I ℂ)
    (hV : V ∈ unitaryGroup I ℂ) (R : Matrix H I ℂ) (cs : List (AdjointStep H))
    (h : ProjectedUnitaryEncoding ((A : ℂ)⁻¹ • V) (evaluate O cs) R R) :
    ProjectedUnitaryEncoding V (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (expanded A R cs))
      (scaleEightFrame R) (scaleEightFrame R) := by
  rw [expanded, (substitute_adjoint_evaluate_cost (TensorGate (1 : Matrix Bool Bool ℂ) O)
    (MPFOAAPadding.body A cs) (word A (scaleEightFrame R))).1]
  exact word_encoding A V _ _ hV (MPFOAAPadding.body_encoding O A hA V R cs h)

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAWord
