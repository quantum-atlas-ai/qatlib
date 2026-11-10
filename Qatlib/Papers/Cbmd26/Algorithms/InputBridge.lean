/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Foundations.CbmdAnalysis.Core.Algebra
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.Cbmd26.Algorithms

noncomputable section

namespace CBMD

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

variable {W I O : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

theorem blockEncoding_adjoint {A : Matrix O I ℂ} {U : Matrix W W ℂ}
    {L : Matrix W O ℂ} {R : Matrix W I ℂ} {α ε : ℝ}
    (h : BlockEncoding A U L R α ε) :
    BlockEncoding Aᴴ Uᴴ R L α ε := by
  refine ⟨adjoint_unitary h.unitary, h.right_isometry, h.left_isometry,
    h.normalization_pos, h.error_nonneg, ?_⟩
  have heq : Aᴴ - α • compress R Uᴴ L = (A - α • compress L U R)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
      compress_adjoint]
  rw [heq, Matrix.l2_opNorm_conjTranspose]
  exact h.error_le

def oracleAdjointPair {n : Type*} (A : Matrix n n ℂ) : Bool → Matrix n n ℂ :=
  fun b => if b then Aᴴ else A

def sampleCoefficients (s : ℝ) : Bool → ℂ :=
  fun b => if b then (1 + Complex.I * (s : ℂ)) / 2
    else (1 - Complex.I * (s : ℂ)) / 2

theorem sample_coefficient_weight (s : ℝ) :
    (∑ b : Bool, ‖sampleCoefficients s b‖) = Real.sqrt (1 + s ^ 2) := by
  simpa [sampleCoefficients, Fintype.sum_bool, add_comm] using
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.original_oracle_coefficient_weight s

theorem sample_scaled_coefficient_mass (s α : ℝ) (hα : 0 < α) :
    coefficientMass (scaledLCUCoefficients (sampleCoefficients s) (fun _ => α)) =
      α * Real.sqrt (1 + s ^ 2) := by
  rw [(scaled_lcu_coefficient_mass (sampleCoefficients s) (fun _ => α)
    (fun _ => hα)).1, ← Finset.sum_mul, sample_coefficient_weight, mul_comm]

noncomputable def sampleInputUnitary (U : Matrix W W ℂ) (α s : ℝ) :
    Matrix (Bool × W) (Bool × W) ℂ :=
  coefficientLCUUnitary (scaledLCUCoefficients (sampleCoefficients s) (fun _ => α))
    (oracleAdjointPair U) false

theorem original_oracle_sample_blockEncoding
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α ε s : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α ε) :
    BlockEncoding (L + (s : ℂ) • H) (sampleInputUnitary U α s)
      (tagFrame false R) (tagFrame false R)
      (α * Real.sqrt (1 + s ^ 2)) (ε * Real.sqrt (1 + s ^ 2)) := by
  have hpair : ∀ b : Bool, BlockEncoding (oracleAdjointPair (L + Complex.I • H) b)
      (oracleAdjointPair U b) R R α ε := by
    intro b
    cases b
    · exact henc
    · exact blockEncoding_adjoint henc
  have hmass : 0 < coefficientMass
      (scaledLCUCoefficients (sampleCoefficients s) (fun _ => α)) := by
    rw [sample_scaled_coefficient_mass s α henc.normalization_pos]
    apply mul_pos henc.normalization_pos
    apply Real.sqrt_pos.2
    positivity
  have hsum : (∑ b : Bool, sampleCoefficients s b •
      oracleAdjointPair (L + Complex.I • H) b) = L + (s : ℂ) • H := by
    simpa [Fintype.sum_bool, sampleCoefficients, oracleAdjointPair, add_comm] using
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.hermitian_sample_from_original L H hL hH s
  have hn (a : ℝ) : (∑ b : Bool, ‖sampleCoefficients s b‖ * a) =
      a * Real.sqrt (1 + s ^ 2) := by
    rw [← Finset.sum_mul, sample_coefficient_weight, mul_comm]
  have h := scaled_approximate_lcu_encoding false
    (oracleAdjointPair (L + Complex.I • H)) (oracleAdjointPair U) R R
    (sampleCoefficients s) (fun _ => α) (fun _ => ε) hpair hmass
  rw [hsum, hn α, hn ε] at h
  exact h

def firstOrderCoefficients (s : ℝ) : Bool → ℂ :=
  fun b => if b then ((s : ℂ) + Complex.I) / 2
    else ((s : ℂ) - Complex.I) / 2

theorem first_order_coefficient_weight (s : ℝ) :
    (∑ b : Bool, ‖firstOrderCoefficients s b‖) = Real.sqrt (1 + s ^ 2) := by
  have hm : ((s : ℂ) - Complex.I) / 2 =
      -Complex.I * ((1 + Complex.I * (s : ℂ)) / 2) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hp : ((s : ℂ) + Complex.I) / 2 =
      Complex.I * ((1 - Complex.I * (s : ℂ)) / 2) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp only [Fintype.sum_bool, firstOrderCoefficients, Bool.false_eq_true,
    ↓reduceIte, hm, hp, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.original_oracle_coefficient_weight s

noncomputable def firstOrderInputUnitary (U : Matrix W W ℂ) (α s : ℝ) :
    Matrix (Bool × W) (Bool × W) ℂ :=
  coefficientLCUUnitary (scaledLCUCoefficients (firstOrderCoefficients s) (fun _ => α))
    (oracleAdjointPair U) false

theorem original_oracle_first_order_blockEncoding
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α ε s : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α ε) :
    BlockEncoding (H + (s : ℂ) • L) (firstOrderInputUnitary U α s)
      (tagFrame false R) (tagFrame false R)
      (α * Real.sqrt (1 + s ^ 2)) (ε * Real.sqrt (1 + s ^ 2)) := by
  have hpair : ∀ b : Bool, BlockEncoding (oracleAdjointPair (L + Complex.I • H) b)
      (oracleAdjointPair U b) R R α ε := by
    intro b
    cases b
    · exact henc
    · exact blockEncoding_adjoint henc
  have hn (a : ℝ) : (∑ b : Bool, ‖firstOrderCoefficients s b‖ * a) =
      a * Real.sqrt (1 + s ^ 2) := by
    rw [← Finset.sum_mul, first_order_coefficient_weight, mul_comm]
  have hmass : 0 < coefficientMass
      (scaledLCUCoefficients (firstOrderCoefficients s) (fun _ => α)) := by
    rw [(scaled_lcu_coefficient_mass (firstOrderCoefficients s) (fun _ => α)
      (fun _ => henc.normalization_pos)).1, hn α]
    apply mul_pos henc.normalization_pos
    apply Real.sqrt_pos.2
    positivity
  have hsum : (∑ b : Bool, firstOrderCoefficients s b •
      oracleAdjointPair (L + Complex.I • H) b) = H + (s : ℂ) • L := by
    simpa [Fintype.sum_bool, firstOrderCoefficients, oracleAdjointPair, add_comm] using
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.first_order_sample_from_original L H hL hH s
  have h := scaled_approximate_lcu_encoding false
    (oracleAdjointPair (L + Complex.I • H)) (oracleAdjointPair U) R R
    (firstOrderCoefficients s) (fun _ => α) (fun _ => ε) hpair hmass
  rw [hsum, hn α, hn ε] at h
  exact h

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
