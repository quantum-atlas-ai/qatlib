/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSVM13.GramDensity
import Qatlib.Papers.QuantumSVM13.CopyStep
import Qatlib.Papers.QuantumSVM13.TraceReadout.TraceEstimation
import Qatlib.Papers.QuantumSVM13.TraceReadout.ActualData

/-! # Actual data consumers of the kernel-copy and trace-readout producers
The entries and amplitudes come from the given real data table. No final kernel
density, evolved state, success probability or trace estimate is supplied as a field.
This is a finite static/measurement contract, not an efficient QRAM or HHL implementation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QuantumSVM13.TraceReadout

open Qatlib.Papers.QuantumSVM13.CopyStep
open Qatlib.Papers.QuantumSVM13.GramDensity
open Qatlib.Papers.QuantumSVM13.TraceReadout
open Qatlib.Concepts.CopyEvolution.Discriminate

/-- The actual finite ancilla-one readout is a nonnegative probability mass. -/
theorem actualTraceWeight_nonneg {M N : ℕ} (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (t : ℝ) : 0 ≤ actualTraceWeight x hM t := by
  unfold actualTraceWeight
  exact Finset.sum_nonneg (fun p hp => bornProb_nonneg _ _)

/-- The finite ancilla-one readout is bounded by total probability mass. -/
theorem actualTraceWeight_le_one {M N : ℕ} (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (t : ℝ) : actualTraceWeight x hM t ≤ 1 := by
  rw [actualTraceWeight_eq]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : (∑ j, Real.sin (dataVecNorm (x j) * t) ^ 2) ≤ (M : ℝ) := by
    calc
      (∑ j, Real.sin (dataVecNorm (x j) * t) ^ 2)
          ≤ ∑ _ : Fin M, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            apply (sq_le_one_iff_abs_le_one _).2
            exact (abs_le).2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      _ = (M : ℝ) := by simp
  calc
    (1 / (M : ℝ)) * ∑ j, Real.sin (dataVecNorm (x j) * t) ^ 2
        ≤ (1 / (M : ℝ)) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

/-- The finite readout has the quadratic small-time envelope induced by the
actual training-table norm, before invoking the sharper fourth-order bias
estimate. -/
theorem actualTraceWeight_le_quadratic {M N : ℕ} (x : Fin M → Fin N → ℝ)
    (hM : 0 < M) (t : ℝ) :
    actualTraceWeight x hM t ≤ t ^ 2 / (M : ℝ) * dataNormSq x := by
  rw [actualTraceWeight_eq]
  have hsum :
      (∑ j, Real.sin (dataVecNorm (x j) * t) ^ 2) ≤
        ∑ j, (dataVecNorm (x j) * t) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    exact (sq_le_sq).2 (Real.abs_sin_le_abs)
  have hnorm : (∑ j, dataVecNorm (x j) ^ 2) = dataNormSq x := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg (x j k))
  calc
    (1 / (M : ℝ)) * ∑ j, Real.sin (dataVecNorm (x j) * t) ^ 2
        ≤ (1 / (M : ℝ)) * ∑ j, (dataVecNorm (x j) * t) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = t ^ 2 / (M : ℝ) * dataNormSq x := by
      rw [show (∑ j, (dataVecNorm (x j) * t) ^ 2) =
          t ^ 2 * ∑ j, dataVecNorm (x j) ^ 2 by
        simp_rw [mul_pow]
        rw [← Finset.sum_mul]
        ring]
      rw [hnorm]
      ring

/-- A zero-norm training table has no ancilla-one mass at any evolution time. -/
theorem actualTraceWeight_zero_of_dataNormSq_zero {M N : ℕ}
    (x : Fin M → Fin N → ℝ) (hM : 0 < M) (t : ℝ)
    (hzero : dataNormSq x = 0) : actualTraceWeight x hM t = 0 := by
  apply le_antisymm
  · simpa [hzero] using actualTraceWeight_le_quadratic x hM t
  · exact actualTraceWeight_nonneg x hM t

/-- The native readout satisfies both the total-probability and data-norm
envelopes simultaneously. -/
theorem actualTraceWeight_le_min_one_quadratic {M N : ℕ}
    (x : Fin M → Fin N → ℝ) (hM : 0 < M) (t : ℝ) :
    actualTraceWeight x hM t ≤
      min 1 (t ^ 2 / (M : ℝ) * dataNormSq x) := by
  exact le_min (actualTraceWeight_le_one x hM t)
    (actualTraceWeight_le_quadratic x hM t)

/-- Package the native finite readout as an explicit probability interval. -/
theorem actualTraceWeight_mem_Icc_min_one_quadratic {M N : ℕ}
    (x : Fin M → Fin N → ℝ) (hM : 0 < M) (t : ℝ) :
    actualTraceWeight x hM t ∈
      Set.Icc 0 (min 1 (t ^ 2 / (M : ℝ) * dataNormSq x)) := by
  exact ⟨actualTraceWeight_nonneg x hM t,
    actualTraceWeight_le_min_one_quadratic x hM t⟩

/-- The native finite ancilla readout is a valid probability mass. -/
theorem actualTraceWeight_mem_Icc_one {M N : ℕ}
    (x : Fin M → Fin N → ℝ) (hM : 0 < M) (t : ℝ) :
    actualTraceWeight x hM t ∈ Set.Icc 0 1 := by
  exact ⟨actualTraceWeight_nonneg x hM t, actualTraceWeight_le_one x hM t⟩

/-- At zero evolution time the actual ancilla-one readout has zero mass. -/
theorem actualTraceWeight_zero_time {M N : ℕ} (x : Fin M → Fin N → ℝ) (hM : 0 < M) :
    actualTraceWeight x hM 0 = 0 := by
  rw [actualTraceWeight_eq x hM 0]
  simp

/-- A finite algebraic witness: the first of two training rows is `(1, 0)` and the
second is zero. This table is a static trace-readout consumer, not a physical
QRAM or circuit implementation. -/
def traceToyData : Fin 2 → Fin 2 → ℝ :=
  fun i k => if i = 0 ∧ k = 0 then 1 else 0

/-- The toy table has exact unnormalised training-kernel trace one. -/
theorem traceToyData_trainingKernel_trace :
    Matrix.trace (trainingKernel traceToyData) = (1 : ℂ) := by
  rw [trainingKernel_trace]
  norm_num [dataNormSq, traceToyData, Fin.sum_univ_two]
  decide

/-- The toy table's exact ancilla-one trace-readout weight at time `π / 2` is
`1 / 2`; this is a finite evaluation of the native definitions. -/
theorem traceToyData_trace_weight :
    actualTraceWeight traceToyData (by norm_num) (Real.pi / 2) = (1 : ℝ) / 2 := by
  rw [actualTraceWeight_eq]
  have hnorm0 : dataVecNorm (traceToyData 0) = 1 := by
    norm_num [dataVecNorm, traceToyData, Fin.sum_univ_two]
  have hnorm1 : dataVecNorm (traceToyData 1) = 0 := by
    norm_num [dataVecNorm, traceToyData, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, hnorm0, hnorm1]
  norm_num

/-- The toy table's exact trace-readout bias against the leading trace term is
`|1 / 2 - π² / 8|`; this equality records the finite model's bias without
claiming that the scalar model is a physical algorithm. -/
theorem traceToyData_trace_bias :
    |actualTraceWeight traceToyData (by norm_num) (Real.pi / 2) -
      (Real.pi / 2) ^ 2 / (2 : ℝ) *
        (Matrix.trace (trainingKernel traceToyData)).re| =
      |(1 : ℝ) / 2 - Real.pi ^ 2 / 8| := by
  rw [traceToyData_trace_weight, traceToyData_trainingKernel_trace]
  norm_num [Complex.ofReal_re]
  congr 1
  ring

/-- The concrete trace toy input remains normalized after its native unitary
evolution at the same time used by the finite readout consumer. -/
theorem traceToyData_output_normalized :
    Normalized (ApplyGate
      (HamiltonianEvolution (traceHamiltonian (fun j => dataVecNorm (traceToyData j)))
        (Real.pi / 2))
      (uniformTraceState (by norm_num))) := by
  exact actual_trace_output_normalized traceToyData (by norm_num) (Real.pi / 2)
end Qatlib.Papers.QuantumSVM13.TraceReadout
