/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSVM13.GramDensity
import Qatlib.Papers.QuantumSVM13.CopyStep
import Qatlib.Papers.QuantumSVM13.TraceReadout.TraceEstimation
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
namespace Qatlib.Papers.QuantumSVM13.TraceReadout
open Qatlib.Papers.QuantumSVM13.GramDensity
open Qatlib.Papers.QuantumSVM13.CopyStep
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

def trainingKernel {M N : ℕ} (x : Fin M→Fin N→ℝ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => ((∑ k, x i k*x j k:ℝ):ℂ)

theorem trainingKernel_trace {M N : ℕ} (x : Fin M→Fin N→ℝ) :
    Matrix.trace (trainingKernel x)=(dataNormSq x:ℂ) := by
  simp [Matrix.trace,trainingKernel,dataNormSq,pow_two]

theorem actual_dataset_copy_step {M N : ℕ} (x : Fin M→Fin N→ℝ) (hM : 0<M)
    (hx : ∀ i,0<∑ k,(x i k)^2) (rho : Operator M) (theta : ℝ) :
    ‖partialSwapOutput (kernelDensity x) theta rho-
        (rho-(Complex.I*(theta:ℂ))•commutator (kernelDensity x) rho)‖ ≤
      theta^2*(‖Matrix.trace rho‖*‖kernelDensity x‖+‖rho‖+4*‖kernelDensity x‖*‖rho‖) := by
  exact kernel_swap_quadratic_error _ _ (kernelDensity_bridge x hM hx).2.2 theta

def actualTraceWeight {M N : ℕ} (x : Fin M→Fin N→ℝ) (hM : 0<M) (t : ℝ) : ℝ :=
  ∑ p∈Finset.univ.filter (fun p:Fin 2×Fin M=>p.1=1),
    BornProb (ApplyGate (HamiltonianEvolution (traceHamiltonian (fun j=>dataVecNorm (x j))) t)
      (uniformTraceState hM)) p

theorem actualTraceWeight_eq {M N : ℕ} (x : Fin M→Fin N→ℝ) (hM : 0<M) (t : ℝ) :
    actualTraceWeight x hM t=(1/(M:ℝ))*∑ j,Real.sin (dataVecNorm (x j)*t)^2 := by
  unfold actualTraceWeight
  rw [traceEvolvedState_eq _ _ hM,traceSuccessProb_eq _ _ hM]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_of_nonneg (show 0≤dataVecNorm (x j) from Real.sqrt_nonneg _)]

theorem actual_trace_output_normalized {M N : ℕ} (x : Fin M→Fin N→ℝ)
    (hM : 0<M) (t : ℝ) :
    Normalized (ApplyGate (HamiltonianEvolution (traceHamiltonian (fun j=>dataVecNorm (x j))) t)
      (uniformTraceState hM)) :=
  normalized_applyGate (traceHamiltonian_unitary _ _) (uniformTraceState_normalized hM)

theorem dataVecNorm_sq_sum {M N : ℕ} (x : Fin M→Fin N→ℝ) :
    (∑ j,dataVecNorm (x j)^2)=dataNormSq x := by
  apply Finset.sum_congr rfl
  intro j _
  exact Real.sq_sqrt (Finset.sum_nonneg fun k _=>sq_nonneg (x j k))

theorem actual_trace_bias_bound {M N : ℕ} (x : Fin M→Fin N→ℝ) (hM : 0<M)
    (t : ℝ) (ht : 0≤t) (hsmall : ∀ j,dataVecNorm (x j)*t≤1) :
    |actualTraceWeight x hM t-t^2/(M:ℝ)*(Matrix.trace (trainingKernel x)).re| ≤
      t^4/(M:ℝ)*∑ j,(∑ k,(x j k)^2)^2 := by
  unfold actualTraceWeight
  rw [traceEvolvedState_eq _ _ hM,trainingKernel_trace,Complex.ofReal_re]
  have hb := traceSuccessProb_error (fun j=>dataVecNorm (x j)) t hM
    (fun j=>by simpa only [abs_of_nonneg (show 0≤dataVecNorm (x j) from Real.sqrt_nonneg _)] using hsmall j) ht
  rw [dataVecNorm_sq_sum] at hb
  have hf : (∑ j,dataVecNorm (x j)^4)=∑ j,(∑ k,(x j k)^2)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show dataVecNorm (x j)^4=(dataVecNorm (x j)^2)^2 by ring]
    rw [dataVecNorm,Real.sq_sqrt (Finset.sum_nonneg fun k _=>sq_nonneg (x j k))]
  simpa only [hf] using hb
end Qatlib.Papers.QuantumSVM13.TraceReadout
