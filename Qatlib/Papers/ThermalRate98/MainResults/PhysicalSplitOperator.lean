/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.SplitOperator
import Qatlib.Concepts.QftPreparation.LocalQft
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation (localQFT)
open Qatlib.Foundations.PureStateMath.BornBridge (relabelGate)

def sourcePhaseDiagonal {N : ℕ} (theta : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun j => Complex.exp (Complex.I*(theta j : ℂ)))

def sourceInputPhase (N : ℕ) (Δt : ℝ) (V : Fin N → ℝ) (j : Fin N) : ℝ :=
  -Real.pi*(j.val : ℝ)^2/(N : ℝ)+V j*Δt

def sourceOutputPhase (N : ℕ) (j : Fin N) : ℝ := -Real.pi*(j.val : ℝ)^2/(N : ℝ)

def sourceChirpKernel (N : ℕ) (m Δx Δt : ℝ) (V : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun out inp => (Real.sqrt (N : ℝ) : ℂ)⁻¹*
    Complex.exp (Complex.I*((-m*((inp.val : ℝ)-(out.val : ℝ))^2*Δx^2/(2*Δt)+V inp*Δt : ℝ) : ℂ))

theorem source_phase_unit (theta : ℝ) :
    star (Complex.exp (Complex.I*(theta : ℂ)))*Complex.exp (Complex.I*(theta : ℂ)) = 1 := by
  have hc : star (Complex.exp (Complex.I*(theta : ℂ))) = Complex.exp (-(Complex.I*(theta : ℂ))) := by
    rw [Complex.star_def,← Complex.exp_conj]
    congr 1
    simp
  rw [hc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero]

theorem sourcePhaseDiagonal_unitary {N : ℕ} (theta : Fin N → ℝ) :
    sourcePhaseDiagonal theta ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  unfold sourcePhaseDiagonal
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  simp only [Pi.star_apply,source_phase_unit,Matrix.diagonal_one]

theorem source_chirp_matrix_factorization (N : ℕ) (hN : 0 < N) (m Δx Δt : ℝ)
    (hΔt : Δt ≠ 0) (V : Fin N → ℝ)
    (hres : m*Δx^2/Δt = 2*Real.pi/(N : ℝ)) :
    sourceChirpKernel N m Δx Δt V =
      sourcePhaseDiagonal (sourceOutputPhase N)*QFTMatrix N*
        sourcePhaseDiagonal (sourceInputPhase N Δt V) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  ext out inp
  simp only [sourcePhaseDiagonal,Matrix.mul_diagonal,Matrix.diagonal_mul,
    source_fourier_kernel_eq_qftMatrix,sourceOutputPhase,sourceInputPhase,sourceChirpKernel]
  have hs := source_split_operator_kernel_factorization m Δx Δt (N : ℝ) hn hΔt hres
    (V inp) (inp.val : ℤ) (out.val : ℤ)
  simp only [Int.cast_natCast] at hs
  have hf : 2*Real.pi*Complex.I*((out.val : ℝ)*(inp.val : ℝ)/(N : ℝ)) =
      Complex.I*(2*Real.pi*(inp.val : ℝ)*(out.val : ℝ)/(N : ℝ)) := by
    push_cast
    ring
  push_cast at hs hf ⊢
  rw [hf,← hs]
  ring

theorem sourceChirpKernel_unitary (N : ℕ) (hN : 0 < N) (m Δx Δt : ℝ)
    (hΔt : Δt ≠ 0) (V : Fin N → ℝ)
    (hres : m*Δx^2/Δt = 2*Real.pi/(N : ℝ)) :
    sourceChirpKernel N m Δx Δt V ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [source_chirp_matrix_factorization N hN m Δx Δt hΔt V hres]
  exact (Matrix.unitaryGroup (Fin N) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin N) ℂ).mul_mem (sourcePhaseDiagonal_unitary _) (qftMatrix_unitary hN))
    (sourcePhaseDiagonal_unitary _)

def sourceChirpWord (N : ℕ) (Δt : ℝ) (V : Fin N → ℝ) : Circuit (Fin N) :=
  [Step.gate (sourcePhaseDiagonal (sourceInputPhase N Δt V)),Step.gate (QFTMatrix N),
    Step.gate (sourcePhaseDiagonal (sourceOutputPhase N))]

theorem sourceChirpWord_run (N : ℕ) (hN : 0 < N) (m Δx Δt : ℝ)
    (hΔt : Δt ≠ 0) (V : Fin N → ℝ)
    (hres : m*Δx^2/Δt = 2*Real.pi/(N : ℝ)) (psi : QState (Fin N)) :
    Run 1 (sourceChirpWord N Δt V) psi = ApplyGate (sourceChirpKernel N m Δx Δt V) psi := by
  rw [source_chirp_matrix_factorization N hN m Δx Δt hΔt V hres]
  simp only [sourceChirpWord,Run,ApplyGate,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem sourceChirpWord_resources (N : ℕ) (hN : 0 < N) (Δt : ℝ) (V : Fin N → ℝ) :
    IsUnitaryCircuit (sourceChirpWord N Δt V) ∧
      QueryCount (sourceChirpWord N Δt V) = 0 ∧ GateCount (sourceChirpWord N Δt V) = 3 := by
  refine ⟨?_,rfl,rfl⟩
  simp only [sourceChirpWord,isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
  exact ⟨sourcePhaseDiagonal_unitary _,qftMatrix_unitary hN,sourcePhaseDiagonal_unitary _⟩

theorem source_native_fourier (n : ℕ) (out inp : Fin (2^n)) :
    localProgramMatrix (localQFT n) ((bitVecEquiv n).symm out) ((bitVecEquiv n).symm inp) =
      (Real.sqrt (2^n : ℕ) : ℂ)⁻¹*
        Complex.exp (2*Real.pi*Complex.I*((out.val : ℝ)*(inp.val : ℝ)/(2^n : ℕ))) ∧
    GateCount (localProgramCircuit (localQFT n)) = n+n*(n-1)/2+n/2 ∧
    QueryCount (localProgramCircuit (localQFT n)) = 0 := by
  have h := aqLocalQFT_actual_matrix_and_cost n
  refine ⟨?_,h.2.1,h.2.2⟩
  rw [h.1]
  simpa only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,
    Equiv.apply_symm_apply] using! source_fourier_kernel_eq_qftMatrix (2^n) out inp

end Qatlib.Papers.ThermalRate98.MainResults
