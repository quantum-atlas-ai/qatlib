/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QftPreparation.LocalQft
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic
import Qatlib.Papers.QSystemSim96.MainResults.ShortTimeStepFactorization
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QftPreparation.LocalQft
open Matrix
open scoped BigOperators
noncomputable section
namespace Qatlib.Papers.QSystemSim96.MainResults

def zmodFourier (M : ℕ) [NeZero M] : Matrix (ZMod M) (ZMod M) ℂ :=
  fun a b => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (a*b)

theorem finZmodValue (M : ℕ) [NeZero M] (a : ZMod M) :
    ((ZMod.finEquiv M).symm a).val = a.val := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M => rfl

theorem qftFinZmod (M : ℕ) [NeZero M] :
    relabelGate (ZMod.finEquiv M).toEquiv (QFTMatrix M) = zmodFourier M := by
  ext a b
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, zmodFourier]
  change (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^
    ((((ZMod.finEquiv M).symm a).val : ℤ) * (((ZMod.finEquiv M).symm b).val : ℤ)) = _
  rw [finZmodValue, finZmodValue]
  have hab : a*b = (((a.val*b.val : ℕ) : ℤ) : ZMod M) := by
    push_cast
    simp
  rw [hab, ZMod.stdAddChar_coe, primRoot, ← Complex.exp_int_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem diagonalQftSandwichRun (n : ℕ) (Cpre Cpost : Circuit (Reg n))
    (Dpre Dpost : Matrix (Reg n) (Reg n) ℂ)
    (hpre : ∀ψ, Run 1 Cpre ψ = ApplyGate Dpre ψ)
    (hpost : ∀ψ, Run 1 Cpost ψ = ApplyGate Dpost ψ) (ψ : QState (Reg n)) :
    Run 1 (Cpre ++ localProgramCircuit (localQFT n) ++ Cpost) ψ =
      ApplyGate (Dpost * relabelGate (bitVecEquiv n).symm (QFTMatrix (2^n)) * Dpre) ψ := by
  rw [run_append, run_append, hpre, (localDyadicProgram_run_adjoint_cost n (localQFT n) _).1,
    (localQFT_exact_positive_matrix n).1, hpost, applyGate_mul, applyGate_mul]

theorem diagonalQftSandwichCosts (n : ℕ) (Cpre Cpost : Circuit (Reg n)) :
    GateCount (Cpre ++ localProgramCircuit (localQFT n) ++ Cpost) =
      GateCount Cpre + (n+n*(n-1)/2+n/2) + GateCount Cpost ∧
    QueryCount (Cpre ++ localProgramCircuit (localQFT n) ++ Cpost) =
      QueryCount Cpre + QueryCount Cpost := by
  rw [gateCount_append, gateCount_append, queryCount_append, queryCount_append,
    (aqLocalQFT_actual_matrix_and_cost n).2.1, (aqLocalQFT_actual_matrix_and_cost n).2.2]
  simp

def latticeRegEquiv (n : ℕ) : Reg n ≃ ZMod (2 ^ n) :=
  (bitVecEquiv n).trans (ZMod.finEquiv (2 ^ n)).toEquiv

theorem localQFT_lattice_matrix (n : ℕ) :
    relabelGate (latticeRegEquiv n) (localProgramMatrix (localQFT n)) =
      zmodFourier (2 ^ n) := by
  calc
    relabelGate (latticeRegEquiv n) (localProgramMatrix (localQFT n)) =
        relabelGate (ZMod.finEquiv (2 ^ n)).toEquiv (QFTMatrix (2 ^ n)) := by
      rw [(aqLocalQFT_actual_matrix_and_cost n).1]
      ext a b
      simp [relabelGate, latticeRegEquiv]
    _ = zmodFourier (2 ^ n) := qftFinZmod _

theorem source_basis_map_qft_sandwich (N : ℕ) [NeZero N]
    (m Δx Δt : ℝ) (V : ZMod N → ℝ)
    (hcond : m * Δx ^ 2 / Δt = 2 * Real.pi / (N : ℝ)) :
    stepMatrix N m Δx Δt V =
      diagonalRight N m Δx Δt * zmodFourier N * diagonalLeft N m Δx Δt V := by
  rw [stepMatrix_eq_smul_diagonal_mul_fourier_mul_diagonal,
    fourierMatrix_eq_twistedDFT N m Δx Δt 1 (by simpa using hcond)]
  have hnorm : zmodFourier N = stepNormalisation N • twistedDFT N 1 := by
    ext a b
    simp [zmodFourier, stepNormalisation, twistedDFT, Matrix.smul_apply]
  rw [hnorm, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Nat.cast_one]

theorem source_basis_map_unitary (N : ℕ) [NeZero N]
    (m Δx Δt : ℝ) (V : ZMod N → ℝ)
    (hcond : m * Δx ^ 2 / Δt = 2 * Real.pi / (N : ℝ)) :
    stepMatrix N m Δx Δt V ∈ Matrix.unitaryGroup (ZMod N) ℂ :=
  stepMatrix_mem_unitaryGroup N m Δx Δt V 1 (by simp) (by simpa using hcond)

end Qatlib.Papers.QSystemSim96.MainResults
