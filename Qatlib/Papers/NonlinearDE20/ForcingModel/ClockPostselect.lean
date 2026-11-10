/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.ForcingModel.ForcingHistoryBridge
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
open Qatlib.Papers.NonlinearDE20.HistorySystem.History

def clockSelector {J : Type} [DecidableEq J] (N : ℕ) (k : Fin N) : Matrix J (Fin N×J) ℂ :=
  fun i p=>if p=(k,i) then 1 else 0

theorem clockSelector_action {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N)
    (X : Fin N×J→ℂ) (i : J) : (clockSelector (J:=J) N k*ᵥ X) i=X (k,i) := by
  simp [Matrix.mulVec,dotProduct,clockSelector,ite_mul]

theorem clockSelector_coisometry {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N) :
    clockSelector (J:=J) N k*(clockSelector (J:=J) N k)ᴴ=1 := by
  ext i j
  simp [Matrix.mul_apply,clockSelector,Matrix.conjTranspose_apply,mul_ite,Matrix.one_apply,eq_comm]

theorem clockSelector_outer {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N) (X : Fin N×J→ℂ) :
    clockSelector (J:=J) N k*sliceOuter X*(clockSelector (J:=J) N k)ᴴ=sliceOuter (fun i=>X (k,i)) := by
  ext i j
  simp [Matrix.mul_apply,clockSelector,Matrix.conjTranspose_apply,sliceOuter,Matrix.vecMulVec,
    mul_ite,ite_mul]

def normalizeMatrix {J : Type} [Fintype J] (ρ : Matrix J J ℂ) : Matrix J J ℂ :=ρ.trace.re⁻¹ •ρ

theorem normalizeMatrix_smul {J : Type} [Fintype J] (ρ : Matrix J J ℂ) (a : ℝ) (ha : a≠0) :
    normalizeMatrix (a •ρ)=normalizeMatrix ρ := by
  rw [normalizeMatrix,Matrix.trace_smul,Complex.smul_re,smul_eq_mul,smul_smul,normalizeMatrix]
  congr 1
  rw [_root_.mul_inv_rev,mul_assoc,inv_mul_cancel₀ ha,mul_one]

theorem normalized_clock_condition {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N)
    (X : Fin N×J→ℂ) (hX : 0<(sliceOuter X).trace.re) :
    normalizeMatrix (clockSelector (J:=J) N k*normalizeMatrix (sliceOuter X)*(clockSelector (J:=J) N k)ᴴ)=
      conditionSlice (fun i=>X (k,i)) := by
  change normalizeMatrix
      (clockSelector (J:=J) N k*((sliceOuter X).trace.re⁻¹ •sliceOuter X)*(clockSelector (J:=J) N k)ᴴ)=_
  rw [Matrix.mul_smul,Matrix.smul_mul,normalizeMatrix_smul _ _ (inv_ne_zero hX.ne'),clockSelector_outer]
  rfl

def singleEulerTarget : Fin 2→ℂ :=basis 0+(1/10:ℂ) •basis 1

theorem targetDensity_singleEuler : targetDensity=conditionSlice singleEulerTarget := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [targetDensity,targetAmplitude,conditionSlice,sliceOuter,Matrix.trace,Matrix.vecMulVec,
      Fin.sum_univ_two,singleEulerTarget,basis,map_ofNat]

end Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
