/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Papers.NonlinearDE20.ForcingModel.Counter

abbrev Tail (m : ℕ) := Fin m→Fin 2

def copiedAmplitude (m : ℕ) (p : Fin 2×Tail m) : ℂ :=
  10*(if p.1=0 ∧ p.2=(fun _=>0) then 1 else 0)+
    (if p.1=1 ∧ p.2=(fun _=>1) then 1 else 0)

def copiedDensity (m : ℕ) : Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ :=
  (1/101:ℝ) • Matrix.vecMulVec (copiedAmplitude m) (star (copiedAmplitude m))

def reduced {m : ℕ} (ρ : Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b=>∑ r : Tail m,ρ (a,r) (b,r)

theorem tail_basis_ne (m : ℕ) (hm : 0 < m) : (fun _ : Fin m=>(0:Fin 2))≠(fun _=>(1:Fin 2)) := by
  intro h
  have hh := congrFun h ⟨0,hm⟩
  norm_num at hh

theorem copied_reduced (m : ℕ) (hm : 0 < m) :
    reduced (copiedDensity m)=!![(100/101:ℂ),0;0,1/101] := by
  have hn := tail_basis_ne m hm
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [reduced,copiedDensity,Matrix.vecMulVec,copiedAmplitude,Ne.symm hn,
      mul_ite,ite_mul,map_ofNat]

theorem copiedDensity_psd (m : ℕ) : (copiedDensity m).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (copiedAmplitude m)).smul (by norm_num : (0:ℝ)≤1/101)

theorem reduced_trace (m : ℕ) (ρ : Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ) :
    (reduced ρ).trace=ρ.trace := by
  simp [Matrix.trace,reduced,Fintype.sum_prod_type]

theorem copiedDensity_trace (m : ℕ) (hm : 0 < m) : (copiedDensity m).trace=1 := by
  rw [← reduced_trace,copied_reduced m hm]
  norm_num [Matrix.trace,Fin.sum_univ_two]

def targetAmplitude : Fin 2→ℂ := ![10,1]

def targetDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/101:ℝ) • Matrix.vecMulVec targetAmplitude (star targetAmplitude)

theorem targetDensity_matrix : targetDensity=!![(100/101:ℂ),10/101;10/101,1/101] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [targetDensity,targetAmplitude,Matrix.vecMulVec,map_ofNat]

theorem targetDensity_psd : targetDensity.PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star targetAmplitude).smul (by norm_num : (0:ℝ)≤1/101)

theorem targetDensity_trace : targetDensity.trace=1 := by
  rw [targetDensity_matrix]
  norm_num [Matrix.trace,Fin.sum_univ_two]

theorem density_difference (m : ℕ) (hm : 0 < m) :
    reduced (copiedDensity m)-targetDensity=(-10/101:ℂ) • (!![0,1;1,0]:Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [copied_reduced m hm,targetDensity_matrix]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num

theorem swap_traceNorm : Matrix.traceNorm (!![0,1;1,0]:Matrix (Fin 2) (Fin 2) ℂ)=2 := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
  have h : Matrix.traceNorm (X*(1:Matrix (Fin 2) (Fin 2) ℂ))=Matrix.traceNorm (1:Matrix (Fin 2) (Fin 2) ℂ) := by
    apply Matrix.traceNorm_isometry_left
    unfold Matrix.Isometry
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [X,Matrix.mul_apply,Fin.sum_univ_two]
  simp only [Matrix.mul_one] at h
  rw [h]
  norm_num [Matrix.traceNorm,Matrix.trace,Fin.sum_univ_two]

theorem forcing_traceNorm_counterexample (m : ℕ) (hm : 0 < m) :
    Matrix.traceNorm (reduced (copiedDensity m)-targetDensity)=20/101 := by
  rw [density_difference m hm,Matrix.traceNorm_smul,swap_traceNorm]
  norm_num [Complex.norm_def]

end Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
