/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Reduced density of replicated forcing

The vectors `copiedAmplitude` and `targetAmplitude` encode replicated and single-system forcing
targets associated with [LloydEtAl2020]. The module computes their density matrices and the
partial trace `reduced`, proving positivity, unit trace for the stated tail sizes, and a
trace-norm discrepancy independent of the positive number of tail copies.

## Main statements

* `copied_reduced`: For a nonempty tail, the copied density reduces to the diagonal matrix with
  entries `100/101` and `1/101`.
* `density_difference`: For a nonempty tail, the reduced copied density minus the target is
  `-10/101` times the two-dimensional swap matrix.
* `forcing_traceNorm_counterexample`: For every positive tail size, the reduced copied density
  differs from the target density by trace norm `20/101`.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Papers.NonlinearDE20.ForcingModel.Counter

/-- The basis labels for `m` two-level tail systems. -/
abbrev Tail (m : ℕ) := Fin m→Fin 2

/-- The replicated vector with amplitude ten on the all-zero string and amplitude one on the
all-one string. -/
def copiedAmplitude (m : ℕ) (p : Fin 2×Tail m) : ℂ :=
  10*(if p.1=0 ∧ p.2=(fun _=>0) then 1 else 0)+
    (if p.1=1 ∧ p.2=(fun _=>1) then 1 else 0)

/-- The outer product of `copiedAmplitude`, scaled by `1/101`. -/
def copiedDensity (m : ℕ) : Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ :=
  (1/101:ℝ) • Matrix.vecMulVec (copiedAmplitude m) (star (copiedAmplitude m))

/-- The partial trace over the tail systems, leaving the distinguished two-level system. -/
def reduced {m : ℕ} (ρ : Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b=>∑ r : Tail m,ρ (a,r) (b,r)

/-- For a positive tail size, the constant-zero and constant-one tail labels are distinct. -/
theorem tail_basis_ne (m : ℕ) (hm : 0 < m) : (fun _ : Fin m=>(0:Fin 2))≠(fun _=>(1:Fin 2)) := by
  intro h
  have hh := congrFun h ⟨0,hm⟩
  norm_num at hh

/-- For a nonempty tail, the copied density reduces to the diagonal matrix with entries
`100/101` and `1/101`. -/
theorem copied_reduced (m : ℕ) (hm : 0 < m) :
    reduced (copiedDensity m)=!![(100/101:ℂ),0;0,1/101] := by
  have hn := tail_basis_ne m hm
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [reduced,copiedDensity,Matrix.vecMulVec,copiedAmplitude,Ne.symm hn,
      mul_ite,ite_mul,map_ofNat]

/-- The copied density matrix is positive semidefinite. -/
theorem copiedDensity_psd (m : ℕ) : (copiedDensity m).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (copiedAmplitude m)).smul (by norm_num : (0:ℝ)≤1/101)

/-- Taking the partial trace over the tail preserves the matrix trace. -/
theorem reduced_trace (m : ℕ) (ρ : Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ) :
    (reduced ρ).trace=ρ.trace := by
  simp [Matrix.trace,reduced,Fintype.sum_prod_type]

/-- For a nonempty tail, the copied density matrix has trace one. -/
theorem copiedDensity_trace (m : ℕ) (hm : 0 < m) : (copiedDensity m).trace=1 := by
  rw [← reduced_trace,copied_reduced m hm]
  norm_num [Matrix.trace,Fin.sum_univ_two]

/-- The single-system target vector with amplitudes ten and one. -/
def targetAmplitude : Fin 2→ℂ := ![10,1]

/-- The target vector outer product scaled by `1/101`. -/
def targetDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/101:ℝ) • Matrix.vecMulVec targetAmplitude (star targetAmplitude)

/-- The target density has diagonal entries `100/101` and `1/101` and off-diagonal entries
`10/101`. -/
theorem targetDensity_matrix : targetDensity=!![(100/101:ℂ),10/101;10/101,1/101] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [targetDensity,targetAmplitude,Matrix.vecMulVec,map_ofNat]

/-- The single-system target density matrix is positive semidefinite. -/
theorem targetDensity_psd : targetDensity.PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star targetAmplitude).smul (by norm_num : (0:ℝ)≤1/101)

/-- The single-system target density matrix has trace one. -/
theorem targetDensity_trace : targetDensity.trace=1 := by
  rw [targetDensity_matrix]
  norm_num [Matrix.trace,Fin.sum_univ_two]

/-- For a nonempty tail, the reduced copied density minus the target is `-10/101` times the
two-dimensional swap matrix. -/
theorem density_difference (m : ℕ) (hm : 0 < m) :
    reduced (copiedDensity m)-targetDensity=(-10/101:ℂ) • (!![0,1;1,0]:Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [copied_reduced m hm,targetDensity_matrix]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num

/-- The two-dimensional swap matrix has trace norm two. -/
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

/-- For every positive tail size, the reduced copied density differs from the target density by
trace norm `20/101`. -/
theorem forcing_traceNorm_counterexample (m : ℕ) (hm : 0 < m) :
    Matrix.traceNorm (reduced (copiedDensity m)-targetDensity)=20/101 := by
  rw [density_difference m hm,Matrix.traceNorm_smul,swap_traceNorm]
  norm_num [Complex.norm_def]

end Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
