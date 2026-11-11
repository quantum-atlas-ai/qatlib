/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.ForcingModel.ForcingHistoryBridge

/-!
# Clock selection and normalized postselection

The matrix `clockSelector` extracts a fixed clock slice from a finite history vector. The module
proves its coisometry and outer-product identities, then shows that normalizing the selected
block agrees with `conditionSlice`. The explicit `singleEulerTarget` connects this readout to
the forcing example for the history construction of [LloydEtAl2020].

## Main statements

* `clockSelector_coisometry`: The clock selector multiplied by its conjugate transpose is the
  identity on the system space.
* `normalized_clock_condition`: For a history outer product with positive real trace, normalized
  clock postselection equals the normalized outer product of the selected slice.
* `targetDensity_singleEuler`: The target density matrix is the normalized outer product of
  `singleEulerTarget`.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
open Qatlib.Papers.NonlinearDE20.HistorySystem.History

/-- The coordinate selector that extracts the system vector at clock value `k`. -/
def clockSelector {J : Type} [DecidableEq J] (N : ℕ) (k : Fin N) : Matrix J (Fin N×J) ℂ :=
  fun i p=>if p=(k,i) then 1 else 0

/-- Applying `clockSelector` to a history vector returns its slice at clock value `k`. -/
theorem clockSelector_action {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N)
    (X : Fin N×J→ℂ) (i : J) : (clockSelector (J:=J) N k*ᵥ X) i=X (k,i) := by
  simp [Matrix.mulVec,dotProduct,clockSelector,ite_mul]

/-- The clock selector multiplied by its conjugate transpose is the identity on the system
space. -/
theorem clockSelector_coisometry {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N) :
    clockSelector (J:=J) N k*(clockSelector (J:=J) N k)ᴴ=1 := by
  ext i j
  simp [Matrix.mul_apply,clockSelector,Matrix.conjTranspose_apply,mul_ite,Matrix.one_apply,eq_comm]

/-- Selecting both sides of a history outer product gives the outer product of the selected
clock slice. -/
theorem clockSelector_outer {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N) (X : Fin N×J→ℂ) :
    clockSelector (J:=J) N k*sliceOuter X*(clockSelector (J:=J) N k)ᴴ=sliceOuter (fun i=>X (k,i)) := by
  ext i j
  simp [Matrix.mul_apply,clockSelector,Matrix.conjTranspose_apply,sliceOuter,Matrix.vecMulVec,
    mul_ite,ite_mul]

/-- Rescale a matrix by the reciprocal of the real part of its trace. -/
def normalizeMatrix {J : Type} [Fintype J] (ρ : Matrix J J ℂ) : Matrix J J ℂ :=ρ.trace.re⁻¹ •ρ

/-- Trace normalization is invariant under multiplication by a nonzero real scalar. -/
theorem normalizeMatrix_smul {J : Type} [Fintype J] (ρ : Matrix J J ℂ) (a : ℝ) (ha : a≠0) :
    normalizeMatrix (a •ρ)=normalizeMatrix ρ := by
  rw [normalizeMatrix,Matrix.trace_smul,Complex.smul_re,smul_eq_mul,smul_smul,normalizeMatrix]
  congr 1
  rw [_root_.mul_inv_rev,mul_assoc,inv_mul_cancel₀ ha,mul_one]

/-- For a history outer product with positive real trace, normalized clock postselection equals
the normalized outer product of the selected slice. -/
theorem normalized_clock_condition {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (k : Fin N)
    (X : Fin N×J→ℂ) (hX : 0<(sliceOuter X).trace.re) :
    normalizeMatrix (clockSelector (J:=J) N k*normalizeMatrix (sliceOuter X)*(clockSelector (J:=J) N k)ᴴ)=
      conditionSlice (fun i=>X (k,i)) := by
  change normalizeMatrix
      (clockSelector (J:=J) N k*((sliceOuter X).trace.re⁻¹ •sliceOuter X)*(clockSelector (J:=J) N k)ᴴ)=_
  rw [Matrix.mul_smul,Matrix.smul_mul,normalizeMatrix_smul _ _ (inv_ne_zero hX.ne'),clockSelector_outer]
  rfl

/-- The two-component Euler target with amplitudes `1` and `1/10`. -/
def singleEulerTarget : Fin 2→ℂ :=basis 0+(1/10:ℂ) •basis 1

/-- The target density matrix is the normalized outer product of `singleEulerTarget`. -/
theorem targetDensity_singleEuler : targetDensity=conditionSlice singleEulerTarget := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [targetDensity,targetAmplitude,conditionSlice,sliceOuter,Matrix.trace,Matrix.vecMulVec,
      Fin.sum_univ_two,singleEulerTarget,basis,map_ofNat]

end Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
