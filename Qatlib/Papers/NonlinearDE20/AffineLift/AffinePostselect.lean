/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.AffineLift.TensorSumEvolution
import Mathlib.LinearAlgebra.Matrix.PosDef
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Model

def bornMass {J : Type} [Fintype J] (v : J→ℂ) : ℝ :=∑ j,Complex.normSq (v j)

theorem tensorPower_bornMass {J : Type} [Fintype J] (n : ℕ) (y : J→ℂ) :
    bornMass (tensorPower n y)=(bornMass y)^n := by
  unfold bornMass tensorPower
  simp_rw [map_prod]
  have h := Finset.prod_univ_sum (κ:=fun _ : Fin n=>J) (t:=fun _=>Finset.univ)
    (f:=fun _ j=>Complex.normSq (y j))
  rw [Fintype.piFinset_univ] at h
  simpa only [Finset.prod_const,Fintype.card_fin,Finset.card_univ] using h.symm

def branchEmbedding {I : Type} (n : ℕ) (u : Fin n→I) : Fin n→Option I :=fun k=>some (u k)

theorem branchEmbedding_injective {I : Type} (n : ℕ) : Function.Injective (branchEmbedding (I:=I) n) := by
  intro u v h
  funext k
  exact Option.some.inj (congrFun h k)

def branchSelector {I : Type} [DecidableEq I] (n : ℕ) : Matrix (Fin n→I) (Fin n→Option I) ℂ :=
  fun u v=>if v=branchEmbedding n u then 1 else 0

theorem branchSelector_action {I : Type} [Fintype I] [DecidableEq I] (n : ℕ)
    (v : (Fin n→Option I)→ℂ) (u : Fin n→I) :
    (branchSelector n*ᵥ v) u=v (branchEmbedding n u) := by
  simp [Matrix.mulVec,dotProduct,branchSelector,ite_mul]

theorem branchSelector_coisometry {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) :
    branchSelector (I:=I) n*(branchSelector (I:=I) n)ᴴ=1 := by
  ext u v
  simp [Matrix.mul_apply,branchSelector,Matrix.conjTranspose_apply,mul_ite,Matrix.one_apply,eq_comm,
    (branchEmbedding_injective (I:=I) n).eq_iff]

theorem homogeneous_branch {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (x : I→ℂ) :
    branchSelector n*ᵥ tensorPower n (homogenize x)=tensorPower n x := by
  funext u
  rw [branchSelector_action]
  rfl

theorem homogeneous_tensor_mass {I : Type} [Fintype I] (n : ℕ) (x : I→ℂ) :
    bornMass (tensorPower n (homogenize x))=(1+bornMass x)^n := by
  rw [tensorPower_bornMass]
  congr 1
  exact homogenize_normSq x

theorem homogeneous_branch_probability {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (x : I→ℂ) :
    bornMass (branchSelector n*ᵥ tensorPower n (homogenize x))/bornMass (tensorPower n (homogenize x))=
      (bornMass x/(1+bornMass x))^n := by
  rw [homogeneous_branch,tensorPower_bornMass,homogeneous_tensor_mass,div_pow]

def normalizedOuter {J : Type} [Fintype J] (v : J→ℂ) : Matrix J J ℂ :=
  (bornMass v)⁻¹ • Matrix.vecMulVec v (star v)

theorem normalizedOuter_psd {J : Type} [Fintype J] (v : J→ℂ) : (normalizedOuter v).PosSemidef := by
  apply (Matrix.posSemidef_vecMulVec_self_star v).smul
  exact inv_nonneg.mpr (Finset.sum_nonneg (fun j _=>Complex.normSq_nonneg (v j)))

theorem outer_trace {J : Type} [Fintype J] (v : J→ℂ) :
    (Matrix.vecMulVec v (star v)).trace=(bornMass v:ℂ) := by
  simp [Matrix.trace,Matrix.vecMulVec,Complex.mul_conj,bornMass]

theorem normalizedOuter_trace {J : Type} [Fintype J] (v : J→ℂ) (hv : 0<bornMass v) :
    (normalizedOuter v).trace=1 := by
  rw [normalizedOuter,Matrix.trace_smul,outer_trace]
  apply Complex.ext
  · simp only [Complex.smul_re,Complex.ofReal_re,smul_eq_mul,Complex.one_re]
    exact inv_mul_cancel₀ hv.ne'
  · simp

theorem homogeneous_conditional_density {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (x : I→ℂ) :
    normalizedOuter (branchSelector n*ᵥ tensorPower n (homogenize x))=normalizedOuter (tensorPower n x) := by
  rw [homogeneous_branch]

end Qatlib.Papers.NonlinearDE20.AffineLift.Model
