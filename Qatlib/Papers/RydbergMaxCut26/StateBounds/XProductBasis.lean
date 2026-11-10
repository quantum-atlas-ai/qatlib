/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Hamiltonian
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open Qatlib.Concepts.ShadowModels.ShadowChannel
open scoped Classical ComplexOrder
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment

namespace Qatlib.Papers.RydbergMaxCut26.StateBounds.XBasis

def localHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

theorem localHadamard_adjoint : localHadamardᴴ=localHadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localHadamard,Matrix.conjTranspose_apply]

theorem localHadamard_square : localHadamard*localHadamard=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localHadamard,Matrix.mul_apply,Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [sqrt2_sq]

theorem localHadamard_unitary : localHadamard∈Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [show star localHadamard=localHadamard from localHadamard_adjoint]
  exact localHadamard_square

theorem x_leaf_operator (b : Bool) :
    localHadamardᴴ*Projector {if b then (0 : Fin 2) else 1}*localHadamard=PauliProjector 0 b := by
  rw [localHadamard_adjoint]
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [localHadamard,Projector,PauliProjector,pauliMatrix,pauliX,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.diagonal_apply] <;>
    ring_nf <;> norm_num [sqrt2_sq]

theorem x_projector_square (b : Bool) : PauliProjector 0 b*PauliProjector 0 b=PauliProjector 0 b := by
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [PauliProjector,pauliMatrix,pauliX,Matrix.mul_apply,Fin.sum_univ_two]

def sign (b : Bool) : ℝ := if b then 1 else -1

def xVector (b : Bool) : Fin 3 → ℝ := fun a => if a=0 then sign b else 0

theorem local_x_projector (b : Bool) : bloch (xVector b)=PauliProjector 0 b := by
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bloch,xVector,sign,PauliProjector,pauliMatrix,pauliX] <;> decide

def xDensity {n : ℕ} (s : Reg n) : Matrix (Reg n) (Reg n) ℂ :=
  productState (fun i => xVector (s i))

theorem x_density {n : ℕ} (s : Reg n) : (xDensity s).PosSemidef ∧ (xDensity s).trace=1 := by
  apply product_density
  intro i
  cases h : s i <;> norm_num [sqnorm,xVector,sign,h,Fin.sum_univ_three]

theorem x_density_tensor {n : ℕ} (s : Reg n) :
    xDensity s=qubitTensor (fun i => PauliProjector 0 (s i)) := by
  unfold xDensity productState
  simp_rw [local_x_projector]

theorem x_resolution (n : ℕ) : (∑ s : Reg n,xDensity s)=1 := by
  simp_rw [x_density_tensor]
  rw [qubitTensor_sum]
  simp_rw [pauliProjector_sum]
  exact qubitTensor_one n

theorem x_hermitian {n : ℕ} (s : Reg n) : (xDensity s)ᴴ=xDensity s :=
  (x_density s).1.isHermitian

theorem x_square {n : ℕ} (s : Reg n) : xDensity s*xDensity s=xDensity s := by
  rw [x_density_tensor,qubitTensor_mul]
  simp_rw [x_projector_square]

def computationalProjector {n : ℕ} (s : Reg n) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun i => Projector {if s i then (0 : Fin 2) else 1})

theorem tensor_hadamard_unitary (n : ℕ) :
    globalUnitary n (localHadamard)∈Matrix.unitaryGroup (Reg n) ℂ :=
  global_unitary n _ (localHadamard_unitary)

theorem actual_x_basis {n : ℕ} (s : Reg n) :
    (globalUnitary n (localHadamard))ᴴ*computationalProjector s*
      globalUnitary n (localHadamard)=xDensity s := by
  rw [globalUnitary,computationalProjector,qubitTensor_conjTranspose,
    qubitTensor_mul,qubitTensor_mul,x_density_tensor]
  simp_rw [x_leaf_operator]

theorem local_x_eigen (b : Bool) :
    pauliMatrix 0*PauliProjector 0 b=(sign b:ℂ) • PauliProjector 0 b := by
  rw [PauliProjector,Matrix.mul_smul,Matrix.mul_add,Matrix.mul_one,Matrix.mul_smul,axis_square]
  cases b <;> norm_num [sign] <;> module

theorem pair_x_eigen {n : ℕ} (s : Reg n) (i j : Fin n) (hij : i≠j) :
    pairPauli i j 0*xDensity s=(sign (s i)*sign (s j):ℝ) • xDensity s := by
  rw [pairPauli,x_density_tensor,qubitTensor_mul]
  have he : (fun h : Fin n => (if h=i ∨ h=j then pauliMatrix 0 else 1)*PauliProjector 0 (s h))=
      (fun h : Fin n => ((if h=i then (sign (s i):ℂ) else 1)*
        (if h=j then (sign (s j):ℂ) else 1)) • PauliProjector 0 (s h)) := by
    funext h
    by_cases hi : h=i
    · subst h
      simpa only [true_or,ite_true,ite_false,hij,mul_one] using! local_x_eigen (s i)
    · by_cases hj : h=j
      · subst h
        simpa only [or_true,ite_true,ite_false,hi,one_mul] using! local_x_eigen (s j)
      · simp [hi,hj]
  rw [he,qubitTensor_smul,Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,if_true]
  ext x y
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul]

theorem local_x_orthogonal (b c : Bool) (hbc : b≠c) :
    PauliProjector 0 b*PauliProjector 0 c=0 := by
  ext i j
  cases b <;> cases c <;> fin_cases i <;> fin_cases j <;>
    simp_all [PauliProjector,pauliMatrix,pauliX,Matrix.mul_apply,Fin.sum_univ_two]

theorem x_orthogonal {n : ℕ} (s u : Reg n) (hsu : s≠u) : xDensity s*xDensity u=0 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hsu
  rw [x_density_tensor,x_density_tensor,qubitTensor_mul]
  ext x y
  change (∏ j : Fin n,(PauliProjector 0 (s j)*PauliProjector 0 (u j))
    (boolEquivFin2 (x j)) (boolEquivFin2 (y j)))=0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [local_x_orthogonal (s i) (u i) hi]
  rfl

theorem x_correlations {n : ℕ} (s : Reg n) (i j : Fin n) (hij : i≠j) :
    corr (xDensity s) i j 0=sign (s i)*sign (s j) ∧
      corr (xDensity s) i j 1=0 ∧ corr (xDensity s) i j 2=0 := by
  simp only [corr,xDensity,pair_product_trace _ i j hij]
  norm_num [xVector,show (2:Fin 3)≠0 by decide]

theorem x_born_nonneg {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (s : Reg n) :
    0≤(xDensity s*ρ).trace.re := by
  have hp := (moment_posSemidef (fun u : Reg n => xDensity u) ρ hρ).diag_nonneg (i:=s)
  have hr := (RCLike.nonneg_iff.mp hp).1
  simpa only [moment,Matrix.diag_apply,x_hermitian,x_square] using! hr

theorem x_born_sum {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (htr : ρ.trace=1) :
    (∑ s : Reg n,(xDensity s*ρ).trace.re)=1 := by
  rw [← Complex.re_sum,← Matrix.trace_sum,← Matrix.sum_mul,x_resolution,Matrix.one_mul,htr]
  rfl

end Qatlib.Papers.RydbergMaxCut26.StateBounds.XBasis
