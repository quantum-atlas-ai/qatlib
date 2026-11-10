/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds

noncomputable def sitePauli (n : ℕ) (i : Fin n) (a : Fin 3) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun h => if h=i then pauliMatrix a else 1)

theorem site_hermitian (n : ℕ) (i : Fin n) (a : Fin 3) : (sitePauli n i a)ᴴ=sitePauli n i a := by
  rw [sitePauli,qubitTensor_conjTranspose]
  congr 1
  funext h
  split <;> simp only [axis_adjoint,Matrix.conjTranspose_one]

theorem site_square (n : ℕ) (i : Fin n) (a : Fin 3) : sitePauli n i a*sitePauli n i a=1 := by
  rw [sitePauli,qubitTensor_mul]
  have he : (fun h : Fin n => (if h=i then pauliMatrix a else 1)*(if h=i then pauliMatrix a else 1)) =
      (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext h
    split <;> simp only [axis_square,Matrix.one_mul]
  rw [he,qubitTensor_one]

theorem site_unitary (n : ℕ) (i : Fin n) (a : Fin 3) : (sitePauli n i a)ᴴ*sitePauli n i a=1 := by
  rw [site_hermitian,site_square]

theorem site_pair (n : ℕ) (i j : Fin n) (hij : i≠j) (a : Fin 3) :
    sitePauli n i a*sitePauli n j a=pairPauli i j a := by
  rw [sitePauli,sitePauli,qubitTensor_mul,pairPauli]
  congr 1
  funext h
  by_cases hi : h=i
  · subst h
    simp [hij]
  · by_cases hj : h=j
    · subst h
      simp [hi]
    · simp [hi,hj]

noncomputable def globalUnitary (n : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun _ : Fin n => U)

theorem global_unitary (n : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    globalUnitary n U ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (globalUnitary n U)ᴴ*globalUnitary n U=1
  rw [globalUnitary,qubitTensor_conjTranspose,qubitTensor_mul]
  have he : Uᴴ*U=1 := Matrix.mem_unitaryGroup_iff'.mp hU
  simp_rw [he]
  exact qubitTensor_one n

noncomputable def rotate (n : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n) (Reg n) ℂ := globalUnitary n U*ρ*(globalUnitary n U)ᴴ

theorem rotate_density (n : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) : (rotate n U ρ).PosSemidef ∧ (rotate n U ρ).trace=1 := by
  constructor
  · simpa only [rotate,Matrix.conjTranspose_conjTranspose] using
      hρ.conjTranspose_mul_mul_same ((globalUnitary n U)ᴴ)
  · have hg : (globalUnitary n U)ᴴ*globalUnitary n U=1 := Matrix.mem_unitaryGroup_iff'.mp (global_unitary n U hU)
    rw [rotate,Matrix.trace_mul_cycle,hg,Matrix.one_mul,htr]

theorem rotated_trace (n : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (A ρ : Matrix (Reg n) (Reg n) ℂ) :
    (A*rotate n U ρ).trace = ((globalUnitary n U)ᴴ*A*globalUnitary n U*ρ).trace := by
  have he : A*rotate n U ρ = (A*globalUnitary n U)*ρ*(globalUnitary n U)ᴴ := by
    rw [rotate]
    noncomm_ring
  rw [he,Matrix.trace_mul_cycle]
  congr 1
  noncomm_ring

theorem pair_conjugate (n : ℕ) (i j : Fin n) (hij : i≠j)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (a b : Fin 3) (s : ℂ) (hs : s*s=1) (hact : Uᴴ*pauliMatrix a*U=s • pauliMatrix b) :
    (globalUnitary n U)ᴴ*pairPauli i j a*globalUnitary n U=pairPauli i j b := by
  rw [globalUnitary,pairPauli,qubitTensor_conjTranspose,qubitTensor_mul,qubitTensor_mul]
  have he : (fun h : Fin n => (Uᴴ*(if h=i ∨ h=j then pauliMatrix a else 1))*U) =
      (fun h : Fin n => (if h=i ∨ h=j then s else 1) • (if h=i ∨ h=j then pauliMatrix b else 1)) := by
    funext h
    split
    · exact hact
    · simpa only [Matrix.mul_one,one_smul] using! Matrix.mem_unitaryGroup_iff'.mp hU
  rw [he,qubitTensor_smul]
  have hc : (∏ h : Fin n, if h=i ∨ h=j then s else 1) = 1 := by
    have hf : ∀ h : Fin n, (if h=i ∨ h=j then s else 1) =
        (if h=i then s else 1)*(if h=j then s else 1) := by
      intro h
      by_cases hi : h=i
      · subst h
        simp [hij]
      · by_cases hj : h=j
        · subst h
          simp [hi]
        · simp [hi,hj]
    simp_rw [hf]
    rw [Finset.prod_mul_distrib]
    simpa using hs
  rw [hc,one_smul]
  rfl

noncomputable def phase : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,Complex.I]

theorem phase_unitary : phase ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phase,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem phase_x : phaseᴴ*pauliMatrix 0*phase=(-1:ℂ) • pauliMatrix 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phase,pauliMatrix,pauliX,pauliY,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem phase_y : phaseᴴ*pauliMatrix 1*phase=pauliMatrix 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phase,pauliMatrix,pauliX,pauliY,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem phase_z : phaseᴴ*pauliMatrix 2*phase=pauliMatrix 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phase,pauliMatrix,pauliZ,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem phase_corr_x (n : ℕ) (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    corr (rotate n phase ρ) i j 0=corr ρ i j 1 := by
  rw [corr,rotated_trace,pair_conjugate n i j hij phase phase_unitary 0 1 (-1) (by norm_num) phase_x]
  rfl

theorem phase_corr_y (n : ℕ) (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    corr (rotate n phase ρ) i j 1=corr ρ i j 0 := by
  rw [corr,rotated_trace,pair_conjugate n i j hij phase phase_unitary 1 0 1 (by norm_num) (by simpa using phase_y)]
  rfl

theorem phase_corr_z (n : ℕ) (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    corr (rotate n phase ρ) i j 2=corr ρ i j 2 := by
  rw [corr,rotated_trace,pair_conjugate n i j hij phase phase_unitary 2 2 1 (by norm_num) (by simpa using phase_z)]
  rfl
end Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation
