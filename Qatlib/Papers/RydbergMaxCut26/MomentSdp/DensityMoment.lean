/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.GroundBounds
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.GramFactor
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment

noncomputable def moment {I A : Type*} [Fintype I] (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) :
    Matrix A A ℂ := fun a b => ((P a)ᴴ*P b*ρ).trace

noncomputable def realMoment {I A : Type*} [Fintype I] (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) :
    Matrix A A ℝ := fun a b => (moment P ρ a b).re

noncomputable def root {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    Matrix I I ℂ := (HermitianMat.sqrt (⟨ρ,hρ.isHermitian⟩ : HermitianMat I ℂ)).mat

theorem root_hermitian {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    (root ρ hρ)ᴴ=root ρ hρ :=
  (HermitianMat.sqrt (⟨ρ,hρ.isHermitian⟩ : HermitianMat I ℂ)).H

theorem root_square {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    root ρ hρ*root ρ hρ=ρ := HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hρ)

noncomputable def complexRows {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : Matrix (I×I) A ℂ :=
  fun ij a => (P a*root ρ hρ) ij.1 ij.2

theorem root_trace {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef)
    (A B : Matrix I I ℂ) : ((A*root ρ hρ)ᴴ*(B*root ρ hρ)).trace = (Aᴴ*B*ρ).trace := by
  rw [Matrix.conjTranspose_mul,root_hermitian]
  have he : root ρ hρ*Aᴴ*(B*root ρ hρ) = root ρ hρ*(Aᴴ*B)*root ρ hρ := by noncomm_ring
  rw [he,Matrix.trace_mul_cycle,Matrix.trace_mul_comm,root_square]

theorem moment_gram {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    moment P ρ=(complexRows P ρ hρ)ᴴ*complexRows P ρ hρ := by
  ext a b
  rw [moment,← root_trace ρ hρ (P a) (P b)]
  simp only [Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,complexRows,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem moment_posSemidef {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : (moment P ρ).PosSemidef := by
  rw [moment_gram P ρ hρ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

noncomputable def realRows {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : Matrix ((I×I)×Fin 2) A ℝ :=
  fun c a => if c.2=0 then (complexRows P ρ hρ c.1 a).re else (complexRows P ρ hρ c.1 a).im

theorem realMoment_gram {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    realMoment P ρ=(realRows P ρ hρ).transpose*realRows P ρ hρ := by
  ext a b
  simp only [realMoment,moment_gram P ρ hρ,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    realRows,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp [Complex.mul_re,Finset.sum_add_distrib]

theorem realMoment_posSemidef {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : (realMoment P ρ).PosSemidef := by
  rw [realMoment_gram P ρ hρ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem moment_diag {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (hP : ∀ a,(P a)ᴴ*P a=1) (ρ : Matrix I I ℂ) (htr : ρ.trace=1) (a : A) :
    moment P ρ a a=1 := by simp only [moment,hP,Matrix.one_mul,htr]

theorem realMoment_diag {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (hP : ∀ a,(P a)ᴴ*P a=1) (ρ : Matrix I I ℂ) (htr : ρ.trace=1) (a : A) :
    realMoment P ρ a a=1 := by simp only [realMoment,moment_diag P hP ρ htr,Complex.one_re]

theorem realMoment_relation {I A : Type*} [Fintype I]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (a b c d : A) (s : ℝ)
    (hrel : (P a)ᴴ*P b=s • ((P c)ᴴ*P d)) :
    realMoment P ρ a b=s*realMoment P ρ c d := by
  simp [realMoment,moment,hrel,Matrix.trace_smul]
end Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment
