/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Papers.AdiabaticQLS23.MainResults.BlockEncoding
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults.SourceCircuit
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
variable {W : Type} [Fintype W] [DecidableEq W]

noncomputable def sourceReflection (Ub : Matrix W W ℂ) (seed : W) : Matrix W W ℂ :=
  -(Ub * ReflectionAbout (outerProduct (Ket seed)) * Ubᴴ)

theorem sourceReflection_unitary (Ub : Matrix W W ℂ) (seed : W)
    (hUb : Ub ∈ Matrix.unitaryGroup W ℂ) :
    sourceReflection Ub seed ∈ Matrix.unitaryGroup W ℂ := by
  have h : Ub * ReflectionAbout (outerProduct (Ket seed)) * Ubᴴ ∈
      Matrix.unitaryGroup W ℂ :=
    (Matrix.unitaryGroup W ℂ).mul_mem
      ((Matrix.unitaryGroup W ℂ).mul_mem hUb
        (outerProduct_reflection_unitary (normalized_ket seed))) (adjoint_unitary hUb)
  rw [sourceReflection, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_neg, neg_mul_neg]
  simpa only [Matrix.star_eq_conjTranspose] using h.1

theorem sourceReflection_eq (Ub : Matrix W W ℂ) (seed : W)
    (hUb : Ub ∈ Matrix.unitaryGroup W ℂ) :
    sourceReflection Ub seed = 1 - (2:ℂ) • outerProduct (Ub *ᵥ Ket seed) := by
  have h := (prepared_aa_reflection_and_access Ub seed ∅ hUb).2.2.1
  rw [sourceReflection, h]
  simp only [ReflectionAbout, preparedAAState, ApplyGate]
  module

def cleanFrame {A D : Type} [DecidableEq A] [DecidableEq D] (seed : A) :
    Matrix (A × D) D ℂ := fun p i => if p.1=seed then if p.2=i then 1 else 0 else 0

theorem cleanFrame_isometry {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (seed : A) :
    (cleanFrame (D:=D) seed)ᴴ * cleanFrame (D:=D) seed = (1 : Matrix D D ℂ) := by
  ext i j
  simp [cleanFrame,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,
    Matrix.one_apply, apply_ite]
  split_ifs <;> aesop

theorem compress_cleanFrame {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (seed : A) (U : Matrix (A × D) (A × D) ℂ) (i j : D) :
    compress (cleanFrame seed) U (cleanFrame seed) i j = U (seed,i) (seed,j) := by
  simp [compress,cleanFrame,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, apply_ite, ite_mul]

theorem encoding_of_corner {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix (A × W) (A × W) ℂ) (seed : A) (M : Matrix W W ℂ)
    (hU : U ∈ Matrix.unitaryGroup (A × W) ℂ)
    (hc : ∀ i j, U (seed,i) (seed,j) = M i j) :
    ProjectedUnitaryEncoding M U (cleanFrame seed) (cleanFrame seed) := by
  refine ⟨hU, cleanFrame_isometry seed, cleanFrame_isometry seed, ?_⟩
  ext i j
  rw [compress_cleanFrame]
  exact hc i j

def layout {A N : Type} :
    (Fin 2 × (Fin 2 × (Fin 2 × (A × N)))) ≃
      ((Fin 2 × (Fin 2 × A)) × (Fin 2 × N)) where
  toFun p := ((p.1,(p.2.1,p.2.2.2.1)),(p.2.2.1,p.2.2.2.2))
  invFun p := (p.1.1,(p.1.2.1,(p.2.1,(p.1.2.2,p.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

theorem encoding_of_raw_corner {A N : Type} [Fintype A] [DecidableEq A]
    [Fintype N] [DecidableEq N]
    (U : Matrix (Fin 2 × (Fin 2 × (Fin 2 × (A × N))))
      (Fin 2 × (Fin 2 × (Fin 2 × (A × N)))) ℂ)
    (a0 : A) (M : Matrix (Fin 2 × N) (Fin 2 × N) ℂ)
    (hU : U ∈ Matrix.unitaryGroup _ ℂ)
    (hc : ∀ h k i j, U (0,(0,(h,(a0,i)))) (0,(0,(k,(a0,j)))) = M (h,i) (k,j)) :
    ProjectedUnitaryEncoding M (Matrix.reindex layout layout U)
      (cleanFrame (0,(0,a0))) (cleanFrame (0,(0,a0))) := by
  apply encoding_of_corner
  · exact unitaryGroup_reindex layout hU
  · intro i j
    exact hc i.1 j.1 i.2 j.2

theorem sourceReflection_eq_rankOne (Ub : Matrix W W ℂ) (seed : W)
    (hUb : Ub ∈ Matrix.unitaryGroup W ℂ) :
    sourceReflection Ub seed = 1-(2:ℂ) • rankOne (Ub *ᵥ Ket seed) := by
  simpa only [outerProduct, rankOne] using! sourceReflection_eq Ub seed hUb

end Qatlib.Papers.AdiabaticQLS23.MainResults.SourceCircuit
