/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.CubeRounding
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open scoped Classical
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTail
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

theorem binarySpin_cube {N:ℕ} (b:Fin N→Bool) : binarySpin b∈hilbertCube N := by
  intro i
  unfold binarySpin
  cases b i <;>norm_num

theorem cubeOpt_le_binaryGround {q N:ℕ} (A:Tensor q N) : cubeOpt A≤binaryGround A := by
  obtain ⟨b,hb⟩:=binaryGround_attained A
  exact (cubeOpt_le_energy A (binarySpin b) (binarySpin_cube b)).trans_eq hb

theorem optimum_gap_bound {q N:ℕ} (A:Tensor q N) (ε:ℝ)
    (hR:∀u∈hilbertCube N,|tensorEnergy (repeated A) u|≤ε) :
    0≤binaryGround A-cubeOpt A ∧ binaryGround A-cubeOpt A≤2*ε := by
  refine ⟨sub_nonneg.mpr (cubeOpt_le_binaryGround A),?_⟩
  obtain ⟨u,hu,heu⟩:=cubeOpt_attained A
  obtain ⟨b,heb⟩:=binaryGround_attained (noRepeat A)
  have hnr:tensorEnergy (noRepeat A) (binarySpin b)≤tensorEnergy (noRepeat A) u := by
    rw [heb,← noRepeat_cube_eq_binary A]
    exact cubeOpt_le_energy (noRepeat A) u hu
  have hb:=binaryGround_le_energy A b
  have hru:=abs_le.mp (hR u hu)
  have hrb:=abs_le.mp (hR (binarySpin b) (binarySpin_cube b))
  have he1:=energy_decomposition A u
  have he2:=energy_decomposition A (binarySpin b)
  rw [heu] at he1
  linarith

theorem optimum_gap_inclusion {q N:ℕ} (ε:ℝ) :
    {A:Tensor q N|2*ε<binaryGround A-cubeOpt A}⊆
      {A|∃u∈hilbertCube N,ε≤|tensorEnergy (repeated A) u|} := by
  intro A hA
  simp only [Set.mem_setOf_eq] at hA ⊢
  by_contra! hbad
  have h:= (optimum_gap_bound A ε (fun u hu=>(hbad u hu).le)).2
  linarith
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
