/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.SoftGround
import Qatlib.Papers.OverlapGapGoh26.UniformGrid.ExplicitGrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.SoftGround
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.CubeGround

def coordinate (m : ℕ) (j : Fin (m+1)) : ℝ := -1+2*((j:ℝ)/(m:ℝ))

theorem coordinate_cube {m : ℕ} (hm : 0 < m) (j : Fin (m+1)) : coordinate m j∈Set.Icc (-1:ℝ) 1 := by
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hj : (j:ℝ)≤ m := by exact_mod_cast (show j.val≤ m by omega)
  have hd : (j:ℝ)/(m:ℝ)≤1 := (div_le_one hm').mpr hj
  have hn : 0≤(j:ℝ)/(m:ℝ) := by positivity
  unfold coordinate
  constructor <;> linarith

theorem coordinate_cover {m : ℕ} (hm : 0 < m) (z : ℝ) (hz : z∈Set.Icc (-1:ℝ) 1) :
    ∃ j : Fin (m+1),|z-coordinate m j|≤2/(m:ℝ) := by
  have hτ : (z+1)/2∈Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hz.1,hz.2]
  obtain ⟨σ,hσ,hclose⟩ := Grid.uniformGrid_cover hm ((z+1)/2) hτ
  obtain ⟨j,_hj,rfl⟩ := Finset.mem_image.mp hσ
  refine ⟨j,?_⟩
  have he : z-coordinate m j=2*(((z+1)/2)-(j:ℝ)/(m:ℝ)) := by unfold coordinate; ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left hclose (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

def cubeState {N : ℕ} (m : ℕ) (v : Fin N→Fin (m+1)) : Fin N→ℝ := fun i => coordinate m (v i)

theorem cubeState_mem {N m : ℕ} (hm : 0 < m) (v : Fin N→Fin (m+1)) : cubeState m v∈hilbertCube N :=
  fun i => coordinate_cube hm (v i)

theorem cubeState_card (N m : ℕ) : Fintype.card (Fin N→Fin (m+1))=(m+1)^N := by simp

theorem cubeState_cover {N m : ℕ} (hm : 0 < m) (z : Fin N→ℝ) (hz : z∈hilbertCube N) :
    ∃ v : Fin N→Fin (m+1),
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (cubeState m v)‖≤(2/(m:ℝ))*Real.sqrt (N:ℝ) := by
  choose v hv using fun i => coordinate_cover hm (z i) (hz i)
  refine ⟨v,?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  calc
    _ ≤ ∑ _i : Fin N,(2/(m:ℝ))^2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using! pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
    _ = _ := by simp; ring

def gridMinimum {r N : ℕ} (m : ℕ) (x : Input r N) : ℝ :=
  finiteMin (fun v : Fin N→Fin (m+1) => stateEnergy (cubeState m v) x)

theorem cubeOpt_le_gridMinimum {r N m : ℕ} (hN : 0<N) (hm : 0 < m) (x : Input r N) :
    cubeOpt (sourceTensor (tensorCoords x).ofLp)/(N:ℝ)≤gridMinimum m x := by
  have hn : (0:ℝ)≤N := by exact_mod_cast hN.le
  unfold gridMinimum finiteMin
  apply Finset.le_inf'
  intro v _
  exact div_le_div_of_nonneg_right (cubeOpt_le_energy _ _ (cubeState_mem hm v)) hn

theorem gridMinimum_le_cubeOpt {r N m : ℕ} (hr : 0<r) (hN : 0<N) (hm : 0 < m)
    (x : Input r N) (K : ℝ) (hK : normScale x≤K) :
    gridMinimum m x≤cubeOpt (sourceTensor (tensorCoords x).ofLp)/(N:ℝ)+2*K*((r+1:ℕ):ℝ)/(m:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hsq : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hK0 : 0≤K := le_trans (by dsimp [normScale]; positivity) hK
  obtain ⟨z,hz,hez⟩ := cubeOpt_attained (sourceTensor (tensorCoords x).ofLp)
  obtain ⟨v,hv⟩ := cubeState_cover hm z hz
  have hzc : ∀ i,|(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin N)) i|≤1 := fun i => abs_le.mpr (hz i)
  have hvc : ∀ i,|(WithLp.toLp 2 (cubeState m v) : EuclideanSpace ℝ (Fin N)) i|≤1 :=
    fun i => abs_le.mpr (cubeState_mem hm v i)
  have hs := source_energy_spin_difference hr hN (tensorCoords x)
    (WithLp.toLp 2 z) (WithLp.toLp 2 (cubeState m v)) hzc hvc K hK
  have he : (K*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ))*((2/(m:ℝ))*Real.sqrt (N:ℝ))=
      2*K*((r+1:ℕ):ℝ)/(m:ℝ) := by field_simp
  have hh :=
      hs.trans (mul_le_mul_of_nonneg_left hv (by positivity : 0≤K*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ)))
  rw [he] at hh
  have hfin : gridMinimum m x≤ stateEnergy (cubeState m v) x :=
    Finset.inf'_le (s:=Finset.univ) _ (Finset.mem_univ v)
  change |tensorEnergy (sourceTensor (tensorCoords x).ofLp) z/(N:ℝ)-stateEnergy
      (cubeState m v) x|≤_ at hh
  rw [hez] at hh
  have hlo := (abs_le.mp hh).1
  linarith

def smoothGround {r N : ℕ} (m : ℕ) (β : ℝ) (x : Input r N) : ℝ :=
  softEnergy (β*(N:ℝ)) (cubeState (N:=N) m) x

theorem cube_entropy {N m : ℕ} (hN : 0<N) (β : ℝ) (hβ : 0<β) :
    Real.log (Fintype.card (Fin N→Fin (m+1)):ℝ)/(β*(N:ℝ))=Real.log (m+1:ℝ)/β := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [cubeState_card,Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one]
  field_simp

theorem cubeOpt_entropy_le_smoothGround {r N m : ℕ} (hN : 0<N) (hm : 0 < m)
    (β : ℝ) (hβ : 0<β) (x : Input r N) :
    cubeOpt (sourceTensor (tensorCoords x).ofLp)/(N:ℝ)-Real.log (m+1:ℝ)/β≤ smoothGround m β x := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs := min_sub_entropy_le_softMin (β*(N:ℝ)) (mul_pos hβ hn)
    (fun v : Fin N→Fin (m+1) => stateEnergy (cubeState m v) x)
  rw [cube_entropy hN β hβ] at hs
  exact (sub_le_sub_right (cubeOpt_le_gridMinimum hN hm x) _).trans hs

theorem smoothGround_le_cubeOpt {r N m : ℕ} (hr : 0<r) (hN : 0<N) (hm : 0 < m)
    (β : ℝ) (hβ : 0<β) (x : Input r N) (K : ℝ) (hK : normScale x≤K) :
    smoothGround m β x≤cubeOpt (sourceTensor (tensorCoords x).ofLp)/(N:ℝ)+2*K*((r+1:ℕ):ℝ)/(m:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  exact (softMin_le_min (β*(N:ℝ)) (mul_pos hβ hn)
    (fun v : Fin N→Fin (m+1) => stateEnergy (cubeState m v) x)).trans
    (gridMinimum_le_cubeOpt hr hN hm x K hK)

theorem smoothGround_rotation_tail {r N m : ℕ} (hN : 0<N) (hm : 0 < m)
    (β : ℝ) (hβ : 0<β) (ε : ℝ) (hε : 0<ε) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
      {z | ∃ θ∈Set.Icc (0:ℝ) (Real.pi/2),ε≤|smoothGround m β (ContinuousLinearMap.rotation θ z).1-smoothGround m β z.1|}≤
      Real.pi^2/(4*(N:ℝ)*ε^2) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  exact softEnergy_rotation_tail hN (β*(N:ℝ)) (mul_pos hβ hn) (cubeState m)
    (fun v i => abs_le.mpr (cubeState_mem hm v i)) ε hε

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.CubeGround
