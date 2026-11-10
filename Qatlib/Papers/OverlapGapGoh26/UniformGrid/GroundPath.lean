/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.CubeGround
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.CubeGround
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.GroundPath

def ground {r N : ℕ} (x : Input r N) : ℝ := cubeOpt (sourceTensor (tensorCoords x).ofLp)/(N:ℝ)

theorem approximation_parameters (r : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ m : ℕ,∃ β : ℝ,0 < m ∧ 0<β ∧
      4*normBound r*((r+1:ℕ):ℝ)/(m:ℝ)≤ε/4 ∧ Real.log (m+1:ℝ)/β≤ε/4 := by
  let m := Nat.ceil (16*normBound r*((r+1:ℕ):ℝ)/ε)+1
  have hm : 0 < m := by dsimp [m]; omega
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hmesh : 16*normBound r*((r+1:ℕ):ℝ)/ε≤(m:ℝ) := by
    calc
      _ ≤ (Nat.ceil (16*normBound r*((r+1:ℕ):ℝ)/ε):ℝ) := Nat.le_ceil _
      _ ≤ (Nat.ceil (16*normBound r*((r+1:ℕ):ℝ)/ε):ℝ)+1 := by linarith
      _ = _ := by simp only [m,Nat.cast_add,Nat.cast_one]
  have hmesh' := (div_le_iff₀ hε).mp hmesh
  have hfirst : 4*normBound r*((r+1:ℕ):ℝ)/(m:ℝ)≤ε/4 := by
    apply (div_le_iff₀ hm').mpr
    nlinarith
  have hlog : 0≤Real.log (m+1:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤ m+1 by omega))
  let β := 1+4*Real.log (m+1:ℝ)/ε
  have hβ : 0<β := by dsimp [β]; positivity
  have hcalc : (ε/4)*β=Real.log (m+1:ℝ)+ε/4 := by dsimp [β]; field_simp; ring
  refine ⟨m,β,hm,hβ,hfirst,?_⟩
  apply (div_le_iff₀ hβ).mpr
  rw [hcalc]
  linarith

theorem smoothGround_approx {r N m : ℕ} (hr : 0<r) (hN : 0<N) (hm : 0 < m)
    (β ε : ℝ) (hβ : 0<β)
    (hmesh : 4*normBound r*((r+1:ℕ):ℝ)/(m:ℝ)≤ε/4)
    (hentropy : Real.log (m+1:ℝ)/β≤ε/4) (x : Input r N) (hx : normScale x≤2*normBound r) :
    |smoothGround m β x-ground x|≤ε/4 := by
  have hlo := cubeOpt_entropy_le_smoothGround hN hm β hβ x
  have hhi := smoothGround_le_cubeOpt hr hN hm β hβ x (2*normBound r) hx
  have hh : 2*(2*normBound r)*((r+1:ℕ):ℝ)/(m:ℝ)≤ε/4 := by convert! hmesh using 1; ring
  unfold ground
  apply abs_le.mpr
  constructor <;> linarith

theorem actual_ground_continuum_tail {r N : ℕ} (hr : 0<r) (hN : 0<N) (ε : ℝ) (hε : 0<ε) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
      {w | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|ground (inputPath w.1 w.2 τ)-ground w.1|}≤
      4*Real.exp (-(N:ℝ))+Real.pi^2/((N:ℝ)*ε^2) := by
  obtain ⟨m,β,hm,hβ,hmesh,hentropy⟩ := approximation_parameters r ε hε
  let D := {w : Input r N×Input r N | ∃ θ∈Set.Icc (0:ℝ) (Real.pi/2),
    ε/2≤|smoothGround m β (ContinuousLinearMap.rotation θ w).1-smoothGround m β w.1|}
  have hsub : {w : Input r N×Input r N | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|ground (inputPath w.1 w.2 τ)-ground w.1|}⊆
      (pairRegion r N)ᶜ∪D := by
    rintro w ⟨τ,hτ,hbad⟩
    by_cases hw : w∈pairRegion r N
    · right
      have hτnorm := normScale_inputPath w.1 w.2 (normBound r) hw.1 hw.2 τ hτ
      have h0norm : normScale w.1≤2*normBound r := by linarith [hw.1,normBound_pos r]
      have hτapprox :=
          smoothGround_approx hr hN hm β ε hβ hmesh hentropy (inputPath w.1 w.2 τ) hτnorm
      have h0approx := smoothGround_approx hr hN hm β ε hβ hmesh hentropy w.1 h0norm
      have htri :=
          abs_sub_le (ground (inputPath w.1 w.2 τ)) (smoothGround m β (inputPath w.1 w.2 τ))
          (ground w.1)
      have htri' :=
          abs_sub_le (smoothGround m β (inputPath w.1 w.2 τ)) (smoothGround m β w.1) (ground w.1)
      rw [abs_sub_comm (ground (inputPath w.1 w.2 τ)) (smoothGround m β (inputPath w.1 w.2 τ))] at htri
      refine ⟨Real.arcsin (Real.sqrt τ),inputPath_angle τ,?_⟩
      change ε/2≤|smoothGround m β
          (ContinuousLinearMap.rotation (Real.arcsin (Real.sqrt τ)) w).1-smoothGround m β w.1|
      rw [← inputPath_rotation w.1 w.2 τ hτ]
      linarith
    · exact Or.inl hw
  refine ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans ?_
  have htail := smoothGround_rotation_tail (r:=r) hN hm β hβ (ε/2) (by positivity)
  exact (add_le_add (pairRegion_failure hr hN) htail).trans_eq (by ring)

theorem ground_lipschitz {r N : ℕ} (hN : 0<N) :
    LipschitzWith (⟨1/Real.sqrt (N:ℝ),by positivity⟩ : ℝ≥0) (ground (r:=r) (N:=N)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hs := normalized_ground_transport_sq (r:=r) hN (tensorCoords x).ofLp (tensorCoords y).ofLp
  have he : (∑ k,((tensorCoords x).ofLp k-(tensorCoords y).ofLp k)^2)=‖tensorCoords x-tensorCoords y‖^2 :=
    (EuclideanSpace.real_norm_sq_eq (tensorCoords x-tensorCoords y)).symm
  rw [he] at hs
  have hh := Real.abs_le_sqrt hs
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] at hh
  have hp := input_split_sq x y
  have hg : ‖tensorCoords x-tensorCoords y‖≤‖x-y‖ := by
    nlinarith [norm_nonneg (tensorCoords x-tensorCoords y),norm_nonneg (x-y),
      sq_nonneg ‖(WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (seedCoords y)‖]
  have hb := hh.trans (div_le_div_of_nonneg_right hg (Real.sqrt_nonneg _))
  simpa only [Real.dist_eq,dist_eq_norm,div_eq_mul_inv,one_mul,mul_comm,ground] using! hb

theorem sourceTensor_input_neg {r N : ℕ} (x : Input r N) :
    sourceTensor (tensorCoords (-x)).ofLp= -(sourceTensor (tensorCoords x).ofLp) := by
  funext k
  change Real.sqrt (((N:ℝ)^r)⁻¹)*(-x (Sum.inl k))= -(Real.sqrt (((N:ℝ)^r)⁻¹)*x (Sum.inl k))
  ring

theorem inputPath_neg {r N : ℕ} (x y : Input r N) (τ : ℝ) :
    inputPath (-x) (-y) τ= -(inputPath x y τ) := by
  unfold inputPath
  module

def maximum {r N : ℕ} (x : Input r N) : ℝ := -ground (-x)

theorem maximum_formula {r N : ℕ} (x : Input r N) :
    maximum x= -cubeOpt (-(sourceTensor (tensorCoords x).ofLp))/(N:ℝ) := by
  unfold maximum ground
  rw [sourceTensor_input_neg]
  ring

theorem input_neg_preserving (r N : ℕ) : MeasurePreserving (fun x : Input r N => -x)
    (stdGaussian (Input r N)) (stdGaussian (Input r N)) :=
  ⟨by fun_prop,stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩

theorem actual_maximum_continuum_tail {r N : ℕ} (hr : 0<r) (hN : 0<N) (ε : ℝ) (hε : 0<ε) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
      {w | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|maximum (inputPath w.1 w.2 τ)-maximum w.1|}≤
      4*Real.exp (-(N:ℝ))+Real.pi^2/((N:ℝ)*ε^2) := by
  let D :=
      {w : Input r N×Input r N | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|ground (inputPath w.1 w.2 τ)-ground w.1|}
  let f := fun w : Input r N×Input r N => (-w.1,-w.2)
  have hm := (input_neg_preserving r N).prod (input_neg_preserving r N)
  have hsub : {w : Input r N×Input r N | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|maximum (inputPath w.1 w.2 τ)-maximum w.1|}⊆f⁻¹' D := by
    rintro w ⟨τ,hτ,h⟩
    refine ⟨τ,hτ,?_⟩
    change ε≤|ground (inputPath (-w.1) (-w.2) τ)-ground (-w.1)|
    have he : maximum (inputPath w.1 w.2 τ)-maximum w.1=
        -(ground (inputPath (-w.1) (-w.2) τ)-ground (-w.1)) := by
      unfold maximum
      rw [inputPath_neg]
      ring
    rw [he,abs_neg] at h
    exact h
  have hmap :=
      Measure.le_map_apply
      (μ:=(stdGaussian (Input r N)).prod (stdGaussian (Input r N))) hm.measurable.aemeasurable D
  rw [hm.map_eq] at hmap
  have hreal := ENNReal.toReal_mono (by finiteness) hmap
  exact ((measureReal_mono hsub).trans hreal).trans (actual_ground_continuum_tail hr hN ε hε)

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.GroundPath
