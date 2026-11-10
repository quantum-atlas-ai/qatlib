/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorNormProbability
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorNormProbability

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion

theorem tensorForm_linear {q N : ℕ} (a b : ℝ) (A B : Tensor q N) :
    tensorForm (fun k => a*A k+b*B k)=a•tensorForm A+b•tensorForm B := by
  simp only [tensorForm,add_smul,mul_smul,Finset.sum_add_distrib,Finset.smul_sum]

theorem normScale_inputPath {r N : ℕ} (x y : Input r N) (K : ℝ)
    (hx : normScale x≤K) (hy : normScale y≤K) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    normScale (inputPath x y τ)≤2*K := by
  let a := Real.sqrt (1-τ)
  let b := Real.sqrt τ
  have ha : 0≤a := Real.sqrt_nonneg _
  have hb : 0≤b := Real.sqrt_nonneg _
  have ha1 : a≤1 := Real.sqrt_le_one.mpr (by linarith [hτ.1])
  have hb1 : b≤1 := Real.sqrt_le_one.mpr hτ.2
  have hK : 0≤K := le_trans (by dsimp [normScale]; positivity) hx
  have hf : tensorForm (sourceTensor (tensorCoords (inputPath x y τ)).ofLp)=
      a•tensorForm (sourceTensor (tensorCoords x).ofLp)+b•tensorForm (sourceTensor (tensorCoords y).ofLp) := by
    rw [source_tensor_path]
    exact tensorForm_linear a b _ _
  unfold normScale
  rw [hf]
  calc
    _ ≤ (‖a•tensorForm (sourceTensor (tensorCoords x).ofLp)‖+
      ‖b•tensorForm (sourceTensor (tensorCoords y).ofLp)‖)*(Real.sqrt (N:ℝ))^(r-1) :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = a*normScale x+b*normScale y := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
      unfold normScale
      ring
    _ ≤ a*K+b*K := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ ≤ _ := by nlinarith

theorem normScale_measurable (r N : ℕ) : Measurable (normScale (r:=r) (N:=N)) :=
  (normalizedNorm_continuous r N).measurable.comp (actual_tensor_preserving r N).measurable

def normBound (r : ℕ) : ℝ := 1+|goodNormConstant r|

theorem normBound_pos (r : ℕ) : 0 < normBound r := by unfold normBound; positivity

theorem normScale_good_tail {r N : ℕ} (hr : 0<r) (hN : 0<N) :
    (stdGaussian (Input r N)).real {x | goodNormConstant r < normScale x}≤2*Real.exp (-(N:ℝ)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hS : 0 < (Real.sqrt (N:ℝ))^(r-1) := by positivity
  have hsqrt : Real.sqrt ((N:ℝ)/(N:ℝ)^r)=1/(Real.sqrt (N:ℝ))^(r-1) :=
    (eq_div_iff (ne_of_gt hS)).mpr (normalization_identity hr hN)
  have hset : {A : Tensor (r+1) N | goodNormConstant r < normalizedNorm A}=
      {A : Tensor (r+1) N | goodNormConstant r*Real.sqrt ((N:ℝ)/(N:ℝ)^r) < ‖tensorForm A‖} := by
    ext A
    unfold normalizedNorm
    rw [hsqrt,mul_one_div]
    exact (div_lt_iff₀ hS).symm
  have ht := actual_tensor_norm_good (r:=r) hN
  rw [← hset] at ht
  have hm : MeasurableSet {A : Tensor (r+1) N | goodNormConstant r < normalizedNorm A} :=
    measurableSet_lt measurable_const (normalizedNorm_continuous r N).measurable
  have he :=
      congrArg ENNReal.toReal ((actual_tensor_preserving r N).measure_preimage hm.nullMeasurableSet)
  exact he.trans_le ht

theorem normBound_tail {r N : ℕ} (hr : 0<r) (hN : 0<N) :
    (stdGaussian (Input r N)).real {x | normBound r < normScale x}≤2*Real.exp (-(N:ℝ)) := by
  refine (measureReal_mono (fun x hx => ?_)).trans (normScale_good_tail hr hN)
  change goodNormConstant r < normScale x
  have hg := le_abs_self (goodNormConstant r)
  change 1+|goodNormConstant r| < normScale x at hx
  linarith

def pairRegion (r N : ℕ) : Set (Input r N×Input r N) :=
  {w | normScale w.1≤normBound r ∧ normScale w.2≤normBound r}

theorem pairRegion_failure {r N : ℕ} (hr : 0<r) (hN : 0<N) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real (pairRegion r N)ᶜ≤4*Real.exp (-(N:ℝ)) := by
  have hm : MeasurableSet {x : Input r N | normBound r < normScale x} :=
    measurableSet_lt measurable_const (normScale_measurable r N)
  have hfst := congrArg ENNReal.toReal ((measurePreserving_fst (μ:=stdGaussian (Input r N))
    (ν:=stdGaussian (Input r N))).measure_preimage hm.nullMeasurableSet)
  have hsnd := congrArg ENNReal.toReal ((measurePreserving_snd (μ:=stdGaussian (Input r N))
    (ν:=stdGaussian (Input r N))).measure_preimage hm.nullMeasurableSet)
  have hsub : (pairRegion r N)ᶜ⊆{w : Input r N×Input r N | normBound r < normScale w.1}∪
      {w | normBound r < normScale w.2} := by
    intro w hw
    by_cases hx : normScale w.1≤normBound r
    · right
      exact lt_of_not_ge (fun hy => hw ⟨hx,hy⟩)
    · left
      exact lt_of_not_ge hx
  refine ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans ?_
  change ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real {w | normBound r < normScale w.1}=
    (stdGaussian (Input r N)).real {x | normBound r < normScale x} at hfst
  change ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real {w | normBound r < normScale w.2}=
    (stdGaussian (Input r N)).real {x | normBound r < normScale x} at hsnd
  rw [hfst,hsnd]
  nlinarith [normBound_tail hr hN]

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion
