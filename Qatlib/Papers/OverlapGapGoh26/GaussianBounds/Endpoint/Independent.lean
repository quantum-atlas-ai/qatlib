/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.Variance
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical RealInnerProductSpace
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

def overlap {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (z : Input r N×Input r N) : ℝ :=
  test s T (spin s T z.1) z.2

theorem overlap_continuous {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) :
    Continuous (overlap (r:=r) (N:=N) s T) := by
  have hc := (spin_smooth (r:=r) (N:=N) s T).continuous
  unfold overlap test
  fun_prop

theorem overlap_abs_le_one {r N : ℕ} (hN : 0<N) (s : ℕ→ℝ) (T : ℕ) (z : Input r N×Input r N) :
    |overlap s T z|≤1 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [overlap,test,abs_div,abs_of_pos hn]
  calc
    _ ≤ (Real.sqrt (N:ℝ)*Real.sqrt (N:ℝ))/(N:ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (spin_norm_le s T z.1) (spin_norm_le s T z.2) (norm_nonneg _) (Real.sqrt_nonneg _))
    _ = 1 := by rw [Real.mul_self_sqrt hn.le,div_self hn.ne']

theorem overlap_memLp {r N : ℕ} (hN : 0<N) (s : ℕ→ℝ) (T : ℕ) :
    MemLp (overlap (r:=r) (N:=N) s T) 2
      ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))) := by
  apply MemLp.of_bound (overlap_continuous s T).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun z=>by
    simpa only [Real.norm_eq_abs] using overlap_abs_le_one hN s T z

theorem overlap_mean_zero {r N : ℕ} (hr : Odd r) (hN : 0<N) (s : ℕ→ℝ) (T : ℕ) :
    (∫ z:Input r N×Input r N,overlap s T z
      ∂((stdGaussian (Input r N)).prod (stdGaussian (Input r N))))=0 := by
  have hi := (overlap_memLp (r:=r) hN s T).integrable (by norm_num)
  rw [integral_prod _ hi]
  have he (x:Input r N) : (∫ y:Input r N,overlap s T (x,y) ∂stdGaussian (Input r N))=0 :=
    test_mean_zero hr s T (spin s T x)
  simp_rw [he]
  simp

theorem overlap_second_moment {r N T : ℕ} (hr : Odd r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    (∫ z:Input r N×Input r N,(overlap s T z)^2
      ∂((stdGaussian (Input r N)).prod (stdGaussian (Input r N))))≤endpointConstant r T/(N:ℝ) := by
  have hi : Integrable (fun z:Input r N×Input r N=>(overlap s T z)^2)
      ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))) := by
    simpa only [Real.norm_eq_abs,sq_abs] using (overlap_memLp (r:=r) hN s T).integrable_norm_pow'
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _x:Input r N,endpointConstant r T/(N:ℝ) ∂stdGaussian (Input r N) :=
      integral_mono_ae hi.integral_prod_left (integrable_const _)
        (Filter.Eventually.of_forall fun x=>test_second_moment hr hN s hs (spin s T x) (spin_norm_le s T x))
    _ = _ := by simp

theorem overlap_variance {r N T : ℕ} (hr : Odd r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    variance (overlap (r:=r) (N:=N) s T)
      ((stdGaussian (Input r N)).prod (stdGaussian (Input r N)))≤endpointConstant r T/(N:ℝ) := by
  have he := variance_eq_sub (overlap_memLp (r:=r) hN s T)
  rw [overlap_mean_zero hr hN,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at he
  rw [he]
  exact overlap_second_moment hr hN s hs

theorem independent_endpoint_tail {r N T : ℕ} (hr : Odd r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0<δ) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
      {z | δ≤|overlap s T z|}≤endpointConstant r T/((N:ℝ)*δ^2) := by
  have h := meas_ge_le_variance_div_sq (overlap_memLp (r:=r) hN s T) hδ
  rw [overlap_mean_zero hr hN] at h
  simp only [sub_zero] at h
  have hh := ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (variance_nonneg _ _) (sq_nonneg δ)) h
  refine hh.trans ?_
  exact (div_le_div_of_nonneg_right (overlap_variance hr hN s hs) (sq_nonneg δ)).trans_eq (by ring)
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
