/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.TelegraphLimit.UniformDecay
import Qatlib.Papers.ParabolicPDE24.MainResults.Normalization
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Qatlib.Foundations.TimeEvolution.TelegraphLimit
open Qatlib.Papers.ParabolicPDE24.MainResults
namespace Qatlib.Papers.ParabolicPDE24.HeatLimit

def bandConstant (k A t : ℝ) : ℝ := 4*k*A+4*k*A^2*t

theorem physical_relative_error {I : Type} [Fintype I] (a : I→ℝ) (x : EuclideanSpace ℂ I)
    {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A) (ha : ∀i,0≤a i ∧ a i≤A)
    (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖weightedState (fun i=>mode (k*ε^2) (a i) t) x-weightedState (fun i=>heatMode (a i) t) x‖≤
      bandConstant k A t*ε^2*‖weightedState (fun i=>heatMode (a i) t) x‖ := by
  convert finite_band_relative a x (by positivity : 0<k*ε^2) hA ha hm ht using 1
  rw [bandConstant]
  ring

theorem physical_normalized_error {I : Type} [Fintype I] (a : I→ℝ) (x : EuclideanSpace ℂ I)
    (hx : x≠0) {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A)
    (ha : ∀i,0≤a i ∧ a i≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖normalizedState (weightedState (fun i=>heatMode (a i) t) x)-
      normalizedState (weightedState (fun i=>mode (k*ε^2) (a i) t) x)‖≤
      2*bandConstant k A t*ε^2 := by
  let H := weightedState (fun i=>heatMode (a i) t) x
  let U := weightedState (fun i=>mode (k*ε^2) (a i) t) x
  have hH : H≠0 := weightedState_ne_zero _ (fun _=>(Real.exp_pos _).ne') x hx
  have hU : U≠0 := weightedState_ne_zero _ (fun i=>(mode_pos (by positivity : 0<k*ε^2)
    (ha i).1 ((mul_le_mul_of_nonneg_left (ha i).2 (by positivity : 0≤4*(k*ε^2))).trans hm) ht).ne') x hx
  have he : ‖H-U‖≤bandConstant k A t*ε^2*‖H‖ := by
    simpa only [norm_sub_rev] using physical_relative_error a x hk hε hA ha hm ht
  calc
    ‖normalizedState H-normalizedState U‖≤2*‖H-U‖/‖H‖ := norm_normalizedState_sub_le H U hH hU
    _≤2*bandConstant k A t*ε^2 := by
      apply (div_le_iff₀ (norm_pos_iff.mpr hH)).mpr
      nlinarith

theorem physical_target_precision {I : Type} [Fintype I] (a : I→ℝ) (x : EuclideanSpace ℂ I)
    (hx : x≠0) {k ε A t q : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A)
    (ha : ∀i,0≤a i ∧ a i≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) (hq : 0<q)
    (hC : 0<bandConstant k A t) (hp : ε≤Real.sqrt (q/(2*bandConstant k A t))) :
    ‖normalizedState (weightedState (fun i=>heatMode (a i) t) x)-
      normalizedState (weightedState (fun i=>mode (k*ε^2) (a i) t) x)‖≤q := by
  have hs : ε^2≤(Real.sqrt (q/(2*bandConstant k A t)))^2 :=
    (sq_le_sq₀ hε.le (Real.sqrt_nonneg _)).mpr hp
  rw [Real.sq_sqrt (by positivity)] at hs
  have hb := (le_div_iff₀ (by positivity : 0<2*bandConstant k A t)).mp hs
  exact (physical_normalized_error a x hx hk hε hA ha hm ht).trans (by nlinarith)

def uniformConstant (k A : ℝ) : ℝ := 4*k*A+2*A^2

theorem physical_uniform_error {I : Type} [Fintype I] (a : I→ℝ) (x : EuclideanSpace ℂ I)
    {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (ha : ∀i,4*k≤a i ∧ a i≤A)
    (hA : 0≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖weightedState (fun i=>mode (k*ε^2) (a i) t) x-weightedState (fun i=>heatMode (a i) t) x‖≤
      uniformConstant k A*ε^2*Real.exp (-2*k*t)*‖x‖ := by
  have hid : weightedState (fun i=>mode (k*ε^2) (a i) t) x-
      weightedState (fun i=>heatMode (a i) t) x=
      weightedState (fun i=>mode (k*ε^2) (a i) t-heatMode (a i) t) x := by
    ext i
    change ((mode (k*ε^2) (a i) t:ℝ):ℂ)*x i-((heatMode (a i) t:ℝ):ℂ)*x i=
      ((mode (k*ε^2) (a i) t-heatMode (a i) t:ℝ):ℂ)*x i
    push_cast
    ring
  rw [hid]
  apply weightedState_norm _ _ (by dsimp [uniformConstant]; positivity)
  intro i
  have h := uniform_mode_error (by positivity : 0<k*ε^2) (by positivity : 0<2*k)
    (show 2*(2*k)≤a i by linarith [(ha i).1]) (ha i).2
    ((mul_le_mul_of_nonneg_left (ha i).2 (by positivity : 0≤4*(k*ε^2))).trans hm) ht
  convert h using 1
  dsimp [uniformConstant]
  field_simp
  ring
end Qatlib.Papers.ParabolicPDE24.HeatLimit
