/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.HeatLimit.ModeState
import Qatlib.Papers.ParabolicPDE24.FourierModel.FourierSystem
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParabolicPDE24.HeatLimit
open Qatlib.Papers.ParabolicPDE24.FourierDefs
open Qatlib.Foundations.TimeEvolution.TelegraphLimit

def sourceSignal {I : Type} (k ε : ℝ) (ω : I→ℝ) (x : EuclideanSpace ℂ I) (t : ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i=>signal k ε (ω i) (x i) t)

def sourceHeat {I : Type} (k : ℝ) (ω : I→ℝ) (x : EuclideanSpace ℂ I) (t : ℝ) : EuclideanSpace ℂ I :=
  weightedState (fun i=>heatMode (k*(ω i)^2) t) x

theorem sourceSignal_eq_weighted {I : Type} (k ε : ℝ) (ω : I→ℝ) (x : EuclideanSpace ℂ I) (t : ℝ) :
    sourceSignal k ε ω x t=weightedState (fun i=>mode (k*ε^2) (k*(ω i)^2) t) x := rfl

theorem source_uniform_error {I : Type} [Fintype I] (ω : I→ℝ) (x : EuclideanSpace ℂ I)
    {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A)
    (hω : ∀i,4≤(ω i)^2 ∧ k*(ω i)^2≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖sourceSignal k ε ω x t-sourceHeat k ω x t‖≤
      uniformConstant k A*ε^2*Real.exp (-2*k*t)*‖x‖ := by
  rw [sourceSignal_eq_weighted]
  apply physical_uniform_error _ x hk hε _ hA hm ht
  intro i
  exact ⟨by nlinarith [(hω i).1],(hω i).2⟩

theorem source_normalized_error {I : Type} [Fintype I] (ω : I→ℝ) (x : EuclideanSpace ℂ I)
    (hx : x≠0) {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A)
    (hω : ∀i,k*(ω i)^2≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖Qatlib.Papers.ParabolicPDE24.MainResults.normalizedState (sourceHeat k ω x t)-
      Qatlib.Papers.ParabolicPDE24.MainResults.normalizedState (sourceSignal k ε ω x t)‖≤
      2*bandConstant k A t*ε^2 := by
  rw [sourceSignal_eq_weighted]
  apply physical_normalized_error _ x hx hk hε hA _ hm ht
  intro i
  exact ⟨by positivity,hω i⟩
end Qatlib.Papers.ParabolicPDE24.HeatLimit
