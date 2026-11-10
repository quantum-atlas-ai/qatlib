/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Real Filter
open scoped Topology

namespace Qatlib.Papers.LocAdiabSrch01.MainResults.MainResult

open Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule

theorem source_local_adiabatic_time_asymptotic {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℝ => localAdiabaticTime ε N / sqrt N) atTop
      (𝓝 (Real.pi / (2 * ε))) := by

  have hsub : Tendsto (fun N : ℝ => N - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + 1, fun a ha => by linarith⟩)

  have hinv : Tendsto (fun N : ℝ => (N - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsub
  have hone : Tendsto (fun N : ℝ => 1 + (N - 1)⁻¹) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hinv
  have hratio : Tendsto (fun N : ℝ => N / (N - 1)) atTop (𝓝 1) := by
    have hlim : (1 : ℝ) + 0 = 1 := by norm_num
    rw [hlim] at hone
    refine hone.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    field_simp
    ring

  have hsqrtratio : Tendsto (fun N : ℝ => sqrt (N / (N - 1))) atTop (𝓝 1) := by
    have := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
    simpa using! this

  have hsqrttend : Tendsto (fun N : ℝ => sqrt (N - 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hsub
  have harctan : Tendsto (fun N : ℝ => arctan (sqrt (N - 1))) atTop (𝓝 (Real.pi / 2)) := by
    have h := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hsqrttend
    simpa using! h

  have hprod : Tendsto (fun N : ℝ => sqrt (N / (N - 1)) * (arctan (sqrt (N - 1)) / ε))
      atTop (𝓝 (1 * (Real.pi / 2 / ε))) :=
    hsqrtratio.mul (harctan.div_const ε)
  have hlimit : (1 : ℝ) * (Real.pi / 2 / ε) = Real.pi / (2 * ε) := by
    field_simp
  rw [hlimit] at hprod

  refine Tendsto.congr' ?_ hprod
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  exact (localAdiabaticTime_div_sqrt hε hN).symm

end Qatlib.Papers.LocAdiabSrch01.MainResults.MainResult
