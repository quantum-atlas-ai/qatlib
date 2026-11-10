/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Qatlib.Papers.AnyonicSpin06.MainResults.SU2Euler
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open scoped Quaternion
open Quaternion

namespace Qatlib.Papers.AnyonicSpin06.MainResults.TwoAxis

open Qatlib.Papers.AnyonicSpin06.MainResults.SU2Euler

def vv (γ : ℝ) : ℍ[ℝ] := (Real.cos γ : ℍ[ℝ]) * Iq + (Real.sin γ : ℍ[ℝ]) * Jq

lemma vv_re (γ : ℝ) : (vv γ).re = 0 := by
  simp [vv, Iq, Jq]

lemma normSq_vv (γ : ℝ) : normSq (vv γ) = 1 := by
  unfold vv Iq Jq
  rw [Quaternion.normSq_def']
  simp only [re_add, imI_add, imJ_add, imK_add, re_mul, imI_mul, imJ_mul, imK_mul,
    re_coe, imI_coe, imJ_coe, imK_coe]
  nlinarith [Real.sin_sq_add_cos_sq γ]

lemma vv_imJ (γ : ℝ) : (vv γ).imJ = Real.sin γ := by
  simp [vv, Iq, Jq]

lemma vv_imI (γ : ℝ) : (vv γ).imI = Real.cos γ := by
  simp [vv, Iq, Jq]

lemma vv_pi_div_two : vv (Real.pi / 2) = Jq := by
  simp [vv, Jq, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem two_axis_components (a b c γ : ℝ) :
    (expUnit a Iq * expUnit b (vv γ) * expUnit c Iq).imJ
        = Real.sin b * Real.sin γ * Real.cos (a - c) ∧
      (expUnit a Iq * expUnit b (vv γ) * expUnit c Iq).imK
        = Real.sin b * Real.sin γ * Real.sin (a - c) := by
  constructor <;>
    simp only [expUnit, vv, Iq, Jq, re_mul, imI_mul, imJ_mul, imK_mul,
      re_add, imI_add, imJ_add, imK_add, re_coe, imI_coe, imJ_coe, imK_coe,
      Real.cos_sub, Real.sin_sub] <;> ring

theorem two_axis_offaxis_sq (a b c γ : ℝ) :
    (expUnit a Iq * expUnit b (vv γ) * expUnit c Iq).imJ ^ 2
      + (expUnit a Iq * expUnit b (vv γ) * expUnit c Iq).imK ^ 2
        = (Real.sin b * Real.sin γ) ^ 2 := by
  obtain ⟨h1, h2⟩ := two_axis_components a b c γ
  rw [h1, h2]
  nlinarith [Real.sin_sq_add_cos_sq (a - c)]

theorem two_axis_offaxis_le (a b c γ : ℝ) :
    (expUnit a Iq * expUnit b (vv γ) * expUnit c Iq).imJ ^ 2
      + (expUnit a Iq * expUnit b (vv γ) * expUnit c Iq).imK ^ 2
        ≤ Real.sin γ ^ 2 := by
  rw [two_axis_offaxis_sq]
  have hb : Real.sin b ^ 2 ≤ 1 := Real.sin_sq_le_one b
  nlinarith [sq_nonneg (Real.sin γ)]

theorem two_axis_orthonormal (q : ℍ[ℝ]) (hq : normSq q = 1) :
    ∃ a b c : ℝ, q = expUnit a Iq * expUnit b (vv (Real.pi / 2)) * expUnit c Iq := by
  obtain ⟨a, b, c, h⟩ := exists_euler_angles q hq
  refine ⟨a, b, c, ?_⟩
  rw [h, vv_pi_div_two]
  simp [expUnit, expq, expqJ]

theorem euler_two_axis_refuted : ¬ EulerTwoAxis := by
  intro h
  have hIq_re : (Iq).re = 0 := by simp [Iq]
  have hIq_norm : normSq (Iq) = 1 := by
    simp [Iq, Quaternion.normSq_def']
  have hJq_norm : normSq (Jq) = 1 := by
    simp [Jq, Quaternion.normSq_def']
  have hvv_re : (vv (Real.pi / 3)).re = 0 := vv_re _
  have hvv_norm : normSq (vv (Real.pi / 3)) = 1 := normSq_vv _
  have hsin : Real.sin (Real.pi / 3) ≠ 0 := by
    rw [Real.sin_pi_div_three]
    positivity
  have hne : Iq ≠ vv (Real.pi / 3) := by
    intro he
    have h1 : Iq.imJ = (vv (Real.pi / 3)).imJ :=
      congrArg (fun q : ℍ[ℝ] => q.imJ) he
    rw [vv_imJ] at h1
    have h0 : Iq.imJ = 0 := by simp [Iq]
    rw [h0] at h1
    exact hsin h1.symm
  have hne' : Iq ≠ -vv (Real.pi / 3) := by
    intro he
    have h1 : Iq.imJ = (-vv (Real.pi / 3)).imJ :=
      congrArg (fun q : ℍ[ℝ] => q.imJ) he
    rw [Quaternion.imJ_neg, vv_imJ] at h1
    have h0 : Iq.imJ = 0 := by simp [Iq]
    rw [h0] at h1
    exact hsin (by linarith)
  obtain ⟨a, b, c, habc⟩ :=
    h Iq (vv (Real.pi / 3)) hIq_re hvv_re hIq_norm hvv_norm hne hne' Jq hJq_norm
  have hle := two_axis_offaxis_le a b c (Real.pi / 3)
  rw [← habc] at hle
  have hJ1 : Jq.imJ = 1 := by simp [Jq]
  have hJ2 : Jq.imK = 0 := by simp [Jq]
  rw [hJ1, hJ2] at hle
  have hs : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := Real.sq_sin_pi_div_three
  rw [hs] at hle
  norm_num at hle

end Qatlib.Papers.AnyonicSpin06.MainResults.TwoAxis
