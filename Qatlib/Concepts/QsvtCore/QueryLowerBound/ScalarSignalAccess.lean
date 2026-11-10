/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.QsvtCore.QueryLowerBound
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def scalarSignalReflection (x : ℝ) : Matrix Bool Bool ℂ := fun a b =>
  if a=b then (if a then -(x:ℂ) else (x:ℂ)) else (Real.sqrt (1-x^2):ℂ)

noncomputable def scalarSignalDistance (x y : ℝ) : ℝ :=
  Real.sqrt ((x-y)^2+(Real.sqrt (1-x^2)-Real.sqrt (1-y^2))^2)

noncomputable def scalarSignalLift (W : Type) [Fintype W] [DecidableEq W] (x : ℝ) :=
  TensorGate (scalarSignalReflection x) (1:Matrix W W ℂ)

theorem scalarSignalReflection_hermitian (x : ℝ) : (scalarSignalReflection x).IsHermitian := by
  change (scalarSignalReflection x)ᴴ=scalarSignalReflection x
  ext a b
  cases a <;> cases b <;> simp [scalarSignalReflection,Matrix.conjTranspose_apply]

theorem scalar_signal_actual_encoding : ∀ (x : ℝ), x ∈ Set.Icc (-1) 1 →
  (scalarSignalReflection x).IsHermitian ∧
  scalarSignalReflection x ∈ Matrix.unitaryGroup Bool ℂ ∧
  scalarSignalReflection x*scalarSignalReflection x=1 ∧
  ∀ (W : Type) [Fintype W] [DecidableEq W],
    ProjectedUnitaryEncoding ((x:ℂ) • (1:Matrix W W ℂ)) (scalarSignalLift W x)
      (encodingFiber false) (encodingFiber false) := by
  intro x hx
  have hs : 0≤1-x^2 := by nlinarith [hx.1,hx.2]
  have hs2 := Real.sq_sqrt hs
  have hsq : scalarSignalReflection x*scalarSignalReflection x=1 := by
    ext a b
    cases a <;> cases b <;> apply Complex.ext <;>
      simp [scalarSignalReflection,Matrix.mul_apply,
        Complex.mul_re,Complex.mul_im] <;> nlinarith
  have hH := scalarSignalReflection_hermitian x
  have hU : scalarSignalReflection x ∈ unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,hH.eq,hsq]
  refine ⟨hH,hU,hsq,?_⟩
  intro W _ _
  refine ⟨tensorGate_unitary hU (unitaryGroup W ℂ).one_mem,
    encodingFiber_isIsometry false,encodingFiber_isIsometry false,?_⟩
  ext i j
  rw [compress_encodingFiber_eq]
  simp [scalarSignalLift,TensorGate,scalarSignalReflection]

theorem scalarSignalDistance_nonneg (x y : ℝ) : 0≤ scalarSignalDistance x y := Real.sqrt_nonneg _

theorem scalarSignalDistance_sq (x y : ℝ) : scalarSignalDistance x y^2=
    (x-y)^2+(Real.sqrt (1-x^2)-Real.sqrt (1-y^2))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem scalar_difference_gram (x y : ℝ) :
    (scalarSignalReflection x-scalarSignalReflection y)ᴴ*(scalarSignalReflection x-scalarSignalReflection y) =
      (((x-y)^2+(Real.sqrt (1-x^2)-Real.sqrt (1-y^2))^2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  rw [Matrix.conjTranspose_sub,(scalarSignalReflection_hermitian x).eq,(scalarSignalReflection_hermitian y).eq]
  ext a b
  cases a <;> cases b <;> apply Complex.ext <;>
    simp [scalarSignalReflection,Matrix.mul_apply,pow_two,Complex.mul_re,Complex.mul_im] <;> ring

theorem scalar_signal_exact_distance_and_central_lipschitz : ∀ (x y : ℝ), x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
  ‖scalarSignalReflection x-scalarSignalReflection y‖=scalarSignalDistance x y ∧
  scalarSignalDistance x y=Real.sqrt 2 *
    Real.sqrt (1-x*y-Real.sqrt ((1-x^2)*(1-y^2))) ∧
  scalarSignalDistance x y ≤ Real.sqrt 2 *
    max |x-y| |Real.sqrt (1-x^2)-Real.sqrt (1-y^2)| ∧
  (x≠y → 0 < scalarSignalDistance x y) ∧
  (|x| ≤ 1/2 → |y| ≤ 1/2 → scalarSignalDistance x y ≤ 2*|x-y|) := by
  intro x y hx hy
  have hpx : 0≤1-x^2 := by nlinarith [hx.1,hx.2]
  have hpy : 0≤1-y^2 := by nlinarith [hy.1,hy.2]
  have hsx := Real.sq_sqrt hpx
  have hsy := Real.sq_sqrt hpy
  have hdnn := scalarSignalDistance_nonneg x y
  have hn2 : ‖scalarSignalReflection x-scalarSignalReflection y‖^2 =
      (x-y)^2+(Real.sqrt (1-x^2)-Real.sqrt (1-y^2))^2 := by
    rw [pow_two,← Matrix.l2_opNorm_conjTranspose_mul_self,scalar_difference_gram,norm_smul,
      l2_norm_one_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)),mul_one]
  have hnorm : ‖scalarSignalReflection x-scalarSignalReflection y‖=scalarSignalDistance x y := by
    nlinarith only [scalarSignalDistance_sq x y,hn2,norm_nonneg (scalarSignalReflection x-scalarSignalReflection y),hdnn]
  have he : scalarSignalDistance x y^2 =
      2*(1-x*y-Real.sqrt ((1-x^2)*(1-y^2))) := by
    rw [scalarSignalDistance_sq,Real.sqrt_mul hpx]
    nlinarith only [hsx,hsy]
  have hrad : 0≤1-x*y-Real.sqrt ((1-x^2)*(1-y^2)) := by
    nlinarith only [he,sq_nonneg (scalarSignalDistance x y)]
  have hexact : scalarSignalDistance x y=Real.sqrt 2*Real.sqrt (1-x*y-Real.sqrt ((1-x^2)*(1-y^2))) := by
    apply (sq_eq_sq₀ hdnn (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt hrad,he]
  have hmnn : 0≤ max |x-y| |Real.sqrt (1-x^2)-Real.sqrt (1-y^2)| :=
      (abs_nonneg _).trans (le_max_left _ _)
  have hdx := (sq_le_sq₀ (abs_nonneg (x-y)) hmnn).mpr (le_max_left |x-y| _)
  have hde :=
      (sq_le_sq₀ (abs_nonneg (Real.sqrt (1-x^2)-Real.sqrt (1-y^2))) hmnn).mpr (le_max_right |x-y| _)
  simp only [sq_abs] at hdx hde
  have hmax : scalarSignalDistance x y≤Real.sqrt 2*max |x-y| |Real.sqrt (1-x^2)-Real.sqrt (1-y^2)| := by
    apply (sq_le_sq₀ hdnn (mul_nonneg (Real.sqrt_nonneg _) hmnn)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num),scalarSignalDistance_sq]
    nlinarith only [hdx,hde]
  refine ⟨hnorm,hexact,hmax,?_,?_⟩
  · intro hxy
    apply Real.sqrt_pos.mpr
    have hd : x-y≠0 := sub_ne_zero.mpr hxy
    nlinarith only [sq_pos_of_ne_zero hd,sq_nonneg (Real.sqrt (1-x^2)-Real.sqrt (1-y^2))]
  · intro hxhalf hyhalf
    have hx2 : x^2≤(1/2 : ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hxhalf 2
    have hy2 : y^2≤(1/2 : ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hyhalf 2
    have hsxl : (1/2 : ℝ)≤Real.sqrt (1-x^2) := Real.le_sqrt_of_sq_le (by nlinarith only [hx2])
    have hsyl : (1/2 : ℝ)≤Real.sqrt (1-y^2) := Real.le_sqrt_of_sq_le (by nlinarith only [hy2])
    have hsum : 1≤Real.sqrt (1-x^2)+Real.sqrt (1-y^2) := by linarith
    have hsumabs : |x+y|≤1 := (abs_add_le x y).trans (by linarith only [hxhalf,hyhalf])
    have halg : (Real.sqrt (1-x^2)-Real.sqrt (1-y^2))*(Real.sqrt (1-x^2)+Real.sqrt (1-y^2)) =
        (y-x)*(x+y) := by nlinarith only [hsx,hsy]
    have habs := congrArg abs halg
    simp only [abs_mul,abs_of_nonneg (show 0≤Real.sqrt (1-x^2)+Real.sqrt (1-y^2) by positivity),abs_sub_comm y x] at habs
    have hsmall : |Real.sqrt (1-x^2)-Real.sqrt (1-y^2)|≤|x-y| := by
      calc
        _ ≤ |Real.sqrt (1-x^2)-Real.sqrt (1-y^2)| *(Real.sqrt (1-x^2)+Real.sqrt (1-y^2)) := by
          simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hsum (abs_nonneg (Real.sqrt (1-x^2)-Real.sqrt (1-y^2)))
        _ = |x-y| *|x+y| := habs
        _ ≤ |x-y| := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsumabs (abs_nonneg (x-y))
    have he2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg (x-y))).mpr hsmall
    simp only [sq_abs] at he2
    apply (sq_le_sq₀ hdnn (mul_nonneg (by norm_num) (abs_nonneg (x-y)))).mp
    rw [mul_pow,sq_abs,scalarSignalDistance_sq]
    nlinarith only [he2,sq_nonneg (x-y)]

end Qatlib.Concepts.QsvtCore.QueryLowerBound
