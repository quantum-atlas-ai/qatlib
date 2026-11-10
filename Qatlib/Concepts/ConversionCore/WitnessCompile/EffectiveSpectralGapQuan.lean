/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Module
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem source_diagonal_mulVec_bound {H : Type} [Fintype H] [DecidableEq H]
    (c : H → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ h, ‖c h‖ ≤ C) (z : QState H) :
    ‖toEuclidean_fromVec (Matrix.diagonal c *ᵥ z)‖ ≤ C*‖toEuclidean_fromVec z‖ := by
  have hs : ‖toEuclidean_fromVec (Matrix.diagonal c *ᵥ z)‖^2 ≤
      C^2*‖toEuclidean_fromVec z‖^2 := by
    simp only [toEuclidean_fromVec,PiLp.norm_sq_eq_of_L2,Matrix.mulVec_diagonal,
      norm_mul,mul_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc h) 2)
      (sq_nonneg ‖z h‖)
  nlinarith [norm_nonneg (toEuclidean_fromVec (Matrix.diagonal c *ᵥ z)),
    norm_nonneg (toEuclidean_fromVec z),mul_nonneg hC (norm_nonneg (toEuclidean_fromVec z))]

theorem effectiveSpectralGap
    (H : Type) [Fintype H] [DecidableEq H] (P L V : Matrix H H ℂ)
    (angles : H → ℝ) (Θ : ℝ) (w : QState H)
    (_hP : IsOrthogonalProjector P) (_hL : IsOrthogonalProjector L)
    (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (_hangles : ∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi)
    (hU : ReflectionAbout P * ReflectionAbout L =
      V * Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) * Vᴴ)
    (hΘ : 0 ≤ Θ) (hLw : L *ᵥ w = 0) :
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ (P *ᵥ w))‖ ≤
      Θ/2*‖toEuclidean_fromVec w‖ := by
  let U := ReflectionAbout P * ReflectionAbout L
  let z := Vᴴ *ᵥ w
  let f := fun h => if |angles h| ≤ Θ then (1 : ℂ) else 0
  let g := fun h => f h*((1-Complex.exp (Complex.I*angles h))/2)
  have hVV : V*Vᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  have hVhV : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hiV : IsIsometry V := hVhV
  have hiVh : IsIsometry Vᴴ := by
    change (Vᴴ)ᴴ*Vᴴ=1
    simpa only [Matrix.conjTranspose_conjTranspose] using! hVV
  have hRL : ReflectionAbout L *ᵥ w = -w := by
    simp [ReflectionAbout,Matrix.sub_mulVec,Matrix.smul_mulVec,hLw]
  have hUw : U *ᵥ w = w-(2 : ℂ) • (P *ᵥ w) := by
    dsimp only [U]
    rw [← Matrix.mulVec_mulVec,hRL,Matrix.mulVec_neg]
    simp only [ReflectionAbout,Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,two_smul]
    module
  have hPw : P *ᵥ w = (1/2 : ℂ) • (w-U *ᵥ w) := by rw [hUw]; module
  have hUz : Vᴴ *ᵥ (U *ᵥ w) =
      Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) *ᵥ z := by
    dsimp only [U]
    rw [hU]
    simp only [← Matrix.mulVec_mulVec]
    change Vᴴ *ᵥ (V *ᵥ (Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) *ᵥ z)) = _
    rw [Matrix.mulVec_mulVec _ Vᴴ V,hVhV,Matrix.one_mulVec]
  have hPz : Vᴴ *ᵥ (P *ᵥ w) =
      Matrix.diagonal (fun h => (1-Complex.exp (Complex.I*angles h))/2) *ᵥ z := by
    rw [hPw,Matrix.mulVec_smul,Matrix.mulVec_sub,hUz]
    ext h
    simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
    change (1/2 : ℂ)*(z h-Complex.exp (Complex.I*angles h)*z h) = _
    ring
  have hdiag : sourcePhaseProjector V angles Θ *ᵥ (P *ᵥ w) =
      V *ᵥ (Matrix.diagonal g *ᵥ z) := by
    simp only [sourcePhaseProjector,← Matrix.mulVec_mulVec]
    rw [hPz]
    congr 1
    ext h
    simp only [Matrix.mulVec_diagonal,g,f]
    ring
  have hg (h : H) : ‖g h‖ ≤ Θ/2 := by
    dsimp [g,f]
    split_ifs with hh
    · simp only [one_mul,norm_div,Complex.norm_ofNat]
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
      calc
        ‖1-Complex.exp (Complex.I*angles h)‖ = ‖Complex.exp (Complex.I*angles h)-1‖ := norm_sub_rev _ _
        _ ≤ ‖angles h‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
        _ ≤ Θ := by simpa only [Real.norm_eq_abs] using! hh
    · simp only [zero_mul,norm_zero]
      positivity
  rw [hdiag,isometry_mulVec_norm hiV]
  have hb := source_diagonal_mulVec_bound g (Θ/2) (by positivity) hg z
  dsimp only [z] at hb
  rw [isometry_mulVec_norm hiVh] at hb
  exact hb

end Qatlib.Concepts.ConversionCore.WitnessCompile
