/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.MatrixFunctions.ApproximateEigendecompositionTraceStat
import Qatlib.Concepts.SketchSpectral.MatrixFunctions.GibbsTracePerturbationSamp

/-!
# Trace estimates from approximate eigendecompositions

The module proves exponential and trace identities for an isometric compression, together with
scalar estimates used to control polar correction and exponential error.
`approximateEigendecompositionTrace` bounds the relative error of a partition-function estimate
from an approximate eigendecomposition, as in [ChiaEtAl2022].

## Main statements

* `isometry_exp_trace`: The real exponential trace of an isometric compression equals the
  smaller exponential trace plus the difference of the ambient dimensions.
* `approximateEigendecompositionTrace`: A sufficiently accurate approximate eigendecomposition
  with the stated near-isometry bounds estimates the exponential trace with relative error at
  most `2 * (exp 1 - 1) * ε`. See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.NearIsometry
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Matrix NormedSpace Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

/-- For an isometry `V`, the exponential of `V * D * Vᴴ` equals `1 + V * (exp D - 1) * Vᴴ`. -/
theorem isometry_exp_sandwich {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix I J ℂ) (D : Matrix J J ℂ)
    (hV : Vᴴ * V = 1) :
    exp (V*D*Vᴴ) = 1 + V*(exp D - 1)*Vᴴ := by
  let L : Matrix J J ℂ →ₗ[ℂ] Matrix I I ℂ :=
    { toFun := fun M => V*M*Vᴴ
      map_add' := by intro A B; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c A; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let C := L.toContinuousLinearMap
  have hp (k : ℕ) : (V*D*Vᴴ)^(k+1) = V*D^(k+1)*Vᴴ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
      simp only [pow_succ, Matrix.mul_assoc]
  have hsD := expSeries_summable' (𝕂 := ℂ) D
  have hsA := expSeries_summable' (𝕂 := ℂ) (V*D*Vᴴ)
  have hd : exp D - 1 = ∑' k : ℕ, (((k+1).factorial : ℂ)⁻¹) • D^(k+1) := by
    rw [congrFun (exp_eq_tsum ℂ) D, hsD.tsum_eq_zero_add]
    simp
  have ha : exp (V*D*Vᴴ) = 1 + ∑' k : ℕ,
      (((k+1).factorial : ℂ)⁻¹) • (V*D*Vᴴ)^(k+1) := by
    rw [congrFun (exp_eq_tsum ℂ) (V*D*Vᴴ), hsA.tsum_eq_zero_add]
    simp
  have ht : Summable (fun k : ℕ => (((k+1).factorial : ℂ)⁻¹) • D^(k+1)) :=
    (summable_nat_add_iff 1).mpr hsD
  have hm := C.map_tsum ht
  change V*(∑' k : ℕ, (((k+1).factorial : ℂ)⁻¹) • D^(k+1))*Vᴴ =
    ∑' k : ℕ, V*((((k+1).factorial : ℂ)⁻¹) • D^(k+1))*Vᴴ at hm
  rw [ha, hd, hm]
  simp only [hp, Matrix.mul_smul, Matrix.smul_mul]

/-- The real exponential trace of an isometric compression equals the smaller exponential trace
plus the difference of the ambient dimensions. -/
theorem isometry_exp_trace {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix I J ℂ) (D : Matrix J J ℂ)
    (hV : Vᴴ * V = 1) :
    (Matrix.trace (exp (V*D*Vᴴ))).re =
      (Matrix.trace (exp D)).re + ((Fintype.card I : ℝ) - (Fintype.card J : ℝ)) := by
  rw [isometry_exp_sandwich V D hV, Matrix.trace_add, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.trace_sub]
  simp only [Matrix.trace_one, Complex.add_re, Complex.sub_re, Complex.natCast_re]
  ring

/-- For `0 ≤ δ ≤ 1 / 4`, the coefficient `δ * (2 - δ) / (1 - δ)²` is at most `4 * δ`. -/
theorem polar_trace_coefficient_le {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/4) :
    δ*(2-δ)/(1-δ)^2 ≤ 4*δ := by
  have hp : 0 < (1-δ)^2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hp).mpr
  have hc : 2-δ ≤ 4*(1-δ)^2 := by nlinarith [sq_nonneg δ]
  have := mul_le_mul_of_nonneg_left hc hδ
  nlinarith

/-- For `0 ≤ ε ≤ 1 / 2`, `exp (2 * ε) - 1` is at most `2 * (exp 1 - 1) * ε`. -/
theorem gibbs_exp_chord {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/2) :
    Real.exp (2*ε)-1 ≤ 2*(Real.exp 1-1)*ε := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1-2*ε by linarith) (show 0 ≤ 2*ε by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at hc
  nlinarith

/-- A sufficiently accurate approximate eigendecomposition with the stated near-isometry bounds
estimates the exponential trace with relative error at most `2 * (exp 1 - 1) * ε`. See
[ChiaEtAl2022]. -/
theorem approximateEigendecompositionTrace : ApproximateEigendecompositionTrace := by
  intro I _ _ H hH r d D hD Ut ε δ hε hsmall hδeps hδnorm hGram happrox
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hGram
  have hquarter : δ ≤ 1/4 := by linarith
  have hδlt : δ < 1 := by linarith
  let P := nearColumnPolar Utᴴ
  have hpolar := near_isometry_polar_range_pseudoinverse_and_error I (Fin r) Utᴴ δ hδ hδlt
    (by simpa only [Matrix.conjTranspose_conjTranspose] using! hGram)
  have hP : Pᴴ*P=1 := hpolar.1
  have hcorr : ‖Utᴴ*D*Ut-P*D*Pᴴ‖ ≤
      δ*(2-δ)/(1-δ)^2*‖Utᴴ*D*Ut‖ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using! (hpolar.2.2.2.2 D).2
  have hbound : ‖Utᴴ*D*Ut‖ ≤ ‖H‖+ε := by
    have ht := norm_sub_le H (H-Utᴴ*D*Ut)
    rw [sub_sub_cancel] at ht
    linarith
  have hratio : 4*δ*(‖H‖+ε) ≤ ε := by
    have hn : 0 ≤ ‖H‖+ε := add_nonneg (norm_nonneg _) hε
    by_cases hz : ‖H‖+ε=0
    · simp only [hz, mul_zero]; exact hε
    · have hp : 0 < 4*(‖H‖+ε) := by positivity
      have hm := (le_div_iff₀ hp).mp hδnorm
      nlinarith
  have hcorrε : ‖Utᴴ*D*Ut-P*D*Pᴴ‖ ≤ ε := by
    calc
      _ ≤ δ*(2-δ)/(1-δ)^2*‖Utᴴ*D*Ut‖ := hcorr
      _ ≤ 4*δ*‖Utᴴ*D*Ut‖ := mul_le_mul_of_nonneg_right
        (polar_trace_coefficient_le hδ hquarter) (norm_nonneg _)
      _ ≤ 4*δ*(‖H‖+ε) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ ε := hratio
  have hdist : ‖P*D*Pᴴ-H‖ ≤ 2*ε := by
    have ht := norm_sub_le_norm_sub_add_norm_sub H (Utᴴ*D*Ut) (P*D*Pᴴ)
    rw [norm_sub_rev]
    linarith
  have hDH : D.IsHermitian := by
    rw [hD]
    simp only [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hPH := Matrix.isHermitian_mul_mul_conjTranspose P hDH
  have hb : 0 ≤ (Matrix.trace (exp H)).re := by
    rw [hermitian_exp_trace H hH]
    exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hg := gibbsTracePerturbation I H (P*D*Pᴴ) hH hPH
  have hcoeff : Real.exp ‖P*D*Pᴴ-H‖-1 ≤ 2*(Real.exp 1-1)*ε := by
    exact (sub_le_sub_right (Real.exp_le_exp.mpr hdist) 1).trans (gibbs_exp_chord hε hsmall)
  rw [isometry_exp_trace P D hP] at hg
  simp only [Fintype.card_fin] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right hcoeff hb)
end Qatlib.Concepts.SketchSpectral.MatrixFunctions
