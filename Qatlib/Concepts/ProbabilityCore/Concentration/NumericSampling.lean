/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.NumericSamplingDefs
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm

/-!
# Dyadic rounding errors for sampled matrices

The module bounds scalar, complex, and matrix errors caused by dyadic floor rounding and
transports norm tail events through that error budget. Rounding also commutes with matrix
reindexing.

The norm estimates use finite matrix analysis as in [Bhatia1997] and allow sampled matrix bounds
to include numerical precision.

## Main statements

* `dyadic_matrix_error`: a matrix rounding error bounded by `dyadicOpBudget`.
* `dyadic_sample_tail` and `dyadic_measure_tail`: tail bounds with a rounding allowance.
* `dyadic_reindex`: compatibility with coordinate relabeling.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.Concentration
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Encoding a complex number with rational real and imaginary parts agrees with rational dyadic
encoding. -/
theorem dyadicEncode_rat (bits : ℕ) (a b : ℚ) :
    dyadicEncode bits ((a : ℂ) + (b : ℂ)*Complex.I) = dyadicEncodeRat bits (a,b) := by
  have hf (q : ℚ) : ⌊(2 : ℝ)^bits*(q : ℝ)⌋ = ⌊(2 : ℚ)^bits*q⌋ := by
    have h := Int.map_floor (Rat.castHom ℝ) Rat.cast_strictMono ((2 : ℚ)^bits*q)
    simpa using h
  simp [dyadicEncode, dyadicEncodeRat, hf]

/-- Dyadic floor rounding of a real number has absolute error at most `1 / 2 ^ bits`. -/
theorem dyadic_scalar_error (bits : ℕ) (x : ℝ) :
    |(⌊(2 : ℝ)^bits*x⌋ : ℝ)/(2 : ℝ)^bits-x| ≤ 1/(2 : ℝ)^bits := by
  have hs : 0 < (2 : ℝ)^bits := by positivity
  have hlo := Int.floor_le ((2 : ℝ)^bits*x)
  have hhi := Int.lt_floor_add_one ((2 : ℝ)^bits*x)
  have he : (⌊(2 : ℝ)^bits*x⌋ : ℝ)/(2 : ℝ)^bits-x =
      ((⌊(2 : ℝ)^bits*x⌋ : ℝ)-(2 : ℝ)^bits*x)/(2 : ℝ)^bits := by
    field_simp
  rw [he, abs_div, abs_of_pos hs, abs_of_nonpos (sub_nonpos.mpr hlo)]
  exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- Dyadic rounding of a complex number has norm error at most `2 / 2 ^ bits`. -/
theorem dyadic_complex_error (bits : ℕ) (z : ℂ) :
    ‖dyadicRoundComplex bits z-z‖ ≤ 2/(2 : ℝ)^bits := by
  have hr : |(dyadicRoundComplex bits z-z).re| ≤ 1/(2 : ℝ)^bits := by
    simpa only [dyadicRoundComplex, dyadicDecode, dyadicEncode, Complex.sub_re,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using
        dyadic_scalar_error bits z.re
  have hi : |(dyadicRoundComplex bits z-z).im| ≤ 1/(2 : ℝ)^bits := by
    simpa only [dyadicRoundComplex, dyadicDecode, dyadicEncode, Complex.sub_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add] using
        dyadic_scalar_error bits z.im
  calc
    _ ≤ |(dyadicRoundComplex bits z-z).re|+|(dyadicRoundComplex bits z-z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1/(2 : ℝ)^bits+1/(2 : ℝ)^bits := add_le_add hr hi
    _ = _ := by ring

/-- The norm error of a dyadically rounded square matrix is at most `dyadicOpBudget I bits`. -/
theorem dyadic_matrix_error {I : Type} [Fintype I] [DecidableEq I]
    (bits : ℕ) (A : Matrix I I ℂ) :
    ‖dyadicRoundMatrix bits A-A‖ ≤ dyadicOpBudget I bits := by
  have hb : 0 ≤ dyadicOpBudget I bits := by unfold dyadicOpBudget; positivity
  have he (i j : I) : Complex.normSq ((dyadicRoundMatrix bits A-A) i j) ≤
      (2/(2 : ℝ)^bits)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (dyadic_complex_error bits (A i j)) 2
  apply (spectral_operator_norm_le_frobenius _).trans
  apply (sq_le_sq₀ (spectralFrobenius_nonneg _) hb).mp
  rw [spectralFrobenius_sq]
  calc
    _ ≤ ∑ _i : I, ∑ _j : I, (2/(2 : ℝ)^bits)^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => he i j))
    _ = _ := by simp [dyadicOpBudget]; ring

/-- For a finite sample law, the rounded matrix tail beyond `η` plus the rounding budget is
bounded by the original tail beyond `η`. -/
theorem dyadic_sample_tail {X : Type*} [Fintype X] {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist X) (A : X → Matrix I I ℂ) (T : Matrix I I ℂ) (bits : ℕ) (η : ℝ) :
    eventMass p (fun ω => η+dyadicOpBudget I bits < ‖dyadicRoundMatrix bits (A ω)-T‖) ≤
      eventMass p (fun ω => η < ‖A ω-T‖) := by
  unfold eventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hw := (Finset.mem_filter.mp hω).2
    have hb := dyadic_matrix_error bits (A ω)
    have hn := dist_triangle (dyadicRoundMatrix bits (A ω)) (A ω) T
    simp only [dist_eq_norm] at hn
    linarith only [hw, hb, hn]
  · intro ω _ _
    exact p.nonneg ω

/-- Dyadic matrix rounding commutes with reindexing both matrix coordinates by an equivalence. -/
theorem dyadic_reindex {I J : Type*} (e : I ≃ J) (bits : ℕ) (A : Matrix I I ℂ) :
    dyadicRoundMatrix bits (Matrix.reindex e e A) =
      Matrix.reindex e e (dyadicRoundMatrix bits A) := rfl

/-- For any measure, the rounded matrix tail beyond `η` plus the rounding budget is bounded by
the original tail beyond `η`. -/
theorem dyadic_measure_tail {Ω : Type*} [MeasurableSpace Ω]
    {I : Type} [Fintype I] [DecidableEq I]
    (μ : MeasureTheory.Measure Ω) (A : Ω → Matrix I I ℂ) (T : Matrix I I ℂ)
    (bits : ℕ) (η : ℝ) :
    μ {ω | η+dyadicOpBudget I bits < ‖dyadicRoundMatrix bits (A ω)-T‖} ≤
      μ {ω | η < ‖A ω-T‖} := by
  apply MeasureTheory.measure_mono
  intro ω hω
  change η+dyadicOpBudget I bits < ‖dyadicRoundMatrix bits (A ω)-T‖ at hω
  change η < ‖A ω-T‖
  have hb := dyadic_matrix_error bits (A ω)
  have hn := dist_triangle (dyadicRoundMatrix bits (A ω)) (A ω) T
  simp only [dist_eq_norm] at hn
  linarith only [hω, hb, hn]

end Qatlib.Concepts.ProbabilityCore.Concentration
