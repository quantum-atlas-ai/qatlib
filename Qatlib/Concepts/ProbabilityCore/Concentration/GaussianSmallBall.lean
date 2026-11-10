/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Qatlib.Concepts.ProbabilityCore.Concentration.NumericSampling
set_option warningAsError false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.Concentration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem gaussian_density_bound (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2*Real.pi*v))⁻¹ := by
  have he : Real.exp (-(x-m)^2/(2*v)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (mul_one _)

theorem gaussian_interval_bound (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (a b : ℝ) (hab : a ≤ b) :
    gaussianReal m v (Set.Icc a b) ≤ ENNReal.ofReal ((b-a)/Real.sqrt (2*Real.pi*v)) := by
  rw [gaussianReal_apply_eq_integral m hv]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _x in Set.Icc a b, (Real.sqrt (2*Real.pi*v))⁻¹ :=
      setIntegral_mono_on (integrable_gaussianPDFReal m v).integrableOn
        (integrableOn_const (isCompact_Icc.measure_lt_top.ne)) measurableSet_Icc
        (fun x _ => gaussian_density_bound m v x)
    _ = _ := by rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, div_eq_mul_inv]

theorem gaussian_small_ball (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (a ε : ℝ) (hε : 0 ≤ ε) :
    gaussianReal m v {x | |x-a| ≤ ε} ≤ ENNReal.ofReal (2*ε/Real.sqrt (2*Real.pi*v)) := by
  have hs : {x : ℝ | |x-a| ≤ ε} = Set.Icc (a-ε) (a+ε) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hs]
  convert gaussian_interval_bound m v hv (a-ε) (a+ε) (by linarith) using 1
  congr 1
  ring

theorem actual_gaussian_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) (a ε : ℝ) (hε : 0 ≤ ε) :
    P {ω | |X ω-a| ≤ ε} ≤ ENNReal.ofReal (2*ε/Real.sqrt (2*Real.pi*v)) := by
  rw [hX.measure_eq (p := fun x : ℝ => |x-a| ≤ ε) (by measurability)]
  exact gaussian_small_ball m v hv a ε hε

theorem rounded_gaussian_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0)
    (bits : ℕ) (a ε : ℝ) (hε : 0 ≤ ε) :
    P {ω | |(⌊(2 : ℝ)^bits*X ω⌋ : ℝ)/(2 : ℝ)^bits-a| ≤ ε} ≤
      ENNReal.ofReal (2*(ε+1/(2 : ℝ)^bits)/Real.sqrt (2*Real.pi*v)) := by
  apply (measure_mono ?_).trans (actual_gaussian_small_ball P X m v hX hv a
    (ε+1/(2 : ℝ)^bits) (by positivity))
  intro ω hω
  change |(⌊(2 : ℝ)^bits*X ω⌋ : ℝ)/(2 : ℝ)^bits-a| ≤ ε at hω
  change |X ω-a| ≤ ε+1/(2 : ℝ)^bits
  have hr := dyadic_scalar_error bits (X ω)
  have ht := abs_sub_le (X ω) ((⌊(2 : ℝ)^bits*X ω⌋ : ℝ)/(2 : ℝ)^bits) a
  rw [abs_sub_comm (X ω) ((⌊(2 : ℝ)^bits*X ω⌋ : ℝ)/(2 : ℝ)^bits)] at ht
  linarith only [hr, ht, hω]

theorem gaussian_polynomial_measurable (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) Q) := by
  apply Continuous.measurable
  exact Q.continuous_eval.comp (continuous_pi (fun i => by fun_prop))

theorem gaussian_polynomial_probability (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    IsProbabilityMeasure ((stdGaussian (EuclideanSpace ℝ (Fin n))).map
      (fun x => MvPolynomial.eval (fun i => x i) Q)) :=
  inferInstance

section GaussianLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_linear_law (L : StrongDual ℝ E) :
    HasLaw L (gaussianReal 0 (‖L‖^2).toNNReal) (stdGaussian E) := by
  refine ⟨L.continuous.measurable.aemeasurable, ?_⟩
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]

theorem stdGaussian_linear_small_ball (L : StrongDual ℝ E) (hL : L ≠ 0)
    (a ε : ℝ) (hε : 0 ≤ ε) :
    stdGaussian E {x | |L x-a| ≤ ε} ≤
      ENNReal.ofReal (2*ε/Real.sqrt (2*Real.pi*((‖L‖^2).toNNReal : ℝ))) := by
  have hv : (‖L‖^2).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (pow_pos (norm_pos_iff.mpr hL) 2))
  exact actual_gaussian_small_ball (stdGaussian E) L 0 _ (stdGaussian_linear_law L) hv a ε hε

end GaussianLinear

end Qatlib.Concepts.ProbabilityCore.Concentration
