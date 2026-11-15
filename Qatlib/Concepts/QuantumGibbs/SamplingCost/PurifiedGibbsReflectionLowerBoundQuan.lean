/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.SamplingCost.PurifiedGibbsReflectionLowerBoundStat
public import Qatlib.Concepts.QuantumGibbs.SamplingCost.HamiltonianEvolutionHybrid
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
public import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Foundations.QueryWordCore.HamiltonianQuery Qatlib.Concepts.ReferenceError.MixturePaths

set_option autoImplicit false
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.QuantumGibbs.SamplingCost
open Matrix
open scoped Matrix.Norms.L2Operator

/-- The two-level Hamiltonian is Hermitian for every real parameter. -/
theorem twoLevelHamiltonian_hermitian (Δ : ℝ) : (twoLevelHamiltonian Δ).IsHermitian := by
  unfold twoLevelHamiltonian
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp only [IsSelfAdjoint, RCLike.star_def, Complex.conj_ofReal]

/-- The lifted two-level Hamiltonian is Hermitian for every ancilla size and real parameter. -/
theorem twoLevelHamiltonianLift_hermitian (A : ℕ) (Δ : ℝ) :
    (twoLevelHamiltonianLift A Δ).IsHermitian := by
  change (TensorGate (twoLevelHamiltonian Δ) (1 : Matrix (Fin A) (Fin A) ℂ))ᴴ = _
  rw [tensorGate_conjTranspose, (twoLevelHamiltonian_hermitian Δ).eq, Matrix.conjTranspose_one]
  rfl

/-- The purified two-level Gibbs state is normalized. -/
theorem purifiedGibbsTwoLevel_normalized (s : ℝ) : Normalized (purifiedGibbsTwoLevel s) := by
  unfold Normalized
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [purifiedGibbsTwoLevel, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- The pure density matrix of a state equals its outer product. -/
theorem pureDensity_eq_outerProduct {I : Type*} (ψ : QState I) :
    pureDensity ψ = outerProduct ψ := rfl

/-- Conversion from state vectors to Euclidean space preserves addition. -/
theorem toEuclidean_fromVec_add {I : Type*} [Fintype I] [DecidableEq I] (v w : QState I) :
    toEuclidean_fromVec (v + w) = toEuclidean_fromVec v + toEuclidean_fromVec w := rfl

/-- Conversion from state vectors to Euclidean space preserves negation. -/
theorem toEuclidean_fromVec_neg {I : Type*} [Fintype I] [DecidableEq I] (v : QState I) :
    toEuclidean_fromVec (-v) = -toEuclidean_fromVec v := rfl

/-- The amplitude at the pair of zero indices is the square root of the reciprocal of one plus
the exponential of the negative parameter. -/
@[simp] theorem purifiedGibbsTwoLevel_apply00 (s : ℝ) :
    purifiedGibbsTwoLevel s (0, 0) = ((Real.sqrt (1 / (1 + Real.exp (-s)) : ℝ) : ℂ)) := by
  simp [purifiedGibbsTwoLevel]

/-- The amplitude at the pair of unit indices is the square root of the exponential of the
negative parameter divided by one plus that exponential. -/
@[simp] theorem purifiedGibbsTwoLevel_apply11 (s : ℝ) :
    purifiedGibbsTwoLevel s (1, 1) =
      ((Real.sqrt (Real.exp (-s) / (1 + Real.exp (-s)) : ℝ) : ℂ)) := by
  simp [purifiedGibbsTwoLevel]

/-- The purified two-level Gibbs amplitude at zero followed by one vanishes. -/
@[simp] theorem purifiedGibbsTwoLevel_apply01 (s : ℝ) :
    purifiedGibbsTwoLevel s (0, 1) = ((0 : ℝ) : ℂ) := by
  simp [purifiedGibbsTwoLevel, Complex.ofReal_zero]

/-- The purified two-level Gibbs amplitude at one followed by zero vanishes. -/
@[simp] theorem purifiedGibbsTwoLevel_apply10 (s : ℝ) :
    purifiedGibbsTwoLevel s (1, 0) = ((0 : ℝ) : ℂ) := by
  simp [purifiedGibbsTwoLevel, Complex.ofReal_zero]

/-- The squares of the two nonzero purified Gibbs amplitudes sum to one. -/
theorem purifiedGibbsTwoLevel_sq_add_sq (s : ℝ) :
    (Real.sqrt (1 / (1 + Real.exp (-s)))) ^ 2
      + (Real.sqrt (Real.exp (-s) / (1 + Real.exp (-s)))) ^ 2 = 1 := by
  have h1 : (0 : ℝ) < 1 + Real.exp (-s) := by positivity
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (1 + Real.exp (-s))),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.exp (-s) / (1 + Real.exp (-s)))]
  field_simp

/-- The purified Gibbs reflection is the reflection about the purified state's outer product. -/
theorem purifiedGibbsReflection_eq_reflectionAbout (s : ℝ) :
    purifiedGibbsReflection s = ReflectionAbout (outerProduct (purifiedGibbsTwoLevel s)) := by
  have h2 : (2 * outerProduct (purifiedGibbsTwoLevel s) :
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      = (2 : ℂ) • outerProduct (purifiedGibbsTwoLevel s) := by
    rw [two_mul, two_smul]
  simp only [purifiedGibbsReflection, ReflectionAbout, pureDensity_eq_outerProduct]
  rw [h2]

/-- The purified Gibbs reflection maps a state to twice its projection onto the purified Gibbs
state minus itself. -/
theorem applyGate_purifiedGibbsReflection (s : ℝ) (φ : QState (Fin 2 × Fin 2)) :
    ApplyGate (purifiedGibbsReflection s) φ
      = (2 : ℂ) • ((Qatlib.Foundations.PureStateMath.Inner (purifiedGibbsTwoLevel s) φ) • purifiedGibbsTwoLevel s) - φ := by
  rw [purifiedGibbsReflection_eq_reflectionAbout, applyGate_reflectionAbout]
  simp only [ApplyGate, outerProduct_mulVec]

/-- The purified Gibbs reflection fixes its defining purified Gibbs state. -/
theorem applyGate_purifiedGibbsReflection_self (s : ℝ) :
    ApplyGate (purifiedGibbsReflection s) (purifiedGibbsTwoLevel s) = purifiedGibbsTwoLevel s := by
  rw [applyGate_purifiedGibbsReflection, inner_self_eq_one (purifiedGibbsTwoLevel_normalized s),
    one_smul, two_smul, add_sub_cancel_right]

/-- The inner product of two purified two-level Gibbs states is the sum of the products of their
corresponding real amplitudes. -/
theorem purifiedGibbs_inner (s t : ℝ) :
    Qatlib.Foundations.PureStateMath.Inner (purifiedGibbsTwoLevel s) (purifiedGibbsTwoLevel t) =
      ((Real.sqrt (1 / (1 + Real.exp (-s))) * Real.sqrt (1 / (1 + Real.exp (-t)))
        + Real.sqrt (Real.exp (-s) / (1 + Real.exp (-s)))
          * Real.sqrt (Real.exp (-t) / (1 + Real.exp (-t))) : ℝ) : ℂ) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Fintype.sum_prod_type, Fin.sum_univ_two,
    purifiedGibbsTwoLevel_apply00, purifiedGibbsTwoLevel_apply01,
    purifiedGibbsTwoLevel_apply10, purifiedGibbsTwoLevel_apply11,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_zero,
    mul_zero, add_zero, zero_add]

/-- For positive parameters, one minus the squared overlap equals the squared difference of
their square roots divided by the product of one plus each parameter. -/
theorem purified_overlap_sq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 - (Real.sqrt (1 / (1 + x)) * Real.sqrt (1 / (1 + y))
        + Real.sqrt (x / (1 + x)) * Real.sqrt (y / (1 + y))) ^ 2
      = (Real.sqrt x - Real.sqrt y) ^ 2 / ((1 + x) * (1 + y)) := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have h1y : (0 : ℝ) < 1 + y := by linarith
  have hAB : ((1 : ℝ) + x) * (1 + y) ≠ 0 := by positivity
  have e1 : Real.sqrt (1 / (1 + x)) = 1 / Real.sqrt (1 + x) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (1 + x), Real.sqrt_one]
  have e2 : Real.sqrt (x / (1 + x)) = Real.sqrt x / Real.sqrt (1 + x) :=
    Real.sqrt_div hx.le (1 + x)
  have e3 : Real.sqrt (1 / (1 + y)) = 1 / Real.sqrt (1 + y) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (1 + y), Real.sqrt_one]
  have e4 : Real.sqrt (y / (1 + y)) = Real.sqrt y / Real.sqrt (1 + y) :=
    Real.sqrt_div hy.le (1 + y)
  have hform : Real.sqrt (1 / (1 + x)) * Real.sqrt (1 / (1 + y))
        + Real.sqrt (x / (1 + x)) * Real.sqrt (y / (1 + y))
      = (1 + Real.sqrt x * Real.sqrt y) / (Real.sqrt (1 + x) * Real.sqrt (1 + y)) := by
    rw [e1, e2, e3, e4]
    field_simp
  have hUV : (Real.sqrt (1 + x) * Real.sqrt (1 + y)) ^ 2 = (1 + x) * (1 + y) := by
    rw [mul_pow, Real.sq_sqrt h1x.le, Real.sq_sqrt h1y.le]
  have hu : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hv : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  rw [hform, div_pow, hUV, eq_div_iff hAB]
  have key : (1 - (1 + Real.sqrt x * Real.sqrt y) ^ 2 / ((1 + x) * (1 + y)))
        * ((1 + x) * (1 + y)) = (Real.sqrt x - Real.sqrt y) ^ 2 := by
    rw [sub_mul, div_mul_cancel₀ _ hAB]
    linear_combination -(1 + y) * hu - (1 + Real.sqrt x * Real.sqrt x) * hv
  exact key

/-- For positive perturbations at most one, the decrease in the square root of the exponential
weight is at least one eighth of the perturbation. -/
theorem sqrt_exp_gap_ge {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε / 8 ≤ Real.sqrt (Real.exp (-1)) - Real.sqrt (Real.exp (-(1 + ε))) := by
  have hE : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2)) := by
    have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  have hEpos : 0 < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  have hzpos : 0 < Real.exp (-(ε / 2 : ℝ)) := Real.exp_pos _
  have hzhalf : (1 : ℝ) / 2 ≤ Real.exp (-(ε / 2 : ℝ)) := by
    have h1 := Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) ≤ -(ε / 2) by linarith)
    linarith
  have he : Real.exp (-(ε / 2 : ℝ)) * Real.exp (ε / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hkey : Real.exp (-(ε / 2 : ℝ)) * (ε / 2) ≤ 1 - Real.exp (-(ε / 2 : ℝ)) := by
    have h2 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (ε / 2 : ℝ)) hzpos.le
    nlinarith [he]
  have hx : Real.sqrt (Real.exp (-1)) = Real.exp (-(1 / 2 : ℝ)) := by
    have h : Real.exp (-1) = Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h, Real.sqrt_mul_self hEpos.le]
  have hy : Real.sqrt (Real.exp (-(1 + ε)))
      = Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(ε / 2 : ℝ)) := by
    have hstep : Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(ε / 2 : ℝ))
        = Real.exp (-((1 + ε) / 2 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h : Real.exp (-(1 + ε))
        = Real.exp (-((1 + ε) / 2 : ℝ)) * Real.exp (-((1 + ε) / 2 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h, ← hstep, Real.sqrt_mul_self (by positivity)]
  have hcomb : Real.exp (-(1 / 2 : ℝ)) - Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(ε / 2 : ℝ))
      = (1 - Real.exp (-(ε / 2 : ℝ))) * Real.exp (-(1 / 2 : ℝ)) := by ring
  rw [hx, hy, hcomb]
  have h4 : ε / 4 ≤ 1 - Real.exp (-(ε / 2 : ℝ)) := by
    have h3 : (1 / 2 : ℝ) * (ε / 2) ≤ Real.exp (-(ε / 2 : ℝ)) * (ε / 2) :=
      mul_le_mul_of_nonneg_right hzhalf (by linarith : (0 : ℝ) ≤ ε / 2)
    linarith
  have hz1 : Real.exp (-(ε / 2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfin : (ε / 4 : ℝ) * (1 / 2)
      ≤ (1 - Real.exp (-(ε / 2 : ℝ))) * Real.exp (-(1 / 2 : ℝ)) :=
    mul_le_mul h4 hE (by norm_num) (by linarith)
  linarith

noncomputable def purifiedOverlap (ε : ℝ) : ℝ :=
  Real.sqrt (1 / (1 + Real.exp (-1))) * Real.sqrt (1 / (1 + Real.exp (-(1 + ε))))
    + Real.sqrt (Real.exp (-1) / (1 + Real.exp (-1)))
      * Real.sqrt (Real.exp (-(1 + ε)) / (1 + Real.exp (-(1 + ε))))

/-- For positive perturbations at most one, one minus the squared purified overlap is at least
the perturbation squared divided by 256. -/
theorem purified_overlap_sensitivity {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ 2 / 256 ≤ 1 - (purifiedOverlap ε) ^ 2 := by
  have hx : 0 < Real.exp (-1) := Real.exp_pos _
  have hy : 0 < Real.exp (-(1 + ε)) := Real.exp_pos _
  have hdenpos : (0 : ℝ) < (1 + Real.exp (-1)) * (1 + Real.exp (-(1 + ε))) := by positivity
  have hden : (1 + Real.exp (-1)) * (1 + Real.exp (-(1 + ε))) ≤ 4 := by
    have e1 := Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
    have e2 := Real.exp_le_one_iff.mpr (show -(1 + ε : ℝ) ≤ 0 by linarith)
    nlinarith [hx.le, hy.le]
  simp only [purifiedOverlap]
  rw [purified_overlap_sq hx hy, le_div_iff₀ hdenpos]
  have hgap := sqrt_exp_gap_ge hε hε1
  have hnum : (ε / 8) ^ 2
      ≤ (Real.sqrt (Real.exp (-1)) - Real.sqrt (Real.exp (-(1 + ε)))) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (Real.exp (-1))
      - Real.sqrt (Real.exp (-(1 + ε))) - ε / 8)]
  have h1 : ε ^ 2 / 256 * ((1 + Real.exp (-1)) * (1 + Real.exp (-(1 + ε))))
      ≤ ε ^ 2 / 256 * 4 := mul_le_mul_of_nonneg_left hden (by positivity)
  have h2 : ε ^ 2 / 256 * 4 = ε ^ 2 / 64 := by field_simp; ring
  have h3 : ε ^ 2 / 64 = (ε / 8) ^ 2 := by field_simp; ring
  linarith

/-- The operator norm distance between two lifted two-level Hamiltonians is at most the absolute
difference of their parameters. -/
theorem reflection_lift_distance_le (A : ℕ) (Δ Γ : ℝ) :
    ‖twoLevelHamiltonianLift A Δ - twoLevelHamiltonianLift A Γ‖ ≤ |Δ - Γ| := by
  have hbase : ‖twoLevelHamiltonian Δ - twoLevelHamiltonian Γ‖ ≤ |Δ - Γ| := by
    simp only [twoLevelHamiltonian, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i
    fin_cases i <;> simp [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_sub]
  rw [twoLevelHamiltonianLift, twoLevelHamiltonianLift, tensorGate_sub_left, l2_norm_tensorGate]
  calc
    _ ≤ |Δ - Γ| * 1 := mul_le_mul hbase (l2_norm_one_le (I := Fin A)) (norm_nonneg _) (abs_nonneg _)
    _ = _ := mul_one _

/-- The squared output distance of the two purified Gibbs reflections on the perturbed purified
state is four times one minus their squared overlap. -/
theorem norm_reflection_diff_sq {ε : ℝ} :
    ‖toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
          (purifiedGibbsTwoLevel (1 + ε))
        - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε)))‖ ^ 2
      = 4 * (1 - (purifiedOverlap ε) ^ 2) := by
  have hc : Qatlib.Foundations.PureStateMath.Inner (purifiedGibbsTwoLevel 1) (purifiedGibbsTwoLevel (1 + ε))
      = ((purifiedOverlap ε : ℝ) : ℂ) := by
    simp only [purifiedOverlap]
    exact purifiedGibbs_inner 1 (1 + ε)
  have hd : ApplyGate (purifiedGibbsReflection 1) (purifiedGibbsTwoLevel (1 + ε))
        - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε))
      = (2 : ℂ) • (((purifiedOverlap ε : ℝ) : ℂ) • purifiedGibbsTwoLevel 1
          - purifiedGibbsTwoLevel (1 + ε)) := by
    rw [applyGate_purifiedGibbsReflection_self, applyGate_purifiedGibbsReflection, hc]
    module
  have hw : ‖toEuclidean_fromVec (((purifiedOverlap ε : ℝ) : ℂ) • purifiedGibbsTwoLevel 1
        - purifiedGibbsTwoLevel (1 + ε))‖ ^ 2
      = 1 - (purifiedOverlap ε) ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, purifiedGibbsTwoLevel_apply00, purifiedGibbsTwoLevel_apply01,
      purifiedGibbsTwoLevel_apply10, purifiedGibbsTwoLevel_apply11, Complex.ofReal_zero,
      mul_zero, sub_zero, norm_zero]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have hcunfold : purifiedOverlap ε = ((Real.sqrt (1 / (1 + Real.exp (-1)))
          * Real.sqrt (1 / (1 + Real.exp (-(1 + ε))))
        + Real.sqrt (Real.exp (-1) / (1 + Real.exp (-1)))
          * Real.sqrt (Real.exp (-(1 + ε)) / (1 + Real.exp (-(1 + ε)))) : ℝ)) := rfl
    rw [hcunfold]
    linear_combination ((Real.sqrt (1 / (1 + Real.exp (-1)))
          * Real.sqrt (1 / (1 + Real.exp (-(1 + ε))))
        + Real.sqrt (Real.exp (-1) / (1 + Real.exp (-1)))
          * Real.sqrt (Real.exp (-(1 + ε)) / (1 + Real.exp (-(1 + ε))))) ^ 2)
      * purifiedGibbsTwoLevel_sq_add_sq 1
      + purifiedGibbsTwoLevel_sq_add_sq (1 + ε)
  have h2 : ‖toEuclidean_fromVec ((2 : ℂ) • (((purifiedOverlap ε : ℝ) : ℂ)
            • purifiedGibbsTwoLevel 1 - purifiedGibbsTwoLevel (1 + ε)))‖ ^ 2
      = 4 * ‖toEuclidean_fromVec (((purifiedOverlap ε : ℝ) : ℂ) • purifiedGibbsTwoLevel 1
            - purifiedGibbsTwoLevel (1 + ε))‖ ^ 2 := by
    have hsm : toEuclidean_fromVec ((2 : ℂ) • (((purifiedOverlap ε : ℝ) : ℂ)
              • purifiedGibbsTwoLevel 1 - purifiedGibbsTwoLevel (1 + ε)))
        = (2 : ℂ) • toEuclidean_fromVec (((purifiedOverlap ε : ℝ) : ℂ)
            • purifiedGibbsTwoLevel 1 - purifiedGibbsTwoLevel (1 + ε)) := rfl
    rw [hsm, norm_smul]
    rw [Complex.norm_two, mul_pow]
    ring
  rw [hd, h2, hw]

/-- For positive perturbations at most one, the output distance of the two reflections on the
perturbed purified state is at least one eighth of the perturbation. -/
theorem norm_reflection_gap_ge {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε / 8 ≤ ‖toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
          (purifiedGibbsTwoLevel (1 + ε))
        - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε)))‖ := by
  have hsq := norm_reflection_diff_sq (ε := ε)
  have hsens := purified_overlap_sensitivity hε hε1
  have h4 : 4 * (ε ^ 2 / 256) ≤ 4 * (1 - (purifiedOverlap ε) ^ 2) :=
    mul_le_mul_of_nonneg_left hsens (by norm_num)
  have h64 : 4 * (ε ^ 2 / 256) = (ε / 8) ^ 2 := by field_simp; ring
  have hs : (ε / 8) ^ 2 ≤ ‖toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
          (purifiedGibbsTwoLevel (1 + ε))
        - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε)))‖ ^ 2 := by
    rw [hsq]; linarith
  have h := Real.sqrt_le_sqrt hs
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by linarith : (0 : ℝ) ≤ ε / 8)] at h

/-- Establishes the evolution-time lower bound for a valid query program approximating both
nearby purified Gibbs reflections within the specified error. -/
theorem purifiedGibbsReflectionLowerBound : PurifiedGibbsReflectionLowerBound := by
  intro β ε δ p hβ hε hε1 hδ hp h0 h1
  have hb : 0 < β := by linarith

  have hnψ₁ : ‖toEuclidean_fromVec (purifiedGibbsTwoLevel (1 + ε))‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (purifiedGibbsTwoLevel_normalized _)
  have hH0 : (twoLevelHamiltonianLift 2 (1 / β)).IsHermitian :=
      twoLevelHamiltonianLift_hermitian _ _
  have hH1 : (twoLevelHamiltonianLift 2 ((1 + ε) / β)).IsHermitian :=
    twoLevelHamiltonianLift_hermitian _ _
  have hdist : ‖twoLevelHamiltonianLift 2 (1 / β) - twoLevelHamiltonianLift 2 ((1 + ε) / β)‖
      ≤ ε / β := by
    have he : |1 / β - (1 + ε) / β| = ε / β := by
      rw [show 1 / β - (1 + ε) / β = -(ε / β) by field_simp; ring, abs_neg,
        abs_of_pos (div_pos hε hb)]
    exact (reflection_lift_distance_le 2 (1 / β) ((1 + ε) / β)).trans_eq he

  have hhyb : ‖toEuclidean_fromVec (HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
          (purifiedGibbsTwoLevel (1 + ε))
        - HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
          (purifiedGibbsTwoLevel (1 + ε)))‖
      ≤ HamiltonianEvolutionTime p * (ε / β) := by
    have h := norm_hamiltonianQueryRun_sub_le _ _ hH0 hH1 p hp (purifiedGibbsTwoLevel (1 + ε))
    rw [hnψ₁, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdist (hamiltonianEvolutionTime_nonneg p))

  have e0 := h0 (purifiedGibbsTwoLevel (1 + ε))
  rw [hnψ₁, mul_one] at e0
  have e0' : ‖toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
          (purifiedGibbsTwoLevel (1 + ε))
        - HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
          (purifiedGibbsTwoLevel (1 + ε)))‖ ≤ δ := by
    have hfn : ApplyGate (purifiedGibbsReflection 1) (purifiedGibbsTwoLevel (1 + ε))
          - HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
            (purifiedGibbsTwoLevel (1 + ε))
        = -(HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
              (purifiedGibbsTwoLevel (1 + ε))
            - ApplyGate (purifiedGibbsReflection 1) (purifiedGibbsTwoLevel (1 + ε))) := by
      module
    rw [hfn, toEuclidean_fromVec_neg, norm_neg]
    exact e0
  have e1 := h1 (purifiedGibbsTwoLevel (1 + ε))
  rw [hnψ₁, mul_one] at e1

  have hker := norm_reflection_gap_ge hε hε1

  have htrans : ‖toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
          (purifiedGibbsTwoLevel (1 + ε))
        - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε)))‖
      ≤ ‖toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
            (purifiedGibbsTwoLevel (1 + ε))
          - HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
            (purifiedGibbsTwoLevel (1 + ε)))‖
        + ‖toEuclidean_fromVec (HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
              (purifiedGibbsTwoLevel (1 + ε))
            - HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
              (purifiedGibbsTwoLevel (1 + ε)))‖
        + ‖toEuclidean_fromVec (HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
              (purifiedGibbsTwoLevel (1 + ε))
            - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε)))‖ := by
    have hEq : toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
            (purifiedGibbsTwoLevel (1 + ε))
          - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε)))
        = toEuclidean_fromVec (ApplyGate (purifiedGibbsReflection 1)
              (purifiedGibbsTwoLevel (1 + ε))
            - HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
              (purifiedGibbsTwoLevel (1 + ε)))
          + toEuclidean_fromVec (HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
                (purifiedGibbsTwoLevel (1 + ε))
              - HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
                (purifiedGibbsTwoLevel (1 + ε)))
          + toEuclidean_fromVec (HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
                (purifiedGibbsTwoLevel (1 + ε))
              - ApplyGate (purifiedGibbsReflection (1 + ε))
                (purifiedGibbsTwoLevel (1 + ε))) := by
      have hsplit : ApplyGate (purifiedGibbsReflection 1) (purifiedGibbsTwoLevel (1 + ε))
            - ApplyGate (purifiedGibbsReflection (1 + ε)) (purifiedGibbsTwoLevel (1 + ε))
          = (ApplyGate (purifiedGibbsReflection 1) (purifiedGibbsTwoLevel (1 + ε))
              - HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
                (purifiedGibbsTwoLevel (1 + ε)))
            + (HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p
                (purifiedGibbsTwoLevel (1 + ε))
              - HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
                (purifiedGibbsTwoLevel (1 + ε)))
            + (HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p
                (purifiedGibbsTwoLevel (1 + ε))
              - ApplyGate (purifiedGibbsReflection (1 + ε))
                (purifiedGibbsTwoLevel (1 + ε))) := by
        module
      rw [hsplit, toEuclidean_fromVec_add, toEuclidean_fromVec_add]
    rw [hEq]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

  have hfinal := hker.trans (htrans.trans
    (add_le_add (add_le_add e0' hhyb) e1))
  linarith

end Qatlib.Concepts.QuantumGibbs.SamplingCost
