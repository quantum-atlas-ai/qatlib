/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.StationaryPhase.StationaryPhaseVarianceStat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.StationaryPhase
open MeasureTheory Set
open scoped BigOperators

private abbrev coordinateMeasure : Measure ℝ := volume.restrict (Icc (-1/2) (1/2 : ℝ))

private instance coordinate_probability : IsProbabilityMeasure coordinateMeasure := by
  constructor
  norm_num [coordinateMeasure, Real.volume_Icc]

private theorem coordinate_first : ∫ x, x ∂coordinateMeasure = 0 := by
  change (∫ x in Icc (-1/2) (1/2 : ℝ), x) = 0
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

private theorem coordinate_second : ∫ x, x*x ∂coordinateMeasure = 1/12 := by
  change (∫ x in Icc (-1/2) (1/2 : ℝ), x*x) = 1/12
  simp_rw [← pow_two]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
  norm_num

private theorem cube_first (d : ℕ) (i : Fin d) : ∫ u, u i ∂stationaryPhaseCube d = 0 := by
  rw [stationaryPhaseCube, integral_eval]
  exact coordinate_first

private def pairFactor {d : ℕ} (i j k : Fin d) (x : ℝ) : ℝ :=
  (if k=i then x else 1) * (if k=j then x else 1)

private theorem pair_product {d : ℕ} (i j : Fin d) (u : Fin d → ℝ) :
    (∏ k, pairFactor i j k (u k)) = u i * u j := by
  classical
  simp only [pairFactor]
  rw [Finset.prod_mul_distrib]
  simp

private theorem pair_integrable {d : ℕ} (i j : Fin d) :
    Integrable (fun u => u i * u j) (stationaryPhaseCube d) := by
  classical
  change Integrable _ (Measure.pi fun _ : Fin d => coordinateMeasure)
  have hc (k : Fin d) : Continuous (pairFactor i j k) := by
    unfold pairFactor
    split_ifs <;> fun_prop
  simpa only [pair_product] using
    Integrable.fintype_prod (fun k => (hc k).continuousOn.integrableOn_Icc)

private theorem cube_second (d : ℕ) (i j : Fin d) :
    ∫ u, u i * u j ∂stationaryPhaseCube d = if i=j then 1/12 else 0 := by
  classical
  change (∫ u, u i * u j ∂Measure.pi fun _ : Fin d => coordinateMeasure) = _
  simp_rw [← pair_product i j]
  rw [integral_fintype_prod_eq_prod]
  by_cases hij : i=j
  · subst j
    have hf (k : Fin d) : (∫ x, pairFactor i i k x ∂coordinateMeasure) =
        if k=i then 1/12 else 1 := by
      by_cases hk : k=i
      · simp only [pairFactor, hk, ite_true]
        exact coordinate_second
      · simp [pairFactor, hk]
    simp_rw [hf]
    simp
  · have hz : (∫ x, pairFactor i j i x ∂coordinateMeasure) = 0 := by
      simpa [pairFactor, hij] using coordinate_first
    rw [if_neg hij]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

private theorem cube_linear (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (∫ u, ∑ j, A i j * u j ∂stationaryPhaseCube d) = 0 ∧
    (∫ u, (∑ j, A i j * u j)^2 ∂stationaryPhaseCube d) = (1/12)*∑ j, (A i j)^2 := by
  classical
  have hi (j : Fin d) : Integrable (fun u => u j) (stationaryPhaseCube d) :=
    integrable_eval continuous_id.continuousOn.integrableOn_Icc
  constructor
  · rw [integral_finsetSum _ (fun j _ => (hi j).const_mul (A i j))]
    simp_rw [integral_const_mul, cube_first, mul_zero]
    simp
  · have he (u : Fin d → ℝ) : (∑ j, A i j * u j)^2 =
        ∑ j, ∑ k, (A i j * A i k) * (u j * u k) := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => (pair_integrable j k).const_mul (A i j*A i k)))]
    simp_rw [integral_finsetSum _ (fun k _ => (pair_integrable _ k).const_mul _),
      integral_const_mul, cube_second]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem variance_units (n : ℕ) (l m S : ℝ) (hl : 0 < l) (hm : 0 < m)
    (hS : 0 ≤ S) :
    (m/(2^n : ℝ))*Real.sqrt ((2^n : ℝ)^2*l^2/(12*m^2)*S) =
      l/(2*Real.sqrt 3)*Real.sqrt S := by
  have hN : (2^n : ℝ) ≠ 0 := by positivity
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt ((2^n : ℝ)^2*l^2/(12*m^2)*S) =
      ((2^n : ℝ)*l/(m*2*Real.sqrt 3))*Real.sqrt S := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    rw [mul_pow, Real.sq_sqrt hS]
    field_simp
    nlinarith [hs]
  rw [hr]
  field_simp

theorem stationaryPhaseVariance : StationaryPhaseVariance := by
  classical
  refine ⟨cube_first, cube_second, cube_linear, ?_, ?_⟩
  · intro d n l m H i hl hm
    constructor
    · have he := (cube_linear d (fun i j => (2^n : ℝ)*l/m*H i j) i).2
      rw [he]
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      field_simp
    · exact variance_units n l m _ hl hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · intro d _n l m D H i hl _ hD hH
    have hsum : (∑ j, (H i j)^2) ≤ (d : ℝ)*D^2 := by
      calc
        _ ≤ ∑ _j : Fin d, D^2 := by
          apply Finset.sum_le_sum
          intro j _
          have hh := hH i j
          have ha := abs_nonneg (H i j)
          nlinarith [sq_abs (H i j)]
        _ = _ := by simp
    have hs : Real.sqrt (∑ j, (H i j)^2) ≤ D*Real.sqrt d := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · rw [mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith [hsum]
    calc
      _ ≤ l/(2*Real.sqrt 3)*(D*Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring

end Qatlib.Concepts.GradientOracle.StationaryPhase
