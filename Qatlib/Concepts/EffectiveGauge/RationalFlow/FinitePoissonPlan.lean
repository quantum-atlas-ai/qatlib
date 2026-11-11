/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CubicCutoffExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Finite Poisson Plan

Rational Flow constructions for Effective Gauge.
Defines `finitePoissonFrequencyCount`, `finitePoissonMesh`, `finitePoissonSampleAccuracy`.
Proves `finitePoissonFrequencyCount_pos`, `finitePoissonMesh_pos`, `finitePoissonSampleAccuracy_spec`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of finite Poisson Frequency Count in the Rational Flow construction. -/
def finitePoissonFrequencyCount (N : ℕ) : ℕ := (2*N+1)^3

/-- Definition of finite Poisson Mesh in the Rational Flow construction. -/
def finitePoissonMesh (C0 C1 : ℚ) (N : ℕ) (tolerance : ℚ) : ℕ :=
  max 1 (Nat.ceil (144*(finitePoissonFrequencyCount N : ℚ)*(C1+7*(N : ℚ)*C0)/tolerance))

/-- Definition of finite Poisson Sample Accuracy in the Rational Flow construction. -/
def finitePoissonSampleAccuracy (N : ℕ) (tolerance : ℚ) : ℚ :=
  tolerance/(96*(finitePoissonFrequencyCount N : ℚ))

/-- Definition of finite Poisson Mode Accuracy in the Rational Flow construction. -/
def finitePoissonModeAccuracy (C0 : ℚ) (N : ℕ) (tolerance : ℚ) : ℚ :=
  tolerance/(192*(finitePoissonFrequencyCount N : ℚ)*(C0+1))

/-- Definition of finite Poisson Period Accuracy in the Rational Flow construction. -/
def finitePoissonPeriodAccuracy (C0 : ℚ) (N : ℕ) (tolerance : ℚ) : ℚ :=
  tolerance/(4096*(finitePoissonFrequencyCount N : ℚ)*(C0+1)*((N : ℚ)+1))

/-- Original `finitePoissonFrequencyCount_pos` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonFrequencyCount_pos (N : ℕ) : 0<finitePoissonFrequencyCount N := by
  dsimp only [finitePoissonFrequencyCount]
  positivity

/-- Original `finitePoissonMesh_pos` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonMesh_pos (C0 C1 : ℚ) (N : ℕ) (tolerance : ℚ) :
    0<finitePoissonMesh C0 C1 N tolerance := lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)

/-- Original `finitePoissonSampleAccuracy_spec` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonSampleAccuracy_spec (N : ℕ) (tolerance : ℚ)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    0<finitePoissonSampleAccuracy N tolerance ∧ finitePoissonSampleAccuracy N tolerance ≤ 1 := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  have hJ1 : (1 : ℚ) ≤ finitePoissonFrequencyCount N := by
    exact_mod_cast (Nat.succ_le_iff.mpr (finitePoissonFrequencyCount_pos N))
  constructor
  · exact div_pos ht (by positivity)
  · apply (div_le_iff₀ (by positivity : (0 : ℚ)<96*(finitePoissonFrequencyCount N : ℚ))).mpr
    linarith

/-- Original `finitePoissonModeAccuracy_spec` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonModeAccuracy_spec (C0 : ℚ) (hC0 : 0 ≤ C0) (N : ℕ) (tolerance : ℚ)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    0<finitePoissonModeAccuracy C0 N tolerance ∧ finitePoissonModeAccuracy C0 N tolerance ≤ 1 := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  have hJ1 : (1 : ℚ) ≤ finitePoissonFrequencyCount N := by
    exact_mod_cast (Nat.succ_le_iff.mpr (finitePoissonFrequencyCount_pos N))
  constructor
  · exact div_pos ht (by positivity)
  · apply (div_le_iff₀ (by positivity : (0 : ℚ)<192*(finitePoissonFrequencyCount N : ℚ)*(C0+1))).mpr
    nlinarith [mul_nonneg hJ.le hC0]

/-- Original `finitePoissonPeriodAccuracy_spec` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonPeriodAccuracy_spec (C0 : ℚ) (hC0 : 0 ≤ C0) (N : ℕ) (tolerance : ℚ)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    0<finitePoissonPeriodAccuracy C0 N tolerance ∧ finitePoissonPeriodAccuracy C0 N tolerance ≤ 1 := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  have hJ1 : (1 : ℚ) ≤ finitePoissonFrequencyCount N := by
    exact_mod_cast (Nat.succ_le_iff.mpr (finitePoissonFrequencyCount_pos N))
  have hJC : 1 ≤ (finitePoissonFrequencyCount N : ℚ)*(C0+1) := by
    nlinarith [mul_nonneg hJ.le hC0]
  have hfull : 1 ≤ (finitePoissonFrequencyCount N : ℚ)*(C0+1)*((N : ℚ)+1) := by
    have hn : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    nlinarith [mul_nonneg (by linarith : 0 ≤ (finitePoissonFrequencyCount N : ℚ)*(C0+1)) hn]
  constructor
  · exact div_pos ht (by positivity)
  · apply (div_le_iff₀ (by positivity : (0 : ℚ)<
      4096*(finitePoissonFrequencyCount N : ℚ)*(C0+1)*((N : ℚ)+1))).mpr
    nlinarith

/-- Original `finitePoissonModePeriod_budget` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonModePeriod_budget (C0 : ℚ) (hC0 : 0 ≤ C0) (N : ℕ) (tolerance : ℚ)
    (ht : 0<tolerance) :
    3*(N : ℚ)*finitePoissonPeriodAccuracy C0 N tolerance ≤ finitePoissonModeAccuracy C0 N tolerance/2 := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  have hC : 0<C0+1 := by linarith
  have hN : (0 : ℚ)<(N : ℚ)+1 := by positivity
  have he : 0 ≤ finitePoissonPeriodAccuracy C0 N tolerance := div_nonneg ht.le (by positivity)
  have hd : 0 ≤ finitePoissonModeAccuracy C0 N tolerance := div_nonneg ht.le (by positivity)
  have hid : 64*((N : ℚ)+1)*finitePoissonPeriodAccuracy C0 N tolerance=
      3*finitePoissonModeAccuracy C0 N tolerance := by
    dsimp only [finitePoissonPeriodAccuracy,finitePoissonModeAccuracy]
    field_simp [hJ.ne',hC.ne',hN.ne']
    norm_num
  nlinarith

/-- Original `finitePoissonMesh_budget` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonMesh_budget (C0 C1 : ℚ) (N : ℕ) (tolerance : ℚ) (ht : 0<tolerance) :
    3*(C1+7*(N : ℚ)*C0)/(finitePoissonMesh C0 C1 N tolerance : ℚ) ≤
      tolerance/(48*(finitePoissonFrequencyCount N : ℚ)) := by
  have hM : (0 : ℚ)<finitePoissonMesh C0 C1 N tolerance := by
    exact_mod_cast finitePoissonMesh_pos C0 C1 N tolerance
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  have hceil : 144*(finitePoissonFrequencyCount N : ℚ)*(C1+7*(N : ℚ)*C0)/tolerance ≤
      (finitePoissonMesh C0 C1 N tolerance : ℚ) := by
    dsimp only [finitePoissonMesh]
    apply (Nat.le_ceil _).trans
    exact_mod_cast (le_max_right 1
      (Nat.ceil (144*(finitePoissonFrequencyCount N : ℚ)*(C1+7*(N : ℚ)*C0)/tolerance)))
  have hprod := (div_le_iff₀ ht).mp hceil
  apply (div_le_iff₀ hM).mpr
  rw [show tolerance/(48*(finitePoissonFrequencyCount N : ℚ))*(finitePoissonMesh C0 C1 N tolerance : ℚ)=
    ((finitePoissonMesh C0 C1 N tolerance : ℚ)*tolerance)/(48*(finitePoissonFrequencyCount N : ℚ)) by ring]
  apply (le_div_iff₀ (by positivity : (0 : ℚ)<48*(finitePoissonFrequencyCount N : ℚ))).mpr
  nlinarith

/-- Original `finitePoissonSampleMode_budget` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonSampleMode_budget (C0 : ℚ) (hC0 : 0 ≤ C0) (N : ℕ) (tolerance : ℚ)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    finitePoissonSampleAccuracy N tolerance+
      (C0+finitePoissonSampleAccuracy N tolerance)*finitePoissonModeAccuracy C0 N tolerance ≤
        tolerance/(64*(finitePoissonFrequencyCount N : ℚ)) := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  have hC : 0<C0+1 := by linarith
  have hs := (finitePoissonSampleAccuracy_spec N tolerance ht ht1).2
  have hd := (finitePoissonModeAccuracy_spec C0 hC0 N tolerance ht ht1).1.le
  have hsum : C0+finitePoissonSampleAccuracy N tolerance ≤ C0+1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hsum hd
  have hcancel : (C0+1)*finitePoissonModeAccuracy C0 N tolerance=
      tolerance/(192*(finitePoissonFrequencyCount N : ℚ)) := by
    dsimp only [finitePoissonModeAccuracy]
    field_simp [hJ.ne',hC.ne']
  calc
    _ ≤ finitePoissonSampleAccuracy N tolerance+(C0+1)*finitePoissonModeAccuracy C0 N tolerance :=
      add_le_add le_rfl hprod
    _ = tolerance/(64*(finitePoissonFrequencyCount N : ℚ)) := by
      rw [hcancel]
      dsimp only [finitePoissonSampleAccuracy]
      field_simp [hJ.ne']
      norm_num

/-- Original `finitePoissonCoefficient_budget` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonCoefficient_budget (C0 C1 : ℚ) (hC0 : 0 ≤ C0) (N : ℕ) (tolerance : ℚ)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    3*(C1+7*(N : ℚ)*C0)/(finitePoissonMesh C0 C1 N tolerance : ℚ)+
      (finitePoissonSampleAccuracy N tolerance+
        (C0+finitePoissonSampleAccuracy N tolerance)*finitePoissonModeAccuracy C0 N tolerance) ≤
          tolerance/(24*(finitePoissonFrequencyCount N : ℚ)) := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by exact_mod_cast finitePoissonFrequencyCount_pos N
  calc
    _ ≤ tolerance/(48*(finitePoissonFrequencyCount N : ℚ))+
        tolerance/(64*(finitePoissonFrequencyCount N : ℚ)) := add_le_add
      (finitePoissonMesh_budget C0 C1 N tolerance ht)
      (finitePoissonSampleMode_budget C0 hC0 N tolerance ht ht1)
    _ = 7*tolerance/(192*(finitePoissonFrequencyCount N : ℚ)) := by
      field_simp [hJ.ne']
      norm_num
    _ ≤ tolerance/(24*(finitePoissonFrequencyCount N : ℚ)) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℚ)<192*(finitePoissonFrequencyCount N : ℚ))
        (by positivity : (0 : ℚ)<24*(finitePoissonFrequencyCount N : ℚ))).mpr
      nlinarith [mul_nonneg ht.le hJ.le]

/-- Original `finitePoissonCutoff_tail_budget` guarantee for the `FinitePoissonPlan` construction; the complete source hypotheses are retained. -/
theorem finitePoissonCutoff_tail_budget (C6 tolerance : ℚ) (ht : 0<tolerance) :
    156*C6/(finitePoissonCutoff C6 tolerance : ℚ)^3 ≤ 39*tolerance/100 := by
  have hN : (0 : ℚ)<finitePoissonCutoff C6 tolerance := by exact_mod_cast finitePoissonCutoff_pos C6 tolerance
  apply (div_le_iff₀ (pow_pos hN 3)).mpr
  nlinarith [finitePoissonCutoff_budget C6 tolerance ht]

end Qatlib.Concepts.EffectiveGauge.RationalFlow
