/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleySource
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# Finite rational parameter selection for the integer execution

The square root is computed with integer sqrt and one rational comparison.
The precision is the least p with 2^(-p) ≤ tolerance/4. No real comparison or
unbounded search occurs in these definitions. This covers the transport
planner, not source-program runtime or the full periodic-reference backend.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of cayley Ceil Sqrt in the Rational Flow construction. -/
def cayleyCeilSqrt (a : ℚ) : ℕ :=
  let r := Nat.sqrt (Nat.floor a)
  if a ≤ (r : ℚ)^2 then r else r+1

/-- Definition of cayley Steps in the Rational Flow construction. -/
def cayleySteps (K M tolerance : ℚ) : ℕ :=
  max (max 1 (Nat.ceil (M/tolerance))) (cayleyCeilSqrt ((K+1)^3/(3*tolerance)))

/-- Definition of cayley Precision in the Rational Flow construction. -/
def cayleyPrecision (tolerance : ℚ) : ℕ := Nat.clog 2 (Nat.ceil (4/tolerance))

/-- Definition of cayley Planned Execution in the Rational Flow construction. -/
def cayleyPlannedExecution (K M tolerance : ℚ) (oracle : ℚ × ℕ → Fin 3 → ℤ) : CayleyIntegerState :=
  cayleyOracleExecution (cayleySteps K M tolerance) (cayleyPrecision tolerance) oracle

/-- Original `cayleyCeilSqrt_sq` guarantee for the `CayleyBudget` construction; the complete source hypotheses are retained. -/
theorem cayleyCeilSqrt_sq (a : ℚ) : a ≤ (cayleyCeilSqrt a : ℚ)^2 := by
  simp only [cayleyCeilSqrt]
  split_ifs with h
  · exact h
  · have hf : a < (Nat.floor a : ℚ)+1 := Nat.lt_floor_add_one a
    have hs : Nat.floor a+1 ≤ (Nat.sqrt (Nat.floor a)+1)^2 := Nat.succ_le_succ_sqrt' _
    have hs' : (Nat.floor a : ℚ)+1 ≤ ((Nat.sqrt (Nat.floor a) : ℚ)+1)^2 := by exact_mod_cast hs
    simpa only [Nat.cast_add,Nat.cast_one] using hf.le.trans hs'

/-- Original `cayleySteps_spec` guarantee for the `CayleyBudget` construction; the complete source hypotheses are retained. -/
theorem cayleySteps_spec (K M tolerance : ℚ) :
    0<cayleySteps K M tolerance ∧ M/tolerance ≤ cayleySteps K M tolerance ∧
      (K+1)^3/(3*tolerance) ≤ (cayleySteps K M tolerance : ℚ)^2 := by
  have h1 : 1 ≤ cayleySteps K M tolerance := (le_max_left _ _).trans (le_max_left _ _)
  have hm : Nat.ceil (M/tolerance) ≤ cayleySteps K M tolerance :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hs : cayleyCeilSqrt ((K+1)^3/(3*tolerance)) ≤ cayleySteps K M tolerance := le_max_right _ _
  refine ⟨Nat.lt_of_lt_of_le (by decide) h1,(Nat.le_ceil _).trans (by exact_mod_cast hm),?_⟩
  exact (cayleyCeilSqrt_sq _).trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) 2)

/-- Original `cayleyPrecision_spec` guarantee for the `CayleyBudget` construction; the complete source hypotheses are retained. -/
theorem cayleyPrecision_spec (tolerance : ℚ) (ht : 0<tolerance) :
    (2^cayleyPrecision tolerance : ℚ)⁻¹ ≤ tolerance/4 := by
  have hpow : Nat.ceil (4/tolerance) ≤ 2^cayleyPrecision tolerance := Nat.le_pow_clog (by decide) _
  have h : 4/tolerance ≤ (2^cayleyPrecision tolerance : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpow)
  have hp : (0 : ℚ)<2^cayleyPrecision tolerance := by positivity
  apply (inv_le_iff_one_le_mul₀ hp).mpr
  have hh := (div_le_iff₀ ht).mp h
  nlinarith

/-- Original `cayleyPrecision_minimal` guarantee for the `CayleyBudget` construction; the complete source hypotheses are retained. -/
theorem cayleyPrecision_minimal (tolerance : ℚ) (ht : 0<tolerance) (p : ℕ)
    (hp : (2^p : ℚ)⁻¹ ≤ tolerance/4) : cayleyPrecision tolerance ≤ p := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ ht).mpr
  have hpos : (0 : ℚ)<2^p := by positivity
  have h := (inv_le_iff_one_le_mul₀ hpos).mp hp
  push_cast
  nlinarith

noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff
open Set

/-- Original `cayleyBudget_le` guarantee for the `CayleyBudget` construction; the complete source hypotheses are retained. -/
theorem cayleyBudget_le (K M tolerance : ℝ) (hK : 0 ≤ K) (ht : 0<tolerance)
    (ht1 : tolerance ≤ 1) (D p : ℕ) (hD : 0<D)
    (hM : M/tolerance ≤ D) (hc : (K+1)^3/(3*tolerance) ≤ (D : ℝ)^2)
    (hp : (2^p : ℝ)⁻¹ ≤ tolerance/4) :
    M/(2*(D : ℝ))+(2^p : ℝ)⁻¹+(K+(2^p : ℝ)⁻¹)^3/(12*(D : ℝ)^2) ≤ tolerance := by
  have hd : (0 : ℝ)<D := by exact_mod_cast hD
  have hfirst : M/(2*(D : ℝ)) ≤ tolerance/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_le_iff₀ ht).mp hM
    nlinarith
  have he : (2^p : ℝ)⁻¹ ≤ 1 := by linarith
  have hcub : (K+(2^p : ℝ)⁻¹)^3 ≤ (K+1)^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hthird : (K+(2^p : ℝ)⁻¹)^3/(12*(D : ℝ)^2) ≤ tolerance/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_le_iff₀ (by positivity : 0<3*tolerance)).mp hc
    nlinarith
  linarith

/-- Computable selected parameters consume the fixed exact source producer.
Only the dyadic coefficient accuracy and source regularity are promises. -/
theorem cayleyPlannedSource_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (z : TransversePoint)
    (x : ℝ) (hx : 0 ≤ x ∧ x ≤ physicalPeriod) (K M tolerance : ℚ)
    (hK : 0 ≤ K) (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (oracle : ℚ × ℕ → Fin 3 → ℤ)
    (hbound : ∀ t ∈ Icc 0 1, ‖normalizedSourceGenerator v z x t‖ ≤ (K : ℝ))
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      ‖normalizedSourceGenerator v z x t-normalizedSourceGenerator v z x s‖ ≤ (M : ℝ)*|t-s|)
    (horacle : ∀ j < cayleySteps K M tolerance,
      ‖dyadicCoefficient (cayleyPrecision tolerance)
        (oracle ((j : ℚ)/(cayleySteps K M tolerance : ℚ),cayleyPrecision tolerance))-
        normalizedSourceGenerator v z x ((j : ℝ)/(cayleySteps K M tolerance : ℝ))‖ ≤
          (2^cayleyPrecision tolerance : ℝ)⁻¹)
    (initial : ℍ) (delta0 : ℝ) (hinitial : ‖initial-q₀‖ ≤ delta0) :
    ‖initial*decodeCayleyState (cayleyPlannedExecution K M tolerance oracle)-
      sourceLiftExtension v hv q₀ h₀ (z,x)‖ ≤ delta0+(tolerance : ℝ) := by
  obtain ⟨hd,hm,hc⟩ := cayleySteps_spec K M tolerance
  have hpR : (((2^cayleyPrecision tolerance : ℚ)⁻¹ : ℚ) : ℝ) ≤ ((tolerance/4 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (cayleyPrecision_spec tolerance ht)
  push_cast at hpR
  have hb := cayleyBudget_le (K : ℝ) M tolerance (by exact_mod_cast hK) (by exact_mod_cast ht)
    (by exact_mod_cast ht1) (cayleySteps K M tolerance) (cayleyPrecision tolerance) hd
    (by exact_mod_cast hm) (by exact_mod_cast hc)
    hpR
  have he := cayleySourceLine_error v hv hu q₀ h₀ z x hx _ _ hd oracle K M hbound hlip horacle initial delta0 hinitial
  exact he.trans (by linarith)

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
