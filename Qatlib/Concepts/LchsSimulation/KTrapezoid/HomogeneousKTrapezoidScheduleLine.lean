/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidScheduleStat
import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureLine
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

theorem homogeneous_k_trapezoid_schedule_of_quadrature
    (hq : HomogeneousKTrapezoidQuadrature) : HomogeneousKTrapezoidSchedule := by
  intro I _ _ L H s t ε lamL hL hH hPSD hHerm hst hε hbound
  (try dsimp only)
  let K := timeDependentLchsWindowCutoff (ε/2)
  let B := lamL*(t-s)
  let C := 2*(1+B+B^2)/Real.pi
  let M := max 1 (Nat.ceil (Real.sqrt ((2*(K : ℝ))^3*C/(6*ε))))
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hL0 : 0 ≤ lamL := (norm_nonneg _).trans (hbound s)
  have hB : 0 ≤ B := mul_nonneg hL0 (sub_nonneg.mpr hst)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi0 : 0 ≤ ∫ u in s..t, ‖L u‖ :=
    intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
  have hi : (∫ u in s..t, ‖L u‖) ≤ B := by
    have he := intervalIntegral.integral_mono_on (μ := volume) hst (hL.norm.intervalIntegrable s t)
      (intervalIntegrable_const (c := lamL)) (fun u _ => hbound u)
    simpa [B, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using! he
  have hCF : 2*(1+(∫ u in s..t, ‖L u‖)+(∫ u in s..t, ‖L u‖)^2)/Real.pi ≤ C := by
    dsimp [C]
    gcongr
  have hcut : 4/(Real.pi*(ε/2)) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 (Nat.ceil (4/(Real.pi*(ε/2))))))
  have htail : 2/(Real.pi*(K : ℝ)) ≤ ε/4 := by
    apply (div_le_iff₀ (mul_pos Real.pi_pos hKr)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < Real.pi*(ε/2))).mp hcut
    nlinarith
  have hceil : Real.sqrt ((2*(K : ℝ))^3*C/(6*ε)) ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hmceil : Nat.ceil (Real.sqrt ((2*(K : ℝ))^3*C/(6*ε))) ≤ M := le_max_right _ _
      exact_mod_cast hmceil)
  have hquad : (2*(K : ℝ))^3/(12*(M : ℝ)^2)*C ≤ ε/2 := by
    have hz : 0 ≤ (2*(K : ℝ))^3*C/(6*ε) := by positivity
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hceil
    rw [← pow_two, ← pow_two, Real.sq_sqrt hz] at hsquare
    have hraw := (div_le_iff₀ (by positivity : 0 < 6*ε)).1 hsquare
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 12*(M : ℝ)^2)).2
    nlinarith only [hraw]
  refine ⟨hM, ?_⟩
  have he := hq I L H s t K M hL hH hPSD hHerm hst hK hM
  exact he.trans ((add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hCF (by positivity))).trans (by linarith only [htail, hquad, hε.le]))

theorem homogeneousKTrapezoidSchedule : HomogeneousKTrapezoidSchedule :=
  homogeneous_k_trapezoid_schedule_of_quadrature homogeneousKTrapezoidQuadrature

end Qatlib.Concepts.LchsSimulation.KTrapezoid
