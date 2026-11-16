/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanError17.MainResults.Core.SourceModel
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


/-! # Geometric convergence inside the Carleman radius, arXiv:1711.02552v1 Eq. (28).
The theorem concerns the geometric factor only; a bound on the actual ODE truncation
error still needs the tensor-power and analytic bridges.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace Qatlib.Papers.CarlemanError17.MainResults.Radius
open Qatlib.Papers.CarlemanError17.MainResults.Core

/-- The scalar geometric factor converges to zero before its logarithmic radius. -/
theorem geometric_radius (β a t : ℝ) (hβ : 0 < β) (ha : 0 < a) (ht : 0 < t)
    (hT : t < (1 / a) * Real.log (1 + 1 / β)) :
    Tendsto (fun N : ℕ => (β * (Real.exp (a * t) - 1)) ^ N) atTop (𝓝 0) := by
  have hlogarg : 0 < 1 + 1 / β := by positivity
  have hat : a * t < Real.log (1 + 1 / β) := by
    have hh : t < Real.log (1 + 1 / β) / a := by simpa [div_eq_mul_inv, mul_comm] using hT
    have h := (lt_div_iff₀ ha).mp hh
    simpa [mul_comm] using h
  have hexp : Real.exp (a * t) < 1 + 1 / β := by
    calc Real.exp (a * t) < Real.exp (Real.log (1 + 1 / β)) := Real.exp_lt_exp.mpr hat
      _ = 1 + 1 / β := Real.exp_log hlogarg
  have hnonneg : 0 ≤ β * (Real.exp (a * t) - 1) := by
    exact mul_nonneg hβ.le (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity)))
  have hlt : β * (Real.exp (a * t) - 1) < 1 := by
    have hmul := mul_lt_mul_of_pos_left hexp hβ
    have hcancel : β * (1 / β) = 1 := by field_simp
    nlinarith
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt

/-- The initial nonlinear-to-linear norm ratio in the source error bound. -/
def beta0 {n : ℕ} (x0 : TP n 1 → ℝ) (F1 : Matrix (TP n 1) (TP n 1) ℝ)
    (F2 : Matrix (TP n 1) (TP n 2) ℝ) : ℝ :=
  vecSup x0 * matSup F2 / matSup F1

/-- The source convergence radius associated with the initial norm ratio. -/
def Tstar {n : ℕ} (x0 : TP n 1 → ℝ) (F1 : Matrix (TP n 1) (TP n 1) ℝ)
    (F2 : Matrix (TP n 1) (TP n 2) ℝ) : ℝ :=
  (1 / matSup F1) * Real.log (1 + 1 / beta0 x0 F1 F2)

/-- The complete legacy geometric-radius contract follows by substituting its norm ratio. -/
theorem theorem_four_three_radius {n : ℕ} (_hn : 0 < n)
    (x0 : TP n 1 → ℝ) (F1 : Matrix (TP n 1) (TP n 1) ℝ)
    (F2 : Matrix (TP n 1) (TP n 2) ℝ)
    (hβ : 0 < beta0 x0 F1 F2) (hF1 : 0 < matSup F1)
    (t : ℝ) (ht : 0 < t) (htT : t < Tstar x0 F1 F2) :
    Tendsto (fun N : ℕ => (beta0 x0 F1 F2 * (Real.exp (matSup F1 * t) - 1)) ^ N)
      atTop (𝓝 0) :=
  geometric_radius (beta0 x0 F1 F2) (matSup F1) t hβ hF1 ht htT

end Qatlib.Papers.CarlemanError17.MainResults.Radius
