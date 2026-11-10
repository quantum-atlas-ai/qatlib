/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.GroverArbAmp98.MainResults.Dynamics
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GroverArbAmp98.MainResults.TwoMeasurements

def successAt (Pav ΔP θ : ℝ) : ℝ := Pav - ΔP * Real.cos θ

lemma two_phase_sum (Pav ΔP θ : ℝ) :
    successAt Pav ΔP θ + successAt Pav ΔP (θ + Real.pi) = 2 * Pav := by
  unfold successAt
  rw [Real.cos_add_pi]
  ring

lemma one_ge_average (Pav ΔP θ : ℝ) (hΔ0 : 0 ≤ ΔP) :
    Pav ≤ max (successAt Pav ΔP θ) (successAt Pav ΔP (θ + Real.pi)) := by
  unfold successAt
  rw [Real.cos_add_pi]
  rcases le_total 0 (Real.cos θ) with hc | hc
  · have h2 : Pav ≤ Pav - ΔP * (-Real.cos θ) := by
      nlinarith [mul_nonneg hΔ0 hc]
    exact le_trans h2 (le_max_right _ _)
  · have h1 : Pav ≤ Pav - ΔP * Real.cos θ := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hΔ0 hc]
    exact le_trans h1 (le_max_left _ _)

theorem two_measurement_guarantee (Pav ΔP θ : ℝ) (hΔ0 : 0 ≤ ΔP) (hΔ : ΔP ≤ Pav) :
    (Pav + ΔP) / 2 ≤ max (successAt Pav ΔP θ) (successAt Pav ΔP (θ + Real.pi)) := by
  have hPav : (Pav + ΔP) / 2 ≤ Pav := by linarith
  exact le_trans hPav (one_ge_average Pav ΔP θ hΔ0)

lemma quarter_period_phase (ω T1 : ℝ) (hω : ω ≠ 0) :
    2 * ω * (T1 + Real.pi / (2 * ω)) = 2 * ω * T1 + Real.pi := by
  field_simp
  try ring

theorem source_two_measurement_strategy (Pav ΔP φ ω T1 : ℝ)
    (hΔ0 : 0 ≤ ΔP) (hΔ : ΔP ≤ Pav) (hω : ω ≠ 0) :
    (2 * ω * (T1 + Real.pi / (2 * ω)) = 2 * ω * T1 + Real.pi) ∧
    (Pav ≤ max (successAt Pav ΔP (2 * ω * T1 + 2 * φ))
        (successAt Pav ΔP (2 * ω * (T1 + Real.pi / (2 * ω)) + 2 * φ))) ∧
    ((Pav + ΔP) / 2 ≤ max (successAt Pav ΔP (2 * ω * T1 + 2 * φ))
        (successAt Pav ΔP (2 * ω * (T1 + Real.pi / (2 * ω)) + 2 * φ))) := by
  have hphase :
      2 * ω * (T1 + Real.pi / (2 * ω)) + 2 * φ = (2 * ω * T1 + 2 * φ) + Real.pi := by
    have h := quarter_period_phase ω T1 hω
    linarith
  refine ⟨quarter_period_phase ω T1 hω, ?_, ?_⟩
  · rw [hphase]
    exact one_ge_average Pav ΔP (2 * ω * T1 + 2 * φ) hΔ0
  · rw [hphase]
    exact two_measurement_guarantee Pav ΔP (2 * ω * T1 + 2 * φ) hΔ0 hΔ

theorem slowdown_factor_four (Pmax : ℝ) (hpos : 0 < Pmax) :
    (2 : ℝ) * (1 / (Pmax / 2)) = 4 * (1 / Pmax) := by
  field_simp
  try ring

theorem probMarked_eq_phase (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (x0 : Dynamics.Amps r m) (t : ℕ) :
    Dynamics.probMarked (Dynamics.orbit x0 t)
      = successAt (Dynamics.Pav x0) (Dynamics.DeltaP x0)
          (2 * Dynamics.omega r m * (t : ℝ) + (Dynamics.hC x0).arg) := by
  rw [Dynamics.probMarked_orbit_eq hr hm x0 t, Dynamics.re_rot_hC_cos r m x0 t]
  unfold successAt
  rw [show 2 * (Dynamics.omega r m * (t : ℝ) + (Dynamics.hC x0).arg / 2)
      = 2 * Dynamics.omega r m * (t : ℝ) + (Dynamics.hC x0).arg from by ring]

theorem source_two_measurement_dynamics (r m : ℕ) (x0 : Dynamics.Amps r m)
    (ω T1 : ℝ) (hω : ω ≠ 0) :
    (Dynamics.Pmax x0) / 2 ≤
      max (successAt (Dynamics.Pav x0) (Dynamics.DeltaP x0)
            (2 * ω * T1 + (Dynamics.hC x0).arg))
          (successAt (Dynamics.Pav x0) (Dynamics.DeltaP x0)
            (2 * ω * (T1 + Real.pi / (2 * ω)) + (Dynamics.hC x0).arg)) := by
  have hΔ0 := Dynamics.DeltaP_nonneg x0
  have hΔ := Dynamics.DeltaP_le_Pav x0
  have hphase : 2 * ω * (T1 + Real.pi / (2 * ω)) + (Dynamics.hC x0).arg
      = (2 * ω * T1 + (Dynamics.hC x0).arg) + Real.pi := by
    have h := quarter_period_phase ω T1 hω
    linarith
  have hPmax : Dynamics.Pmax x0 = Dynamics.Pav x0 + Dynamics.DeltaP x0 :=
    Dynamics.Pmax_eq x0
  rw [hphase]
  have hbound := two_measurement_guarantee (Dynamics.Pav x0) (Dynamics.DeltaP x0)
    (2 * ω * T1 + (Dynamics.hC x0).arg) hΔ0 hΔ
  linarith

end Qatlib.Papers.GroverArbAmp98.MainResults.TwoMeasurements
