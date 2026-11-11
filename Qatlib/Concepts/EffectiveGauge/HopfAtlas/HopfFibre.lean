/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Model

/-!
# Hopf Fibre

Hopf Atlas constructions for Effective Gauge.
Proves `unit_self_mul_star`, `unit_star_mul_self`, `sameHopf_ratio_commutes`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `unit_self_mul_star` guarantee for the `HopfFibre` construction; the complete source hypotheses are retained. -/
theorem unit_self_mul_star (q : ℍ) (hq : ‖q‖=1) : q*star q=1 := by
  rw [Quaternion.self_mul_star,(normSq_eq_one_iff q).mpr hq]
  rfl

/-- Original `unit_star_mul_self` guarantee for the `HopfFibre` construction; the complete source hypotheses are retained. -/
theorem unit_star_mul_self (q : ℍ) (hq : ‖q‖=1) : star q*q=1 := by
  rw [Quaternion.star_mul_self,(normSq_eq_one_iff q).mpr hq]
  rfl

/-- The left fibre ratio of unit lifts with the same Hopf image commutes
with i; this does not assume a global real phase. -/
theorem sameHopf_ratio_commutes (q r : ℍ) (hq : ‖q‖=1) (hr : ‖r‖=1)
    (h : hopf r=hopf q) : iAxis*(r*star q)=(r*star q)*iAxis := by
  calc
    _ = (r*star r)*iAxis*r*star q := by rw [unit_self_mul_star r hr]; simp only [one_mul,mul_assoc]
    _ = r*hopf r*star q := by simp only [hopf,mul_assoc]
    _ = r*hopf q*star q := by rw [h]
    _ = (r*star q)*iAxis*(q*star q) := by simp only [hopf,mul_assoc]
    _ = _ := by rw [unit_self_mul_star q hq,mul_one]

/-- Original `commutes_iAxis_components` guarantee for the `HopfFibre` construction; the complete source hypotheses are retained. -/
theorem commutes_iAxis_components (z : ℍ) (h : iAxis*z=z*iAxis) : z.imJ=0 ∧ z.imK=0 := by
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  simp [iAxis] at hj hk
  constructor <;> linarith

/-- Original `sameHopf_ratio_components` guarantee for the `HopfFibre` construction; the complete source hypotheses are retained. -/
theorem sameHopf_ratio_components (q r : ℍ) (hq : ‖q‖=1) (hr : ‖r‖=1)
    (h : hopf r=hopf q) : (r*star q).imJ=0 ∧ (r*star q).imK=0 :=
  commutes_iAxis_components _ (sameHopf_ratio_commutes q r hq hr h)

/-- Original `sameHopf_ratio_norm` guarantee for the `HopfFibre` construction; the complete source hypotheses are retained. -/
theorem sameHopf_ratio_norm (q r : ℍ) (hq : ‖q‖=1) (hr : ‖r‖=1) : ‖r*star q‖=1 := by
  simp [norm_mul,norm_star,hq,hr]

/-- Original `sameHopf_ratio_action` guarantee for the `HopfFibre` construction; the complete source hypotheses are retained. -/
theorem sameHopf_ratio_action (q r : ℍ) (hq : ‖q‖=1) : (r*star q)*q=r := by
  rw [mul_assoc,unit_star_mul_self q hq,mul_one]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
