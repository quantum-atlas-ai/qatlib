/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerWinding
import Mathlib.Tactic.FieldSimp

/-! # Positive-margin point seeds derived from the spin, not a supplied lift -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of north Seed in the Hopf Atlas construction. -/
def northSeed (s : ℍ) : ℍ :=
  let a := Real.sqrt ((1+s.imI)/2)
  ⟨a, 0, s.imK/(2*a), -s.imJ/(2*a)⟩

/-- Original `northSeed_norm` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem northSeed_norm (s : ℍ) (hr : s.re = 0) (hn : ‖s‖ = 1)
    (hc : -(1/2 : ℝ) < s.imI) : ‖northSeed s‖ = 1 := by
  let a := Real.sqrt ((1+s.imI)/2)
  have hp : 0 < (1+s.imI)/2 := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr hp
  have ha2 : a^2 = (1+s.imI)/2 := Real.sq_sqrt hp.le
  have ha4 := congrArg (fun x : ℝ => x^2) ha2
  have hs := (normSq_eq_one_iff s).mpr hn
  simp only [Quaternion.normSq_def', hr, zero_pow (by decide : 2 ≠ 0), zero_add] at hs
  apply (normSq_eq_one_iff _).mp
  rw [Quaternion.normSq_def']
  change a^2+0^2+(s.imK/(2*a))^2+(-s.imJ/(2*a))^2 = 1
  field_simp
  nlinarith

/-- Original `northSeed_hopf` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem northSeed_hopf (s : ℍ) (hr : s.re = 0) (hn : ‖s‖ = 1)
    (hc : -(1/2 : ℝ) < s.imI) : hopf (northSeed s) = s := by
  let a := Real.sqrt ((1+s.imI)/2)
  have hp : 0 < (1+s.imI)/2 := by linarith
  have ha : a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have ha2 : a^2 = (1+s.imI)/2 := Real.sq_sqrt hp.le
  have hq := (normSq_eq_one_iff _).mpr (northSeed_norm s hr hn hc)
  rw [Quaternion.normSq_def'] at hq
  change a^2+0^2+(s.imK/(2*a))^2+(-s.imJ/(2*a))^2 = 1 at hq
  ext
  · rw [hopf_re, hr]
  · rw [hopf_imI]
    change a^2+0^2-(s.imK/(2*a))^2-(-s.imJ/(2*a))^2=s.imI
    nlinarith
  · rw [hopf_imJ]
    change 2*(0*(s.imK/(2*a))-a*(-s.imJ/(2*a)))=s.imJ
    field_simp
    ring
  · rw [hopf_imK]
    change 2*(a*(s.imK/(2*a))+0*(-s.imJ/(2*a)))=s.imK
    field_simp
    ring

/-- Original `northSeed_margin` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem northSeed_margin (s : ℍ) (hc : -(1/2 : ℝ) < s.imI) :
    (1/2 : ℝ) < (northSeed s).re := by
  have hp : 0 < (1+s.imI)/2 := by linarith
  change (1/2 : ℝ) < Real.sqrt ((1+s.imI)/2)
  apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/2) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hp.le]
  linarith

/-- Definition of south Seed in the Hopf Atlas construction. -/
def southSeed (s : ℍ) : ℍ :=
  let c := Real.sqrt ((1-s.imI)/2)
  ⟨s.imK/(2*c), s.imJ/(2*c), c, 0⟩

/-- Original `southSeed_norm` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem southSeed_norm (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (hc : s.imI < (1/2 : ℝ)) : ‖southSeed s‖=1 := by
  let c := Real.sqrt ((1-s.imI)/2)
  have hp : 0 < (1-s.imI)/2 := by linarith
  have hpos : 0 < c := Real.sqrt_pos.mpr hp
  have h2 : c^2=(1-s.imI)/2 := Real.sq_sqrt hp.le
  have h4 := congrArg (fun x : ℝ => x^2) h2
  have hs := (normSq_eq_one_iff s).mpr hn
  simp only [Quaternion.normSq_def', hr, zero_pow (by decide : 2 ≠ 0), zero_add] at hs
  apply (normSq_eq_one_iff _).mp
  rw [Quaternion.normSq_def']
  change (s.imK/(2*c))^2+(s.imJ/(2*c))^2+c^2+0^2=1
  field_simp
  nlinarith

/-- Original `southSeed_hopf` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem southSeed_hopf (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (hc : s.imI < (1/2 : ℝ)) : hopf (southSeed s)=s := by
  let c := Real.sqrt ((1-s.imI)/2)
  have hp : 0 < (1-s.imI)/2 := by linarith
  have hne : c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have h2 : c^2=(1-s.imI)/2 := Real.sq_sqrt hp.le
  have hq := (normSq_eq_one_iff _).mpr (southSeed_norm s hr hn hc)
  rw [Quaternion.normSq_def'] at hq
  change (s.imK/(2*c))^2+(s.imJ/(2*c))^2+c^2+0^2=1 at hq
  ext
  · rw [hopf_re, hr]
  · rw [hopf_imI]
    change (s.imK/(2*c))^2+(s.imJ/(2*c))^2-c^2-0^2=s.imI
    nlinarith
  · rw [hopf_imJ]
    change 2*((s.imJ/(2*c))*c-(s.imK/(2*c))*0)=s.imJ
    field_simp; ring
  · rw [hopf_imK]
    change 2*((s.imK/(2*c))*c+(s.imJ/(2*c))*0)=s.imK
    field_simp; ring

/-- Original `southSeed_margin` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem southSeed_margin (s : ℍ) (hc : s.imI < (1/2 : ℝ)) :
    (1/2 : ℝ) < (southSeed s).imJ := by
  have hp : 0 < (1-s.imI)/2 := by linarith
  change (1/2 : ℝ) < Real.sqrt ((1-s.imI)/2)
  apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/2) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hp.le]
  linarith

/-- Original `chart_cover` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem chart_cover (s : Quaternion ℝ) :
    -(1/2 : ℝ) < s.imI ∨ s.imI < (1/2 : ℝ) := by
  by_cases h : -(1/2 : ℝ) < s.imI
  · exact Or.inl h
  · right
    linarith

/-- Original `north_constant_spin_lift` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem north_constant_spin_lift (s : Quaternion ℝ) (hr : s.re=0) (hn : ‖s‖=1)
    (hc : -(1/2 : ℝ) < s.imI) (n : Fin 3 → ℤ) :
    IsPeriodicField (windingLift n (northSeed s)) ∧
    IsSmoothUnitLift (fun _ => s) (windingLift n (northSeed s)) ∧
    IsSolenoidal (windingLift n (northSeed s)) := by
  refine ⟨windingLift_periodic n _, ?_, windingLift_solenoidal n _ (northSeed_norm s hr hn hc)⟩
  simpa only [northSeed_hopf s hr hn hc] using
    windingLift_isSmoothUnitLift n (northSeed s) (northSeed_norm s hr hn hc)

/-- Original `south_constant_spin_lift` guarantee for the `Seeds` construction; the complete source hypotheses are retained. -/
theorem south_constant_spin_lift (s : Quaternion ℝ) (hr : s.re=0) (hn : ‖s‖=1)
    (hc : s.imI < (1/2 : ℝ)) (n : Fin 3 → ℤ) :
    IsPeriodicField (windingLift n (southSeed s)) ∧
    IsSmoothUnitLift (fun _ => s) (windingLift n (southSeed s)) ∧
    IsSolenoidal (windingLift n (southSeed s)) := by
  refine ⟨windingLift_periodic n _, ?_, windingLift_solenoidal n _ (southSeed_norm s hr hn hc)⟩
  simpa only [southSeed_hopf s hr hn hc] using
    windingLift_isSmoothUnitLift n (southSeed s) (southSeed_norm s hr hn hc)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
