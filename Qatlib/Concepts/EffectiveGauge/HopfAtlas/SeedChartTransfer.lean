/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseChartUniqueness

set_option backward.isDefEq.respectTransparency false

/-!
# Seed Chart Transfer

Hopf Atlas constructions for Effective Gauge.
Defines `seedChartTransition`, `constantLeftGauge`.
Proves `seedChartTransition_spec`, `seedChartTransition_cocycle`, `constantLeftGauge_contDiff`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of seed Chart Transition in the Hopf Atlas construction. -/
def seedChartTransition (fromChart toChart : SeedChart) (s : ℍ) : ℍ :=
  exactChartSeed toChart s*star (exactChartSeed fromChart s)

/-- Original `seedChartTransition_spec` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem seedChartTransition_spec (a b : SeedChart) (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (ha : match a with | .north => -(1/2 : ℝ)<s.imI | .south => s.imI<(1/2 : ℝ))
    (hb : match b with | .north => -(1/2 : ℝ)<s.imI | .south => s.imI<(1/2 : ℝ)) :
    ‖seedChartTransition a b s‖=1 ∧
      ((seedChartTransition a b s).imJ=0 ∧ (seedChartTransition a b s).imK=0) ∧
      seedChartTransition a b s*exactChartSeed a s=exactChartSeed b s := by
  have hA := exactChartSeed_spec a s hr hn ha
  have hB := exactChartSeed_spec b s hr hn hb
  exact ⟨sameHopf_ratio_norm _ _ hA.1 hB.1,
    sameHopf_ratio_components _ _ hA.1 hB.1 (hB.2.1.trans hA.2.1.symm),
    sameHopf_ratio_action _ _ hA.1⟩

/-- Transition composition has the left-multiplication order. -/
theorem seedChartTransition_cocycle (a b c : SeedChart) (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (hb : match b with | .north => -(1/2 : ℝ)<s.imI | .south => s.imI<(1/2 : ℝ)) :
    seedChartTransition b c s*seedChartTransition a b s=seedChartTransition a c s := by
  have hB := (exactChartSeed_spec b s hr hn hb).1
  unfold seedChartTransition
  calc
    _ = exactChartSeed c s*(star (exactChartSeed b s)*exactChartSeed b s)*star (exactChartSeed a s) := by
      simp only [mul_assoc]
    _ = _ := by rw [unit_star_mul_self _ hB,mul_one]

/-- Definition of constant Left Gauge in the Hopf Atlas construction. -/
def constantLeftGauge (c : ℍ) (q : QuaternionField) : QuaternionField := fun x => c*q x

/-- Original `constantLeftGauge_contDiff` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem constantLeftGauge_contDiff (c : ℍ) (q : QuaternionField) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (constantLeftGauge c q) := contDiff_const.mul hq

/-- Original `constantLeftGauge_periodic` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem constantLeftGauge_periodic (c : ℍ) (q : QuaternionField) (hp : IsPeriodicField q) :
    IsPeriodicField (constantLeftGauge c q) := by intro x n; simp only [constantLeftGauge,hp x n]

/-- Original `constantLeftGauge_norm` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem constantLeftGauge_norm (c : ℍ) (hu : ‖c‖=1) (q : QuaternionField)
    (hq : ∀ x, ‖q x‖=1) (x : SpatialPoint) : ‖constantLeftGauge c q x‖=1 := by
  simp only [constantLeftGauge,norm_mul,hu,hq x,one_mul]

/-- Original `constantLeftGauge_hopf` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem constantLeftGauge_hopf (c : ℍ) (hu : ‖c‖=1) (hc : c.imJ=0 ∧ c.imK=0)
    (q : QuaternionField) (x : SpatialPoint) : hopf (constantLeftGauge c q x)=hopf (q x) := by
  have hn := (normSq_eq_one_iff c).mpr hu
  simp only [Quaternion.normSq_def',hc.1,hc.2,zero_pow (by decide : 2≠0),add_zero] at hn
  have haxis : hopf c=iAxis := by
    ext <;> simp [hopf,iAxis,hc.1,hc.2] <;> nlinarith
  change hopf (c*q x)=hopf (q x)
  unfold hopf at haxis ⊢
  rw [star_mul]
  calc
    _ = star (q x)*(star c*iAxis*c)*q x := by simp only [mul_assoc]
    _ = _ := by rw [haxis]

/-- Original `constantLeftGauge_connection` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem constantLeftGauge_connection (c : ℍ) (hu : ‖c‖=1) (hc : c.imJ=0 ∧ c.imK=0)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (x : SpatialPoint) (j : Fin 3) :
    connection (constantLeftGauge c q) x j=connection q x j := by
  have hd := ((hq.differentiable (by simp) x).hasFDerivAt).const_mul c
  have hder : spatialPartial (constantLeftGauge c q) x j=c*spatialPartial q x j := by
    change fderiv ℝ (fun y => c*q y) x (EuclideanSpace.single j 1)=_
    rw [hd.fderiv]
    rfl
  have h := connectionValue_iPlane_mul c 0 (q x) (spatialPartial q x j) hc.1 hc.2
  rw [(normSq_eq_one_iff c).mpr hu] at h
  change connectionValue (c*q x) (spatialPartial (constantLeftGauge c q) x j)=_
  rw [hder]
  simpa [connection,connectionValue_eq] using h

/-- Original `constantLeftGauge_solenoidal` guarantee for the `SeedChartTransfer` construction; the complete source hypotheses are retained. -/
theorem constantLeftGauge_solenoidal (c : ℍ) (hu : ‖c‖=1) (hc : c.imJ=0 ∧ c.imK=0)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hs : IsSolenoidal q) :
    IsSolenoidal (constantLeftGauge c q) := by
  have heq : velocity 1 (constantLeftGauge c q)=velocity 1 q := by
    funext x
    ext j
    exact congrArg (fun a : ℝ => (1 : ℝ)*a) (constantLeftGauge_connection c hu hc q hq x j)
  intro x
  rw [heq]
  exact hs x

/-- Analytic chart transfer keeps the physical connection and integer cell.
It never chooses a discontinuous global real argument. -/
theorem seedChartTransfer_spec (a b : SeedChart) (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (ha : match a with | .north => -(1/2 : ℝ)<s.imI | .south => s.imI<(1/2 : ℝ))
    (hb : match b with | .north => -(1/2 : ℝ)<s.imI | .south => s.imI<(1/2 : ℝ))
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hu : ∀ x, ‖q x‖=1)
    (hp : IsPeriodicField q) (hs : IsSolenoidal q) (h0 : q 0=exactChartSeed a s) :
    let r := constantLeftGauge (seedChartTransition a b s) q
    ContDiff ℝ ∞ r ∧ (∀ x, ‖r x‖=1 ∧ hopf (r x)=hopf (q x)) ∧
      IsPeriodicField r ∧ IsSolenoidal r ∧
      (∀ x j, connection r x j=connection q x j) ∧
      r 0=exactChartSeed b s ∧ HasSeedChartPhase b (r 0) := by
  have hC := seedChartTransition_spec a b s hr hn ha hb
  have hzero : constantLeftGauge (seedChartTransition a b s) q 0=exactChartSeed b s := by
    change seedChartTransition a b s*q 0=_
    rw [h0]
    exact hC.2.2
  refine ⟨constantLeftGauge_contDiff _ q hq,?_,constantLeftGauge_periodic _ q hp,
    constantLeftGauge_solenoidal _ hC.1 hC.2.1 q hq hs,
    constantLeftGauge_connection _ hC.1 hC.2.1 q hq,hzero,?_⟩
  · intro x
    exact ⟨constantLeftGauge_norm _ hC.1 q hu x,constantLeftGauge_hopf _ hC.1 hC.2.1 q x⟩
  · rw [hzero]
    exact exactChartSeed_phase b s hr hn hb

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
