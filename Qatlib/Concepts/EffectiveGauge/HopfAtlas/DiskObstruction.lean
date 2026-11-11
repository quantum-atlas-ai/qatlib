/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseLoopObstruction
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Disk Obstruction

Hopf Atlas constructions for Effective Gauge.
Defines `ComplexUnitDisk`, `unitDiskBoundary`.
Proves `continuous_unitDiskBoundary`, `unitDiskBoundary_period`, `circleExp_eq_implies_phase_eq`.
-/


set_option autoImplicit false
noncomputable section
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of Complex Unit Disk in the Hopf Atlas construction. -/
def ComplexUnitDisk := Metric.closedBall (0 : ℂ) 1

/-- Definition of unit Disk Boundary in the Hopf Atlas construction. -/
def unitDiskBoundary (t : ℝ) : ComplexUnitDisk :=
  ⟨(Circle.exp t : ℂ),by simp [ComplexUnitDisk,Metric.mem_closedBall]⟩

/-- Original `continuous_unitDiskBoundary` guarantee for the `DiskObstruction` construction; the complete source hypotheses are retained. -/
theorem continuous_unitDiskBoundary : Continuous unitDiskBoundary :=
  (continuous_subtype_val.comp Circle.isCoveringMap_exp.continuous).subtype_mk _

/-- Original `unitDiskBoundary_period` guarantee for the `DiskObstruction` construction; the complete source hypotheses are retained. -/
theorem unitDiskBoundary_period : unitDiskBoundary physicalPeriod=unitDiskBoundary 0 := by
  apply Subtype.ext
  simp [unitDiskBoundary,physicalPeriod]

/-- Original `circleExp_eq_implies_phase_eq` guarantee for the `DiskObstruction` construction; the complete source hypotheses are retained. -/
theorem circleExp_eq_implies_phase_eq (a b : ℝ) (h : Circle.exp a=Circle.exp b) :
    phase a=phase b := by
  obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp h
  rw [hn]
  exact phase_int_period b n

/-- The identity boundary circle has no continuous circle-valued extension
to its filled disk. No differentiability assumption is used. -/
theorem no_circle_disk_extension (R : ComplexUnitDisk → Circle) (hR : Continuous R)
    (hboundary : ∀ t : ℝ, R (unitDiskBoundary t)=Circle.exp t) : False := by
  have hc : Convex ℝ (Metric.closedBall (0 : ℂ) 1) := convex_closedBall _ _
  have hn : (Metric.closedBall (0 : ℂ) 1).Nonempty := ⟨0,by simp⟩
  letI : ContractibleSpace ComplexUnitDisk := hc.contractibleSpace hn
  letI : LocallyPathConnectedSpace ComplexUnitDisk := hc.locallyPathConnectedSpace
  let r : C(ComplexUnitDisk,Circle) := ⟨R,hR⟩
  have hzero : Circle.exp 0=r (unitDiskBoundary 0) := (hboundary 0).symm
  obtain ⟨F,hF,_hunique⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    r (unitDiskBoundary 0) 0 hzero
  have harg (t : ℝ) : Circle.exp (F (unitDiskBoundary t))=Circle.exp t := by
    have h := congrFun hF.2 (unitDiskBoundary t)
    exact h.trans (hboundary t)
  exact no_closed_phase_lift (fun t => F (unitDiskBoundary t))
    (F.continuous.comp continuous_unitDiskBoundary)
    (fun t => circleExp_eq_implies_phase_eq _ _ (harg t))
    (congrArg F unitDiskBoundary_period)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
