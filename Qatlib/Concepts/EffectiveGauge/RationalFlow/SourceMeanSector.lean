/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanPhysical

set_option backward.isDefEq.respectTransparency false

/-!
# Source-only finite sector selection for the same periodic reference

The physical intervals and the three choices are produced before an output
epsilon is supplied. The true mean belongs to the source-built reference;
it is not supplied to the program. Integer-cell uniqueness here is one part
of the later gauge uniqueness theorem.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Data and hypotheses for Source Mean Sector Result in the Rational Flow construction. -/
structure SourceMeanSectorResult where
  intervals : Fin 3 → RationalMeanInterval
  choices : Fin 3 → MeanCellSelection

/-- A postcondition on the one returned finite result, including its actual
intervals as well as its choices. No certificate is supplied to the program. -/
def SourceMeanSectorCertificate (mean : Fin 3 → ℝ) (result : SourceMeanSectorResult) : Prop :=
  (∀ j, ((result.intervals j).lower : ℝ) ≤ mean j ∧ mean j ≤ ((result.intervals j).upper : ℝ) ∧
    ((result.intervals j).radius : ℝ) ≤ 1/64 ∧
    |mean j-((result.intervals j).midpoint : ℝ)| ≤ ((result.intervals j).radius : ℝ)) ∧
  (∀ j, (result.choices j).shift=0 ∨ (result.choices j).shift=-1/2) ∧
  (∀ j, (1/8 : ℚ)<(result.choices j).margin) ∧
  (∀ j, ((result.choices j).shift : ℝ)+1/8 < mean j+((result.choices j).winding : ℝ) ∧
    mean j+((result.choices j).winding : ℝ) < ((result.choices j).shift : ℝ)+7/8) ∧
  (∀ n : Fin 3 → ℤ,
    (∀ j, ((result.choices j).shift : ℝ)+1/8 < mean j+(n j : ℝ) ∧
      mean j+(n j : ℝ) < ((result.choices j).shift : ℝ)+7/8) →
    n=fun j => (result.choices j).winding)

/-- Definition of source Mean Sector Execution in the Rational Flow construction. -/
def sourceMeanSectorExecution (source : RationalJetSource) (m1 m2 : ℚ) :
    Option SourceMeanSectorResult :=
  (sourceMeanPhysicalExecution source m1 m2 (1/64)).map (fun intervals =>
    ⟨intervals,selectMeanSector (fun j => (intervals j).midpoint) (fun j => (intervals j).radius)⟩)

/-- Original `sourceMeanSectorExecution_zero` guarantee for the `SourceMeanSector` construction; the complete source hypotheses are retained. -/
theorem sourceMeanSectorExecution_zero (source : RationalJetSource) (m2 : ℚ) :
    sourceMeanSectorExecution source 0 m2=some
      ⟨fun _ => ⟨0,0⟩,fun _ => ⟨-1/2,0,1/2⟩⟩ := by
  have hcell : selectMeanCell 0 0=⟨-1/2,0,1/2⟩ := by decide +kernel
  rw [sourceMeanSectorExecution,sourceMeanPhysicalExecution_zero]
  simp only [Option.map_some,RationalMeanInterval.midpoint,
    RationalMeanInterval.radius,zero_add,sub_self,zero_div]
  change some (⟨fun _ => ⟨0,0⟩,fun _ => selectMeanCell 0 0⟩ : SourceMeanSectorResult)=_
  rw [hcell]

/-- Original `sourceMeanMomentAxis_ne` guarantee for the `SourceMeanSector` construction; the complete source hypotheses are retained. -/
theorem sourceMeanMomentAxis_ne (j : Fin 3) : sourceMeanMomentAxis j≠j := by
  fin_cases j <;> decide

noncomputable section
open Set
open scoped ContDiff

/-- The already constructed reference is exactly the reference whose
connection mean is enclosed by the finite original-source producer. -/
theorem sourceMeanPhysicalReference_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 tolerance eta : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1) (he : 0<eta)
    (hb : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ intervals, sourceMeanPhysicalExecution source m1 m2 tolerance=some intervals ∧ ∀ j,
      let mean := physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source hs) m1 m2 eta) x j)
      ((intervals j).lower : ℝ) ≤ mean ∧ mean ≤ ((intervals j).upper : ℝ) ∧
        ((intervals j).radius : ℝ) ≤ (tolerance : ℝ) ∧
        |mean-((intervals j).midpoint : ℝ)| ≤ ((intervals j).radius : ℝ) := by
  obtain ⟨intervals,hex,hcorrect⟩ := sourceMeanPhysicalExecution_correct v hv hu source hs
    m1 m2 tolerance hm1 hm2 ht ht1 hb
  refine ⟨intervals,hex,?_⟩
  intro j
  have hmean := sourcePeriodicReference_unit_mean v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source hs) m1 m2 eta he B hB mu hm hg hoff hmargin
    (sourceMeanMomentAxis j) j (sourceMeanMomentAxis_ne j)
  have hc := hcorrect j
  rw [hmean]
  exact ⟨hc.1,hc.2.1,hc.2.2.1,
    rationalMeanInterval_midpoint_error (intervals j) _ ⟨hc.1,hc.2.1⟩⟩

/-- Same successful finite source execution, same source-built reference,
strict positive cell margins and unique applied integer windings. -/
theorem sourceMeanSectorExecution_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 eta : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (he : 0<eta)
    (hb : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    let mean := fun j => physicalCubeMean (fun x => connection
      (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source hs) m1 m2 eta) x j)
    ∃ result, sourceMeanSectorExecution source m1 m2=some result ∧ SourceMeanSectorCertificate mean result := by
  dsimp only
  obtain ⟨intervals,hex,hcorrect⟩ := sourceMeanPhysicalReference_correct v hv hu hp source hs
    m1 m2 (1/64) eta hm1 hm2 (by norm_num) (by norm_num) he hb B hB mu hm hg hoff hmargin
  let mid := fun j => (intervals j).midpoint
  let rad := fun j => (intervals j).radius
  have hrad (j : Fin 3) : rad j ≤ 1/32 := by
    change (intervals j).radius ≤ (1/32 : ℚ)
    have h := (hcorrect j).2.2.1
    have hh : ((intervals j).radius : ℝ) ≤ (1/32 : ℝ) := by norm_num at h ⊢; linarith
    exact (Rat.cast_le (K := ℝ)).mp
      (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh)
  have hselect := selectMeanSector_correct mid rad hrad _ (fun j => (hcorrect j).2.2.2)
  refine ⟨⟨intervals,selectMeanSector mid rad⟩,?_,?_,?_,?_,hselect.1,hselect.2⟩
  · rw [sourceMeanSectorExecution,hex]
    rfl
  · intro j
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hcorrect j
  · intro j
    exact (selectMeanCell_margin (mid j) (rad j) (hrad j)).1
  · intro j
    exact (selectMeanCell_margin (mid j) (rad j) (hrad j)).2

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
