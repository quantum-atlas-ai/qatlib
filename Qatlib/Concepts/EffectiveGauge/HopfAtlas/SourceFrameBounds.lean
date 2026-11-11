/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanBounds
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ZeroSource
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceWord

set_option backward.isDefEq.respectTransparency false

/-!
# One finite bound-program execution supplies the frame's orders zero to nine

Order zero is one by the unit-source promise. The first original bound is
read once. A zero result derives all remaining bounds as zero; otherwise
the eight remaining original answers are read and compressed once each.
The returned request list is the list used in that execution, not a fee.
The supplied programs' bit runtime is a subsequent obligation.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Source Frame Bound Packet in the Hopf Atlas construction. -/
abbrev SourceFrameBoundPacket := Fin 10 → ℚ

/-- Definition of source Frame Higher Bound Labels in the Hopf Atlas construction. -/
def sourceFrameHigherBoundLabels : List ℕ := [2,3,4,5,6,7,8,9]

/-- Definition of source Frame Bound Decode in the Hopf Atlas construction. -/
def sourceFrameBoundDecode (m1 : ℚ) : List ℚ → Option SourceFrameBoundPacket
  | [m2,m3,m4,m5,m6,m7,m8,m9] => some ![1,m1,
      sourceMeanCompressedBound m2,sourceMeanCompressedBound m3,sourceMeanCompressedBound m4,
      sourceMeanCompressedBound m5,sourceMeanCompressedBound m6,sourceMeanCompressedBound m7,
      sourceMeanCompressedBound m8,sourceMeanCompressedBound m9]
  | _ => none

/-- Definition of source Frame Bound Labels in the Hopf Atlas construction. -/
def sourceFrameBoundLabels (m1 : ℚ) : List ℕ :=
  if m1=0 then [1] else 1::sourceFrameHigherBoundLabels

/-- Definition of source Frame Bound Run in the Hopf Atlas construction. -/
def sourceFrameBoundRun (bounds : ℕ → ℚ) : Option (SourceFrameBoundPacket × List ℕ) :=
  let m1 := sourceMeanCompressedBound (bounds 1)
  if m1=0 then some ((fun r => if r=0 then 1 else 0),[1]) else
    let labels := sourceFrameHigherBoundLabels
    let answers := labels.map bounds
    (sourceFrameBoundDecode m1 answers).map (fun packet => (packet,1::labels))

/-- A semantic description of the returned cache, including its derived
zero branch. It is not an additional bound oracle. -/
def sourceFrameBoundExpected (bounds : ℕ → ℚ) (r : Fin 10) : ℚ :=
  if r=0 then 1 else if r=1 then sourceMeanCompressedBound (bounds 1) else
    if sourceMeanCompressedBound (bounds 1)=0 then 0 else sourceMeanCompressedBound (bounds r.val)

/-- Definition of source Frame Unit Bound in the Hopf Atlas construction. -/
def sourceFrameUnitBound (packet : SourceFrameBoundPacket) (r : Fin 10) : ℚ :=
  (7 : ℚ)^r.val*packet r

/-- Original `sourceFrameBoundRun_eq` guarantee for the `SourceFrameBounds` construction; the complete source hypotheses are retained. -/
theorem sourceFrameBoundRun_eq (bounds : ℕ → ℚ) :
    sourceFrameBoundRun bounds=some
      (sourceFrameBoundExpected bounds,sourceFrameBoundLabels (sourceMeanCompressedBound (bounds 1))) := by
  by_cases h : sourceMeanCompressedBound (bounds 1)=0
  · simp only [sourceFrameBoundRun,if_pos h,sourceFrameBoundLabels]
    apply congrArg some
    apply Prod.ext
    · funext r
      fin_cases r <;> simp [sourceFrameBoundExpected,h]
    · rfl
  · simp only [sourceFrameBoundRun,if_neg h,sourceFrameHigherBoundLabels,
      List.map_cons,List.map_nil,sourceFrameBoundDecode,Option.map_some,sourceFrameBoundLabels]
    apply congrArg some
    apply Prod.ext
    · funext r
      fin_cases r <;> simp [sourceFrameBoundExpected,h]
    · rfl

/-- Original `sourceFrameBoundLabels_length` guarantee for the `SourceFrameBounds` construction; the complete source hypotheses are retained. -/
theorem sourceFrameBoundLabels_length (m1 : ℚ) :
    (sourceFrameBoundLabels m1).length=if m1=0 then 1 else 9 := by
  by_cases h : m1=0 <;> simp [sourceFrameBoundLabels,h,sourceFrameHigherBoundLabels]

/-- Original `sourceFrameBoundLabels_domain` guarantee for the `SourceFrameBounds` construction; the complete source hypotheses are retained. -/
theorem sourceFrameBoundLabels_domain (m1 : ℚ) :
    ∀ r ∈ sourceFrameBoundLabels m1, 1 ≤ r ∧ r ≤ 9 := by
  by_cases h : m1=0 <;> simp [sourceFrameBoundLabels,h,sourceFrameHigherBoundLabels]

/-- Original `sourceFrameBoundExpected_first` guarantee for the `SourceFrameBounds` construction; the complete source hypotheses are retained. -/
theorem sourceFrameBoundExpected_first (bounds : ℕ → ℚ) :
    sourceFrameBoundExpected bounds 1=sourceMeanCompressedBound (bounds 1) := by
  simp [sourceFrameBoundExpected]

/-- Original `sourceFrameBoundExpected_second` guarantee for the `SourceFrameBounds` construction; the complete source hypotheses are retained. -/
theorem sourceFrameBoundExpected_second (bounds : ℕ → ℚ) :
    sourceFrameBoundExpected bounds 2=
      sourceMeanEffectiveSecondBound (sourceMeanCompressedBound (bounds 1)) bounds := by
  simp [sourceFrameBoundExpected,sourceMeanEffectiveSecondBound]

noncomputable section
open scoped ContDiff

/-- The complete actual cache bounds every original ordered derivative
through order nine. The zero branch uses smoothness and periodicity, not
an unqueried higher-bound answer. -/
theorem sourceFrameBoundExpected_word (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (r : Fin 10) (w : List (Fin 3)) (hwlen : w.length=r.val)
    (x : SpatialPoint) (hx : InFundamentalCube x) :
    ‖spatialWordPartial v w x‖ ≤ (sourceFrameBoundExpected bounds r : ℝ) := by
  by_cases hr0 : r=0
  · subst r
    have hw : w=[] := List.length_eq_zero_iff.mp hwlen
    subst w
    simp [spatialWordPartial,sourceFrameBoundExpected,hu]
  · have hw : w≠[] := by
      intro he
      have hr : r.val=0 := by rw [he,List.length_nil] at hwlen; omega
      exact hr0 (Fin.ext hr)
    have hphys := hb.word v hv bounds w hw x hx
    rw [hwlen] at hphys
    have hcomp (n : ℕ) : (bounds n : ℝ) ≤ sourceMeanCompressedBound (bounds n) :=
      (Rat.cast_le (K := ℝ)).mpr (sourceMeanCompressedBound_encloses (bounds n)).1
    by_cases hr1 : r=1
    · subst r
      change ‖spatialWordPartial v w x‖ ≤ (sourceMeanCompressedBound (bounds 1) : ℝ)
      exact hphys.trans (hcomp 1)
    · by_cases hz : sourceMeanCompressedBound (bounds 1)=0
      · have hfirst : ∀ y, InFundamentalCube y → ∀ i,
            ‖fderiv ℝ v y (EuclideanSpace.single i 1)‖ ≤ 0 := by
          intro y hy i
          have hi := hb.word v hv bounds [i] (by simp) y hy
          have hc := hcomp 1
          rw [hz,Rat.cast_zero] at hc
          exact hi.trans hc
        rw [periodicSource_zero_first_word v hv hp hfirst w hw]
        simp [sourceFrameBoundExpected,hr0,hr1,hz]
      · simpa only [sourceFrameBoundExpected,if_neg hr0,if_neg hr1,if_neg hz] using
          hphys.trans (hcomp r.val)

/-- All unit-coordinate majorants used by the subsequent regularity
recurrences follow from the same physical packet, retaining all L powers. -/
theorem sourceFrameBoundExpected_unit_word (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (r : Fin 10) (w : List (Fin 3)) (hwlen : w.length=r.val)
    (u : SpatialPoint) (hucube : InUnitCube u) :
    ‖spatialWordPartial (unitCoordinateSpin v) w u‖ ≤
      (sourceFrameUnitBound (sourceFrameBoundExpected bounds) r : ℝ) := by
  have hphys := sourceFrameBoundExpected_word v hv hu hp bounds hb r w hwlen
    (physicalPeriod • u) (unitCube_scale_physical u hucube)
  have h := unitCoordinateSpin_word_bound v hv w u _ ((norm_nonneg _).trans hphys) hphys
  simpa only [sourceFrameUnitBound,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,hwlen] using h

/-- One successful finite execution supplies both the physical and normalized
cache certificates, and its actual finite bound request trace. -/
theorem sourceFrameBoundRun_correct (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) :
    ∃ packet labels, sourceFrameBoundRun bounds=some (packet,labels) ∧
      labels.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ labels, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (r : Fin 10) (w : List (Fin 3)), w.length=r.val → ∀ x, InFundamentalCube x →
        ‖spatialWordPartial v w x‖ ≤ (packet r : ℝ)) ∧
      (∀ (r : Fin 10) (w : List (Fin 3)), w.length=r.val → ∀ u, InUnitCube u →
        ‖spatialWordPartial (unitCoordinateSpin v) w u‖ ≤ (sourceFrameUnitBound packet r : ℝ)) := by
  refine ⟨_,_,sourceFrameBoundRun_eq bounds,sourceFrameBoundLabels_length _,sourceFrameBoundLabels_domain _,?_,?_⟩
  · exact sourceFrameBoundExpected_word v hv hu hp bounds hb
  · exact sourceFrameBoundExpected_unit_word v hv hu hp bounds hb

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
