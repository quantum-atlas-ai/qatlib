/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceRescaling

/-!
# All-direction finite packets from the original rational jet program

All four requests use the same lower-period physical point. Value and
three directional samples are rounded to a common dyadic denominator.
Neither sphere membership nor tangency is required of returned packets.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Original Jet Query in the Hopf Atlas construction. -/
abbrev OriginalJetQuery := ((Fin 3 → ℚ) × (Fin 3 → ℕ)) × ℕ
/-- Abbreviation for Rational Jet Source in the Hopf Atlas construction. -/
abbrev RationalJetSource := OriginalJetQuery → (Fin 3 → ℚ)

/-- The actual order-one multi-index in a chosen physical direction. -/
def firstJetIndex (i : Fin 3) : Fin 3 → ℕ := fun j => if j=i then 1 else 0

/-- The value/directional pair projects the same original multi-index source. -/
def originalFirstJetPair (source : RationalJetSource) (i : Fin 3)
    (label : (Fin 3 → ℚ) × ℕ) : RationalSpinSample :=
  (source ((label.1,0),label.2),source ((label.1,firstJetIndex i),label.2))

/-- Original accuracy is stated at legal physical rational points using actual
Fréchet derivatives; no normalized derivative or lift oracle is assumed. -/
def OriginalFirstJetAccurate (v : SpatialPoint → SpatialPoint) (source : RationalJetSource) : Prop :=
  ∀ (a : Fin 3 → ℚ) (b : ℕ), (∀ j, 0 ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ physicalPeriod) →
    (∀ j, |(source ((a,0),b) j : ℝ)-v (rationalSpatialPoint a) j| ≤ (2^b : ℝ)⁻¹) ∧
    (∀ i j, |(source ((a,firstJetIndex i),b) j : ℝ)-
      fderiv ℝ v (rationalSpatialPoint a) (EuclideanSpace.single i 1) j| ≤ (2^b : ℝ)⁻¹)

/-- Every directional pair inherits accuracy from the same original program. -/
theorem OriginalFirstJetAccurate.directional (v : SpatialPoint → SpatialPoint)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source) (i : Fin 3) :
    OriginalDirectionalSpinSourceAccurate v i (originalFirstJetPair source i) := by
  intro a b ha
  exact ⟨(hs a b ha).1,(hs a b ha).2 i⟩

/-- The old reference-value API is the value/Dx projection of the full source. -/
theorem OriginalFirstJetAccurate.legacy (v : SpatialPoint → SpatialPoint)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source) :
    OriginalSpinSourceAccurate v (originalFirstJetPair source 0) := by
  intro a b ha
  exact ⟨(hs a b ha).1,(hs a b ha).2 0⟩

/-- One unrounded value query at the finite rescaled physical address. -/
def normalizedFirstJetValue (source : RationalJetSource) (m1 m2 : ℚ)
    (label : (Fin 3 → ℚ) × ℕ) : Fin 3 → ℚ :=
  let q := rescaleSourceQuery m1 m2 label
  source ((q.1,0),q.2)

/-- One derivative query and multiplication by the same finite lower period. -/
def normalizedFirstJetPartial (source : RationalJetSource) (m1 m2 : ℚ) (i : Fin 3)
    (label : (Fin 3 → ℚ) × ℕ) : Fin 3 → ℚ :=
  let q := rescaleSourceQuery m1 m2 label
  let length := periodLower q.2
  let answer := source ((q.1,firstJetIndex i),q.2)
  fun j => length*answer j

/-- A value and all three first derivatives, each encoded by three integers. -/
abbrev RationalFirstJetPacket := (Fin 3 → ℤ) × (Fin 3 → Fin 3 → ℤ)

/-- The same two-bit rounding slack as the original source-mean implementation. -/
def roundedSourceFirstJet (source : RationalJetSource) (m1 m2 : ℚ)
    (a : Fin 3 → ℚ) (b : ℕ) : RationalFirstJetPacket :=
  let p := b+2
  let value := normalizedFirstJetValue source m1 m2 (a,p)
  let derivatives := fun i => normalizedFirstJetPartial source m1 m2 i (a,p)
  (fun j => nearestDyadicNumerator (value j) p,
   fun i j => nearestDyadicNumerator (derivatives i j) p)

/-- The explicit four-request schedule of the finite packet. -/
def sourceFirstJetSchedule (m1 m2 : ℚ) (a : Fin 3 → ℚ) (b : ℕ) : List OriginalJetQuery :=
  let q := rescaleSourceQuery m1 m2 (a,b+2)
  ((q.1,0),q.2) :: List.ofFn (fun i : Fin 3 => ((q.1,firstJetIndex i),q.2))

/-- A packet has exactly four original requests, not three paired callbacks. -/
theorem sourceFirstJetSchedule_length (m1 m2 : ℚ) (a : Fin 3 → ℚ) (b : ℕ) :
    (sourceFirstJetSchedule m1 m2 a b).length=4 := by simp [sourceFirstJetSchedule]

noncomputable section
open Set
open scoped Quaternion ContDiff

/-- Decode a packet coordinate vector without assuming it is unit or tangent. -/
def firstJetPacketVector (p : ℕ) (w : Fin 3 → ℤ) : SpatialPoint :=
  rationalSpatialPoint (fun j => (w j : ℚ)/(2^p : ℚ))

/-- Original `rounded_coordinate_error` guarantee for the `SourceJets` construction; the complete source hypotheses are retained. -/
private theorem rounded_coordinate_error (q : ℚ) (x : ℝ) (b : ℕ)
    (h : |(q : ℝ)-x| ≤ (2^(b+2) : ℝ)⁻¹) :
    |((nearestDyadicNumerator q (b+2) : ℤ) : ℝ)/(2^(b+2) : ℝ)-x| ≤ (2^b : ℝ)⁻¹ := by
  have hr : |((nearestDyadicNumerator q (b+2) : ℤ) : ℝ)/(2^(b+2) : ℝ)-(q : ℝ)| ≤
      (2^(b+2) : ℝ)⁻¹/2 := by
    have hq := (Rat.cast_le (K := ℝ)).mpr (nearestDyadicNumerator_error q (b+2))
    push_cast at hq
    exact hq
  have hp : (2^(b+2) : ℝ)⁻¹=(2^b : ℝ)⁻¹/4 := by
    rw [pow_add]
    norm_num
    ring
  calc
    _ ≤ |((nearestDyadicNumerator q (b+2) : ℤ) : ℝ)/(2^(b+2) : ℝ)-(q : ℝ)|+|(q : ℝ)-x| :=
      abs_sub_le _ _ _
    _ ≤ (2^(b+2) : ℝ)⁻¹/2+(2^(b+2) : ℝ)⁻¹ := add_le_add hr h
    _ ≤ _ := by
      rw [hp]
      have ht : (0 : ℝ) ≤ (2^b : ℝ)⁻¹ := by positivity
      linarith

/-- Original `packet_norm_error` guarantee for the `SourceJets` construction; the complete source hypotheses are retained. -/
private theorem packet_norm_error (p : ℕ) (w : Fin 3 → ℤ) (x : SpatialPoint)
    (e : ℝ) (he : 0 ≤ e)
    (h : ∀ j, |((w j : ℤ) : ℝ)/(2^p : ℝ)-x j| ≤ e) :
    ‖firstJetPacketVector p w-x‖ ≤ 2*e := by
  have hc (j : Fin 3) : |(firstJetPacketVector p w-x) j| ≤ e := by
    simpa [firstJetPacketVector,rationalSpatialPoint] using h j
  have hn := pure_coordinate_norm_le (spinOfVector (firstJetPacketVector p w-x)) rfl e he
    (hc 0) (hc 1) (hc 2)
  rw [spinOfVector_norm] at hn
  linarith

/-- All coordinates of the actual rounded packet approximate the same fixed
physical source values and scaled derivatives. Full second-partial bounds
are consumed for the y/z directions as well as Dx. -/
theorem roundedSourceFirstJet_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hbounds : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (a : Fin 3 → ℚ) (ha : ∀ j, (a j : ℝ) ∈ Icc 0 1) (b : ℕ) :
    ‖firstJetPacketVector (b+2) (roundedSourceFirstJet source m1 m2 a b).1-
        v (physicalPeriod • rationalSpatialPoint a)‖ ≤ 2*(2^b : ℝ)⁻¹ ∧
    ∀ i, ‖firstJetPacketVector (b+2) ((roundedSourceFirstJet source m1 m2 a b).2 i)-
        physicalPeriod • fderiv ℝ v (physicalPeriod • rationalSpatialPoint a) (EuclideanSpace.single i 1)‖ ≤
      2*(2^b : ℝ)⁻¹ := by
  have herr (i : Fin 3) := rescaledDirectionalSpinSamples_error v hv i (originalFirstJetPair source i)
    (OriginalFirstJetAccurate.directional v source hs i) m1 m2 hm1 hm2
    (SourceAllRescalingBounds.directional v _ _ hbounds i) a ha (b+2)
  constructor
  · apply packet_norm_error
    · positivity
    · intro j
      apply rounded_coordinate_error
      simpa [rescaledSpinSamples, originalFirstJetPair, normalizedFirstJetValue, rescaleSourceQuery] using (herr 0).1 j
  · intro i
    apply packet_norm_error
    · positivity
    · intro j
      apply rounded_coordinate_error
      simpa [rescaledSpinSamples, originalFirstJetPair, normalizedFirstJetPartial, rescaleSourceQuery,
        sourcePhysicalPartial] using (herr i).2 j

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
