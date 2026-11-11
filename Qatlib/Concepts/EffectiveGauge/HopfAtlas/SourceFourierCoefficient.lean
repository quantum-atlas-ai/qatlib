/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierSummability
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedReferencePreparation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Fourier Coefficient

Hopf Atlas constructions for Effective Gauge.
Defines `normalizedConnectionReal`, `normalizedConnectionComplex`, `normalizedConnectionFourierCoefficient`.
Proves `contDiff_normalizedConnectionReal`, `contDiff_normalizedConnectionComplex`, `unitPeriodic_normalizedConnectionComplex`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of normalized Connection Real in the Hopf Atlas construction. -/
def normalizedConnectionReal (q : QuaternionField) (j : Fin 3) (x : SpatialPoint) : ℝ :=
  physicalPeriod*connection q (physicalPeriod • x) j

/-- Definition of normalized Connection Complex in the Hopf Atlas construction. -/
def normalizedConnectionComplex (q : QuaternionField) (j : Fin 3) (x : SpatialPoint) : ℂ :=
  Complex.ofRealCLM (normalizedConnectionReal q j x)

/-- Original `contDiff_normalizedConnectionReal` guarantee for the `SourceFourierCoefficient` construction; the complete source hypotheses are retained. -/
theorem contDiff_normalizedConnectionReal (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (j : Fin 3) :
    ContDiff ℝ ∞ (normalizedConnectionReal q j) :=
  contDiff_const.mul ((contDiff_connection q hq j).comp (contDiff_id.const_smul physicalPeriod))

/-- Original `contDiff_normalizedConnectionComplex` guarantee for the `SourceFourierCoefficient` construction; the complete source hypotheses are retained. -/
theorem contDiff_normalizedConnectionComplex (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (j : Fin 3) :
    ContDiff ℝ ∞ (normalizedConnectionComplex q j) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_normalizedConnectionReal q hq j)

/-- Original `unitPeriodic_normalizedConnectionComplex` guarantee for the `SourceFourierCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitPeriodic_normalizedConnectionComplex (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (j : Fin 3) : IsUnitPeriodicField (normalizedConnectionComplex q j) := by
  have h := periodicField_rescale_unit (fun x => connection q x j) (periodicField_connection q hq hp j)
  intro x n
  change Complex.ofRealCLM (physicalPeriod*connection q (physicalPeriod • (x+unitIntegerShift n)) j)=
    Complex.ofRealCLM (physicalPeriod*connection q (physicalPeriod • x) j)
  have heq : connection q (physicalPeriod • (x+unitIntegerShift n)) j=
      connection q (physicalPeriod • x) j := h x n
  rw [heq]

/-- Coefficients are defined for the true normalized connection, retaining
its L factor, with continuity/periodicity proved from the given field. -/
def normalizedConnectionFourierCoefficient (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (j : Fin 3) (k : SpatialFrequency) : ℂ :=
  unitFourierCoefficient (normalizedConnectionComplex q j)
    (contDiff_normalizedConnectionComplex q hq j).continuous
    (unitPeriodic_normalizedConnectionComplex q hq hp j) k

/-- The coefficient decay is now a consumer of the original source program
and its same successful reference-cache run, not an input Fourier modulus. -/
theorem materializeReferencePreparation_fourier_decay (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    let q := preparedPeriodicReference v hv hu source hs prepared eta
    let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
    ∀ (j : Fin 3) (k : SpatialFrequency) (i : Fin 3), k i≠0 →
      ‖normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k‖ ≤
        ((materializeReferencePreparation eta prepared).connectionBounds[6] : ℝ)/
          (physicalPeriod^6*|(k i : ℝ)|^6) := by
  dsimp only
  intro j k i hi
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  have hq : ContDiff ℝ ∞ q := spec.2.1.1
  change ‖unitFourierCoefficient (normalizedConnectionComplex q j)
    (contDiff_normalizedConnectionComplex q hq j).continuous
    (unitPeriodic_normalizedConnectionComplex q hq spec.1 j) k‖ ≤ _
  apply unitFourierCoefficient_decay _ (contDiff_normalizedConnectionComplex q hq j)
    (unitPeriodic_normalizedConnectionComplex q hq spec.1 j) k i hi 6
  intro x _
  change ‖spatialWordPartial (fun y => Complex.ofRealCLM (normalizedConnectionReal q j y))
    (List.replicate 6 i) x‖ ≤ _
  rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
    (contDiff_normalizedConnectionReal q hq j)]
  change ‖((spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real]
  exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb prepared hrun
    eta he he1 B hB mu hm hg hoff hmargin 6 (List.replicate 6 i) (by simp) j x

/-- Same-execution c6 also certifies absolute convergence and reconstruction
of the actual original-source connection at every spatial point. -/
theorem materializeReferencePreparation_fourier_reconstruction (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    let q := preparedPeriodicReference v hv hu source hs prepared eta
    let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
    ∀ j : Fin 3, Summable (normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j) ∧
      ∀ x, HasSum (fun k : SpatialFrequency => unitFourierMode k x*
        normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k) (normalizedConnectionComplex q j x) := by
  dsimp only
  intro j
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  have hq : ContDiff ℝ ∞ q := spec.2.1.1
  have hC6 : ∀ i x, InUnitCube x → ‖spatialWordPartial (normalizedConnectionComplex q j)
      (List.replicate 6 i) x‖ ≤ ((materializeReferencePreparation eta prepared).connectionBounds[6] : ℝ) := by
    intro i x _
    change ‖spatialWordPartial (fun y => Complex.ofRealCLM (normalizedConnectionReal q j y))
      (List.replicate 6 i) x‖ ≤ _
    rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
      (contDiff_normalizedConnectionReal q hq j)]
    change ‖((spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin 6 (List.replicate 6 i) (by simp) j x
  constructor
  · exact unitFourierCoefficient_summable _ (contDiff_normalizedConnectionComplex q hq j)
      (unitPeriodic_normalizedConnectionComplex q hq spec.1 j) _ hC6
  · exact unitFourier_hasSum _ (contDiff_normalizedConnectionComplex q hq j)
      (unitPeriodic_normalizedConnectionComplex q hq spec.1 j) _ hC6

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
