/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.StoredReferenceFrame
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeededConnectionGrid
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.AutomaticCoefficientPreparation

set_option backward.isDefEq.respectTransparency false

/-!
# Stored Poisson Preparation

Hopf Atlas constructions for Effective Gauge.
Defines `storedFourierCoefficientListExecution`, `storedPoissonCoefficientPreparation`, `storedAutomaticPoissonCoefficientsFromGap`.
Proves `storedFourierCoefficientListExecution_store`, `storedPoissonCoefficientPreparation_store`, `storedAutomaticPoissonCoefficientsFromGap_output`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of stored Fourier Coefficient List Execution in the Hopf Atlas construction. -/
def storedFourierCoefficientListExecution (source : RationalJetSource) (frame : StoredReferenceFrame)
    (M : ℕ) (s length d : ℚ) (frequencies : List SpatialFrequency) :
    Option (RationalConnectionGridData × RationalFourierCoefficientList) :=
  (connectionGridWithSeeds source frame M s).map (fun data =>
    (data,frequencies.map (fun k => (k,rationalFourierCoefficientsOfData M length k d data))))

/-- Definition of stored Poisson Coefficient Preparation in the Hopf Atlas construction. -/
def storedPoissonCoefficientPreparation (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : Option PoissonCoefficientPreparation :=
  let cache := frame.regularity
  let N := finitePoissonCutoff cache.connectionBounds[6] tolerance
  let M := finitePoissonMesh cache.connectionBounds[0] cache.connectionBounds[1] N tolerance
  let s := finitePoissonSampleAccuracy N tolerance
  let d := finitePoissonModeAccuracy cache.connectionBounds[0] N tolerance
  let ell := finitePoissonPeriodAccuracy cache.connectionBounds[0] N tolerance
  let length := fourierPeriodExecution ell
  (storedFourierCoefficientListExecution source frame M s length d (sourceFrequencyGrid N)).map
    (fun result => ⟨frame.prepared,cache,N,M,s,d,ell,length,result.1,result.2⟩)

/-- Definition of stored Automatic Poisson Coefficients From Gap in the Hopf Atlas construction. -/
def storedAutomaticPoissonCoefficientsFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option (StoredReferenceFrame × PoissonCoefficientPreparation) := do
  let prepared ← cachedMeanPreparationRun source bounds
  let frame := storeReferenceFrame source prepared (referenceUnitCollar gap)
  let result ← storedPoissonCoefficientPreparation source frame tolerance
  return (frame,result)

/-- Original `storedFourierCoefficientListExecution_store` guarantee for the `StoredPoissonPreparation` construction; the complete source hypotheses are retained. -/
theorem storedFourierCoefficientListExecution_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (M : ℕ) (s length d : ℚ) (frequencies : List SpatialFrequency) :
    storedFourierCoefficientListExecution source (storeReferenceFrame source prepared eta) M s length d frequencies=
      sourceFourierCoefficientListExecution source prepared eta M s length d frequencies := by
  unfold storedFourierCoefficientListExecution
  rw [connectionGridWithSeeds_correct,storedConnectionGrid_store]
  rfl

/-- Original `storedPoissonCoefficientPreparation_store` guarantee for the `StoredPoissonPreparation` construction; the complete source hypotheses are retained. -/
theorem storedPoissonCoefficientPreparation_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta tolerance : ℚ) :
    storedPoissonCoefficientPreparation source (storeReferenceFrame source prepared eta) tolerance=
      materializePoissonCoefficientPreparation source prepared eta tolerance := by
  unfold storedPoissonCoefficientPreparation
  dsimp only
  rw [storedFourierCoefficientListExecution_store]
  rfl

/-- Equality of returned coefficient data, not permission to re-execute the
uncached RHS when using the saved frame for subsequent requests. -/
theorem storedAutomaticPoissonCoefficientsFromGap_output (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) :
    (storedAutomaticPoissonCoefficientsFromGap source bounds gap tolerance).map Prod.snd=
      automaticPoissonCoefficientsFromGap source bounds gap tolerance := by
  simp [storedAutomaticPoissonCoefficientsFromGap,automaticPoissonCoefficientsFromGap,
    Option.map_bind,storedPoissonCoefficientPreparation_store]

/-- Original `storedPoissonCoefficientPreparation_fields` guarantee for the `StoredPoissonPreparation` construction; the complete source hypotheses are retained. -/
theorem storedPoissonCoefficientPreparation_fields (source : RationalJetSource)
    (frame : StoredReferenceFrame) (tolerance : ℚ) (result : PoissonCoefficientPreparation)
    (h : storedPoissonCoefficientPreparation source frame tolerance=some result) :
    result.prepared=frame.prepared ∧ result.referenceCache=frame.regularity := by
  unfold storedPoissonCoefficientPreparation at h
  rcases Option.map_eq_some_iff.mp h with ⟨out,_,rfl⟩
  exact ⟨rfl,rfl⟩

/-- Original `storedAutomaticPoissonCoefficientsFromGap_frame` guarantee for the `StoredPoissonPreparation` construction; the complete source hypotheses are retained. -/
theorem storedAutomaticPoissonCoefficientsFromGap_frame (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) (frame : StoredReferenceFrame) (result : PoissonCoefficientPreparation)
    (h : storedAutomaticPoissonCoefficientsFromGap source bounds gap tolerance=some (frame,result)) :
    ∃ prepared, cachedMeanPreparationRun source bounds=some prepared ∧
      frame=storeReferenceFrame source prepared (referenceUnitCollar gap) ∧
      result.prepared=frame.prepared ∧ result.referenceCache=frame.regularity := by
  unfold storedAutomaticPoissonCoefficientsFromGap at h
  rcases Option.bind_eq_some_iff.mp h with ⟨prepared,hprepared,h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨found,hfound,hpair⟩
  have hp := Option.some.inj hpair
  have hframe := congrArg Prod.fst hp
  have hresult := congrArg Prod.snd hp
  dsimp only at hframe hresult
  subst frame
  subst result
  exact ⟨prepared,hprepared,rfl,storedPoissonCoefficientPreparation_fields source _ tolerance found hfound⟩

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
