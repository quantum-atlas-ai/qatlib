/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.InterferenceStability
public import Qatlib.Concepts.QRAM.SignedReadout.TranscriptStability

@[expose] public section

/-!
# Calibrated tomography records from a coherent preparation

For [KerenidisLandmanPrakash2020], Appendix G, condition the target on
success, reverse its work registers, and measure the physical address.
The second batch uses the same decoded target in the signed interference
with the QRAM reference constructed from the first batch. This gives a
finite law for the retained shots. The total variation bound counts the
decoded-state error in both batches and the calibration error in the
interference batch.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds (FinDist independentSampleLaw tvDist)
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open Qatlib.Foundations.InstrumentCore.Measurement (PostMeasure normalized_postMeasure)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket MeasureProb Normalized QState normalized_applyGate)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open scoped BigOperators Classical

/-- Coherent preparation, decoder, success event, and the physical labels used
by the basis and interference measurements. -/
structure TomographyPreparation (depth : ℕ) (I : Type) [Fintype I] [DecidableEq I] where
  target : Matrix I I ℂ
  decoder : Matrix I I ℂ
  success : Finset I
  seed : I
  place : Address depth ↪ I
  fallback : Address depth
  target_unitary : target ∈ Matrix.unitaryGroup I ℂ
  decoder_unitary : decoder ∈ Matrix.unitaryGroup I ℂ
  success_pos : 0 < MeasureProb (ApplyGate target (Ket seed)) success

namespace TomographyPreparation

variable {depth : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- The physical success probability of the target preparation. -/
def successProbability (P : TomographyPreparation depth I) : ℝ :=
  MeasureProb (ApplyGate P.target (Ket P.seed)) P.success

/-- The target success state after decoding the workspace. -/
def decodedState (P : TomographyPreparation depth I) : QState I :=
  ApplyGate P.decoder (PostMeasure (ApplyGate P.target (Ket P.seed)) P.success)

/-- Positive success and a unitary decoder give a normalized state. -/
theorem decoded_state_normalized (P : TomographyPreparation depth I) : Normalized P.decodedState :=
  normalized_applyGate P.decoder_unitary (normalized_postMeasure P.success_pos)

/-- Read a physical address from one conditioned basis measurement. -/
def basisShot (P : TomographyPreparation depth I) : FinDist (Address depth) :=
  bornReadoutLaw P.decodedState P.decoded_state_normalized (readPlacedAddress P.place P.fallback)

/-- Condition the calibrated interference on the common success flag
after loading the QRAM reference from the first record. -/
def interferenceState (P : TomographyPreparation depth I) (q : ℝ) (samples : List (Address depth)) :
    QState (Bool × (Bool × I)) :=
  heraldedInterferenceReadout P.target P.decoder (embeddedReferencePreparation P.place P.seed samples)
    P.success q P.seed

/-- The positive target mass and a nonnegative calibration keep the
common success event positive, so the conditioned interference is normalized. -/
theorem interference_state_normalized (P : TomographyPreparation depth I)
    (q : ℝ) (hq : 0 ≤ q) (samples : List (Address depth)) : Normalized (P.interferenceState q samples) := by
  unfold interferenceState heraldedInterferenceReadout
  apply normalized_postMeasure
  rw [heralded_interference_success _ _ _ _ _ _ P.decoder_unitary
    (embedded_reference_preparation_unitary P.place P.seed samples) hq]
  exact half_pos (add_pos_of_pos_of_nonneg P.success_pos hq)

/-- When the calibration is a probability, the full flagged interference
uses a unitary preparation. -/
theorem interference_unitary (P : TomographyPreparation depth I)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (samples : List (Address depth)) :
    heraldedInterferencePreparation P.target P.decoder
      (embeddedReferencePreparation P.place P.seed samples) P.success q ∈ Matrix.unitaryGroup _ ℂ :=
  heralded_interference_preparation_unitary _ _ _ _ _ P.target_unitary P.decoder_unitary
    (embedded_reference_preparation_unitary P.place P.seed samples) hq.1 hq.2

/-- The conditioned sign-and-address law for a given first record. -/
def interferenceShot (P : TomographyPreparation depth I) (q : ℝ) (hq : 0 ≤ q)
    (samples : List (Address depth)) : FinDist (Bool × Address depth) :=
  bornReadoutLaw (P.interferenceState q samples) (P.interference_state_normalized q hq samples)
    (placedInterferenceLabel P.place P.fallback)

/-- The law of fresh retained basis shots and fresh retained interference
shots, with the second batch using the QRAM reference from the first. -/
def transcript (P : TomographyPreparation depth I) (q : ℝ) (hq : 0 ≤ q)
    (basisShots interferenceShots : ℕ) :
    FinDist ((Fin basisShots → Address depth) × (Fin interferenceShots → Bool × Address depth)) :=
  jointLaw (independentSampleLaw fun _ : Fin basisShots => P.basisShot)
    (fun b => independentSampleLaw fun _ : Fin interferenceShots => P.interferenceShot q hq (List.ofFn b))

/-- Distance from the normalized direction bounds the basis measurement error. -/
theorem basis_shot_tv_le (P : TomographyPreparation depth I)
    (direction : Address depth → ℝ) (hDirection : ∑ i, direction i ^ 2 = 1) :
    tvDist P.basisShot (basisSampleLaw direction hDirection) ≤
      ‖toEuclidean_fromVec (P.decodedState - embeddedDirection P.place direction)‖ :=
  measured_basis_shot_tv_le P.place P.decodedState P.decoded_state_normalized direction hDirection
    (readPlacedAddress P.place P.fallback) (read_placed_address P.place P.fallback)

/-- The interference measurement error adds the relative calibration imbalance
to the decoded-state error, uniformly over the nonempty first records. -/
theorem interference_shot_tv_le (P : TomographyPreparation depth I) (q : ℝ) (hq : 0 ≤ q)
    (direction : Address depth → ℝ) (hDirection : ∑ i, direction i ^ 2 = 1)
    (samples : List (Address depth)) (hSamples : samples ≠ []) :
    tvDist (P.interferenceShot q hq samples) (interferenceSampleLaw direction hDirection samples hSamples) ≤
      ‖toEuclidean_fromVec (P.decodedState - embeddedDirection P.place direction)‖ +
        2 * (|P.successProbability - q| / (P.successProbability + q)) := by
  obtain ⟨_, h⟩ := embedded_heralded_interference_shot_tv_le P.place P.fallback P.target
    P.decoder P.success q P.seed P.decoder_unitary hq P.success_pos direction hDirection samples hSamples
  exact h

/-- The total variation bound on the actual two-batch record charges each
shot for the target-state error and each interference shot for calibration. -/
theorem transcript_tv_le (P : TomographyPreparation depth I) (q : ℝ) (hq : 0 ≤ q)
    (direction : Address depth → ℝ) (hDirection : ∑ i, direction i ^ 2 = 1)
    (basisShots interferenceShots : ℕ) (hBasis : 0 < basisShots) :
    let δ := ‖toEuclidean_fromVec (P.decodedState - embeddedDirection P.place direction)‖
    let imbalance := |P.successProbability - q| / (P.successProbability + q)
    tvDist (P.transcript q hq basisShots interferenceShots)
      (signedTomographyLaw direction hDirection basisShots interferenceShots hBasis) ≤
      basisShots * δ + interferenceShots * (δ + 2 * imbalance) :=
  signed_tomography_transcript_tv_le direction hDirection hBasis P.basisShot
    (fun b => P.interferenceShot q hq (List.ofFn b)) _ _
    (P.basis_shot_tv_le direction hDirection)
    (fun b hne => P.interference_shot_tv_le q hq direction hDirection (List.ofFn b) hne)

end TomographyPreparation
end Qatlib.Concepts.QRAM.SignedReadout
