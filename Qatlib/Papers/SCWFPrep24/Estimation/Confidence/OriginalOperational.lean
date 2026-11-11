/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalLower
import Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Original Operational

One actual original supplied copy retains every address and spin coordinate, with the original one-over-square-root-grid normalization.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder Kronecker

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

/-- One actual original supplied copy retains every address and spin coordinate, with the original one-over-square-root-grid normalization. -/
def physicalAmplitude (d N : ℕ) (ψ : (Fin (d+1) → Fin N) → Bool → ℂ) :
    ((Fin (d+1) → Fin N) × Bool) → ℂ :=
  fun z => suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) z.2 z.1

/-- The actual maximum-Q operational computation satisfies the original full-domain real-output failure guarantee on its unpadded prefix stopping probabilities. -/
def OperationalAccurate (d N : ℕ) [NeZero N] (Q : ℕ)
    (P : OrdinaryCopyStopping ((Fin (d+1) → Fin N) × Bool) ℝ Q) (δ : ℝ) : Prop :=
  ∀ ψ : (Fin (d+1) → Fin N) → Bool → ℂ,
    (∀ a,(real0 ψ a)^2+(imag0 ψ a)^2+(real1 ψ a)^2+(imag1 ψ a)^2=1) →
    (∀ j : Fin (d+1),bellMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (periodicDoubleShift (d+1) N j)≤256/((N : ℝ)^2)) →
    (P.runProbability (physicalAmplitude d N ψ)
      (estimationFailure (originalLoss d N ψ) ((N : ℝ)^2)) Q).re≤δ

/-- The actual ordinary-copy operational accuracy implies the same complete-input measurement accuracy by internally deriving normalization, padding, a common event effect and exact output probabilities. -/
theorem operational_measurement_accuracy (d N : ℕ) [NeZero N] (h4 : 4∣N) (Q : ℕ)
    (P : OrdinaryCopyStopping ((Fin (d+1) → Fin N) × Bool) ℝ Q) (δ : ℝ)
    (hacc : OperationalAccurate d N Q P δ) :
    AllOriginalAccurate d N h4 Q (InputDim d N Q) (QuantumChannel.id (InputDim d N Q))
      (P.toCausal.toReadout (originalFiniteBasis d N h4 Q)) δ := by
  intro ψ hz hbell
  let v := physicalAmplitude d N ψ
  have hn : Normalized v := supplied_spin_state_normalized (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) hz
  have hv : (∑ z,v z*star (v z))=(1 : ℂ) := by
    have hi := (normalized_iff_inner_self v).mp hn
    simpa only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,mul_comm] using hi
  have he : CopyBudgetPadding.encodedCopies (originalFiniteBasis d N h4 Q) v=encodedOriginalField d N h4 Q ψ := by
    funext i
    simp only [CopyBudgetPadding.encodedCopies,CopyBudgetPadding.copies,encodedOriginalField,copies_zero]
    rfl
  change (P.toCausal.toReadout (originalFiniteBasis d N h4 Q)).born
    (outerProduct (encodedOriginalField d N h4 Q ψ)) (estimationFailure (originalLoss d N ψ) ((N : ℝ)^2))≤δ
  rw [←he,P.readout_probability (originalFiniteBasis d N h4 Q) v hv]
  exact hacc ψ hz hbell

/-- Every actual maximum-Q ordinary-copy stopping computation on the original full physical domain obeys the original confidence-uniform copy lower bound. Its quantum memory and real-output histories are integrated in physical branch operations; neither a fidelity nor a padded-readout representation is supplied as an assumption. -/
theorem original_operational_all_confidence_lower (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (hd : d+1=2 ∨ d+1=3) (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) (Q : ℕ)
    (P : OrdinaryCopyStopping ((Fin (d+1) → Fin N) × Bool) ℝ Q)
    (hacc : OperationalAccurate d N Q P δ) :
    (N : ℝ)^2*Real.log (1/δ)+(N : ℝ)*Real.sqrt ((N^(d+1) : ℕ)*Real.log (1/δ))≤131072*(Q : ℝ) :=
  original_all_confidence_lower d N hN h4 hd δ hδ hmax Q (InputDim d N Q)
    (QuantumChannel.id (InputDim d N Q)) (P.toCausal.toReadout (originalFiniteBasis d N h4 Q))
    (operational_measurement_accuracy d N h4 Q P δ hacc)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
