/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU

/-!
# Analytic Error and Outer LCU Encodings

This module connects analytic approximation bounds to coefficient LCU block encodings.
`outer_blockEncoding_of_discrepancy` combines sample encoding errors with a norm bound on the
difference between a target matrix and its finite weighted sample sum.

`outer_blockEncoding_of_residue_bounds` specializes this discrepancy to a contour contribution
minus auxiliary and tail contributions. `outer_postselection_of_residue_bounds` then gives a
positive success probability and a normalized target-output approximation whenever the total
error is smaller than the target output norm. See [WangEtAl2026].

## Main statements

* `outer_blockEncoding_of_discrepancy` adds an analytic discrepancy to the weighted encoding
  error.
* `outer_blockEncoding_of_residue_bounds` combines the three supplied residue-related norm
  bounds.
* `outer_postselection_of_residue_bounds` supplies a probability lower bound and a conditional
  output error bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.Cbmd26.Algorithms

namespace CBMD

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

variable {J H O I : Type*}
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- Builds a target block encoding from sample encodings and a norm discrepancy bound for their
weighted sum. The scale is the coefficient-weighted sum of sample scales, and the error is
the weighted encoding error plus the supplied discrepancy. -/
theorem outer_blockEncoding_of_discrepancy
    (j₀ : J) (target : Matrix O I ℂ) (samples : J → Matrix O I ℂ)
    (U : J → Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (c : J → ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (samples j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hanalytic : ‖target - ∑ j, c j • samples j‖ ≤ δ) :
    BlockEncoding target
      (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀)
      (tagFrame j₀ L) (tagFrame j₀ R)
      (∑ j, ‖c j‖ * α j) ((∑ j, ‖c j‖ * ε j) + δ) := by
  exact (scaled_approximate_lcu_encoding j₀ samples U L R c α ε henc hmass).perturb
    hδ hanalytic

/-- Uses the contour-minus-auxiliary-minus-tail identity to bound the analytic discrepancy in an
outer coefficient LCU. The resulting encoding error is the weighted sample error plus `εIR +
εAE + εTR`. -/
theorem outer_blockEncoding_of_residue_bounds
    (j₀ : J) (target : Matrix O I ℂ) (samples : J → Matrix O I ℂ)
    (U : J → Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (c : J → ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (samples j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α))
    (contour auxiliary tail : Matrix O I ℂ)
    (hidentity : target - (∑ j, c j • samples j) = contour - auxiliary - tail)
    (εIR εAE εTR : ℝ)
    (hIR : ‖contour‖ ≤ εIR) (hAE : ‖auxiliary‖ ≤ εAE) (hTR : ‖tail‖ ≤ εTR) :
    BlockEncoding target
      (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀)
      (tagFrame j₀ L) (tagFrame j₀ R)
      (∑ j, ‖c j‖ * α j)
      ((∑ j, ‖c j‖ * ε j) + εIR + εAE + εTR) := by
  have hδ : 0 ≤ εIR + εAE + εTR :=
    add_nonneg (add_nonneg ((norm_nonneg _).trans hIR) ((norm_nonneg _).trans hAE))
      ((norm_nonneg _).trans hTR)
  have hanalytic : ‖target - ∑ j, c j • samples j‖ ≤ εIR + εAE + εTR := by
    rw [hidentity]
    calc
      ‖contour - auxiliary - tail‖ ≤ ‖contour - auxiliary‖ + ‖tail‖ := norm_sub_le _ _
      _ ≤ (‖contour‖ + ‖auxiliary‖) + ‖tail‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ εIR + εAE + εTR := add_le_add (add_le_add hIR hAE) hTR
  simpa only [add_assoc] using
    outer_blockEncoding_of_discrepancy j₀ target samples U L R c α ε henc hmass
      (εIR + εAE + εTR) hδ hanalytic

/-- When the total residue and sample error is smaller than the target output norm,
postselection has positive probability bounded below by the squared norm gap divided by the
squared LCU scale. The conditional output approximates the normalized target application
with error at most twice the total error divided by the target output norm. -/
theorem outer_postselection_of_residue_bounds
    (j₀ : J) (target : Matrix O I ℂ) (samples : J → Matrix O I ℂ)
    (U : J → Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (c : J → ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (samples j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α))
    (contour auxiliary tail : Matrix O I ℂ)
    (hidentity : target - (∑ j, c j • samples j) = contour - auxiliary - tail)
    (εIR εAE εTR : ℝ)
    (hIR : ‖contour‖ ≤ εIR) (hAE : ‖auxiliary‖ ≤ εAE) (hTR : ‖tail‖ ≤ εTR)
    (ψ : QState I) (hψ : Normalized ψ)
    (hgap : (∑ j, ‖c j‖ * ε j) + εIR + εAE + εTR <
      ‖stateVector (target *ᵥ ψ)‖) :
    let scale := ∑ j, ‖c j‖ * α j
    let error := (∑ j, ‖c j‖ * ε j) + εIR + εAE + εTR
    let V := coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀
    let L' := tagFrame j₀ L
    let R' := tagFrame j₀ R
    ((‖stateVector (target *ᵥ ψ)‖ - error) / scale) ^ 2 ≤
        postselectionProbability V L' R' ψ ∧
      0 < postselectionProbability V L' R' ψ ∧
      ∃ φ : QState O, postselectionOutput V L' R' ψ = some φ ∧
        IsNormalizedApplication target ψ φ (2 * error / ‖stateVector (target *ᵥ ψ)‖) := by
  (try dsimp only)
  have houter := outer_blockEncoding_of_residue_bounds j₀ target samples U L R c α ε
    henc hmass contour auxiliary tail hidentity εIR εAE εTR hIR hAE hTR
  exact ⟨Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower houter hψ hgap.le,
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap houter hψ hgap⟩

end CBMD

end Qatlib.Papers.Cbmd26.Algorithms
