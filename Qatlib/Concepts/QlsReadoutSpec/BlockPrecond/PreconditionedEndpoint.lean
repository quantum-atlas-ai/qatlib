/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.OptimalCoefficientBlockEncodingStat
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditionedEncoding
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditioningParameters

/-!
# Completed preconditioned reciprocal encoding

This module proves `optimalCoefficientBlockEncoding_complete`. It combines the preconditioned
encoding, singular-gap estimate, and reciprocal polynomial construction to obtain a phase list
with explicit degree and compilation counts. The resulting postselection has the specified
success lower bound and returns a normalized state within `4 * ε` of the normalized original
pseudoinverse solution.

The construction applies a polynomial reciprocal transformation to a projected encoding
[GilyenSuLowWiebe2019].

## Main statements

* `optimalCoefficientBlockEncoding_complete`: Completes the optimal-coefficient encoding and
  postselection specification.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

/-- Establishes `OptimalCoefficientBlockEncodingSubgoal` by constructing the preconditioned
reciprocal encoding with its degree, coefficient, compilation-count, success-probability,
and normalized output-error guarantees. The construction uses the singular value
transformation framework [GilyenSuLowWiebe2019]. -/
theorem optimalCoefficientBlockEncoding_complete : OptimalCoefficientBlockEncodingSubgoal := by
  intro H I O _ _ _ _ _ _ A U L R κ ε t c s b hκ hε hε1 hc henc hb hs ht hgap hconsistent hτ
  have hκ0 : 0<κ := by linarith
  have hc0 : 0< c := by linarith
  have hparams:=preconditioning_scale_and_solution A b κ t c s hb hκ hc ht hs hgap hconsistent hτ.1
  have hs0 : 0< s := hparams.1
  have hs1 : s<1 := hparams.2.1
  have hMnorm:=preconditioned_pseudoinverse_norm A b κ t c s hb hκ hc ht hs hgap hconsistent hτ.2
  let κ' : ℝ:=2*c^2*κ
  have hκ' : 1<κ' := by dsimp [κ'];nlinarith [sq_nonneg (c-1)]
  have hMgap := singular_gap_of_pseudoinverse_norm (stateScaling s b*A) κ' (by linarith) hMnorm
  have hMenc:=preconditioned_projectedEncoding A U L R b s henc hb hs0 hs1
  let J:=nearOptimalReciprocalJ κ' ε
  let c₀ : ℝ:=(4*(J:ℝ))⁻¹
  obtain ⟨Φ,hlen,_,hcounts,hW⟩:=nearOptimalReciprocal_inverse_word (Bool×H) I O
    (stateScaling s b*A) (preconditionedUnitary L b s U) (flagFrame L) (flagFrame R) κ' ε hκ' hε hε1 hMenc hMgap
  have hscale:=nearOptimalReciprocal_scale_parameters κ' ε hκ' hε hε1.le
  have hc₀ : 0< c₀ := hscale.1
  have hdegree : (2*J+1:ℝ)≤32*κ'*Real.log (κ'/ε) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using!
      (nearOptimalReciprocal_family_degree_parity κ' ε hκ' hε hε1).2.2.2.2.2
  have htarget : ‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖=
      c₀*‖stateVector (matrixPseudoinverse (stateScaling s b*A)*ᵥb)‖ := by
    rw [Matrix.smul_mulVec]
    change ‖(c₀:ℂ)•stateVector (matrixPseudoinverse (stateScaling s b*A)*ᵥb)‖=_
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc₀]
  have htargetLower : c₀*κ≤‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖ := by
    rw [htarget]
    exact mul_le_mul_of_nonneg_left hparams.2.2 hc₀.le
  have hgapOutput : 2*c₀*ε<‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖ :=
      by nlinarith
  obtain ⟨_,φ,hout,hstate⟩:=Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap hW hb hgapOutput
  have hprob:=Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower hW hb hgapOutput.le
  have hnormalized:=preconditioning_normalized_target A b s c₀ hs0 hc₀ hb hconsistent
  have hbaseTarget : c₀≤‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖ := by
    have hh:=mul_le_mul_of_nonneg_left hκ.le hc₀.le
    have hs : c₀≤c₀*κ := by simpa only [mul_one] using! hh
    exact hs.trans htargetLower
  have herr : 2*(2*c₀*ε)/‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖≤4*ε := by
    apply (div_le_iff₀ (lt_trans (by positivity : (0:ℝ)<2*c₀*ε) hgapOutput)).mpr
    have hh:=mul_le_mul_of_nonneg_left hbaseTarget (by positivity : (0:ℝ)≤4*ε)
    nlinarith [hh]
  refine ⟨J,c₀,Φ,hlen,hdegree,hc₀,hscale.2,hW,hcounts,?_,φ,hout,hstate.2.1,?_⟩
  · have he0 : 0<1-2*ε := by linarith
    have hl : 0≤c₀*κ*(1-2*ε) := by positivity
    have hshrink:=mul_le_mul_of_nonneg_left hκ.le (by positivity : (0:ℝ)≤2*c₀*ε)
    have hUpper :
        c₀*κ*(1-2*ε)≤‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖-2*c₀*ε :=
        by nlinarith [hshrink]
    have hh :=
        (sq_le_sq₀ hl (by linarith : 0≤‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖-2*c₀*ε)).mpr hUpper
    exact hh.trans (by simpa only [div_one] using! hprob)
  · have herror:=hstate.2.2
    change ‖stateVector φ-NormedSpace.normalize
        (stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb))‖≤2*(2*c₀*ε)/‖stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)‖ at herror
    rw [hnormalized] at herror
    exact herror.trans herr
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
