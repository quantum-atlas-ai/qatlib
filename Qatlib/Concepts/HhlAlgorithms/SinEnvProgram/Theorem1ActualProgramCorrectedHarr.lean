/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1ActualProgramCorrectedStat
import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers

/-!
# Proof of the corrected sine-envelope HHL specification

This module assembles the filter laws, preparation identities, circuit counts, and error
estimates into `Theorem1ActualProgramCorrected`. The result formalizes the positive-spectrum
sine-envelope program analysis associated with [HarrowHassidimLloyd2009].

## Main statements

* `theorem1ActualProgram`: the corrected program guarantee package.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

/-- The corrected program specification holds, including basic laws, workspace and relative mass
estimates, and normalized well-branch accuracy. See [Harrow et al., Theorem
1][HarrowHassidimLloyd2009]. -/
theorem theorem1ActualProgram : Theorem1ActualProgramCorrected :=
  ⟨⟨sin_envelope_filter_bounded, sin_envelope_filter_branch_values,
     sin_envelope_h_normalized, sin_envelope_flag_rotation_unitary_and_column,
     sin_envelope_state_normalized_and_prep, sin_envelope_word_legality_and_counts⟩,
   fun D M hM eig V B j d η hV hB hd hη hη1 heig hbudget =>
     ⟨sin_envelope_hhl_full_workspace_error M hM eig V B j d η hV hB hd hη hη1 heig hbudget,
      sin_envelope_postselection_mass_stability M hM eig V B j d η hV hB hd hη hη1 heig
        hbudget⟩,
   fun D M hM eig V B j d η hV hB hd h2d hη hη1 heig hbudget =>
     ⟨sin_envelope_conditional_well_output_error M hM eig V B j d η hV hB hd h2d hη hη1 heig
         hbudget,
      sin_envelope_well_mass_stability M hM eig V B j d η hV hB hd h2d hη hη1 heig hbudget,
      sin_envelope_ideal_well_output_direction eig V B j d (fun i => (heig i).1)⟩⟩

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
