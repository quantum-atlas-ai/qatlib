/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SectionIIAmplifiedRuntimeCorrectedStat
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

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

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

theorem sectionIIAmplifiedRuntime : SectionIIAmplifiedRuntimeCorrected :=
  fun D M hM eig V B j d η hV hB hd h2d hη hη1 heig hbudget =>
    sin_envelope_aa_success_and_cost M hM eig V B j d η hV hB hd h2d hη hη1 heig hbudget

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
