/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionQSVTGeneralStat
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge

/-!
# Source-convention QSVT theorem

This module proves `sourceConventionQSVTGeneral`, assembling real phase synthesis, minimal phase
lengths, and parity-dependent projected singular transforms. The statement packages the
source-convention consequences of the alternating-phase QSVT framework in
[GilyenSuLowWiebe2019].

## Main statements

* `sourceConventionQSVTGeneral`: Establish the complete packaged source-convention statement.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.QsVtMain
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- Establish the source-convention QSVT statement, including optimal phase lengths,
parity-dependent corners, and constant responses [GilyenSuLowWiebe2019]. -/
theorem sourceConventionQSVTGeneral : SourceConventionQSVTGeneral := by
  constructor
  · intro H I O _ _ _ _ _ _ A U L R p d h hd hdeg hpar hb
    obtain ⟨Φ, hlen, hre, hmin⟩ := source_minimal_degree_existence p d hd hdeg hpar hb
    refine ⟨Φ, hlen, hre, hmin, ?_, ?_⟩
    · intro hodd
      exact source_corner_odd_eq h Φ (hlen.symm ▸ hodd)
    · intro heven
      exact source_corner_even_eq h Φ (hlen.symm ▸ heven)
  · exact source_constant_minimal_length

end Qatlib.Concepts.QsvtCore.QsVtMain
