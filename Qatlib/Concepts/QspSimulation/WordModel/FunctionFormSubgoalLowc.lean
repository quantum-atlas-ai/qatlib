/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.FunctionFormSubgoalStat

/-!
# Polynomial function form of QSP words

This module proves `functionFormSubgoal`, expressing the entries of a QSP word using four
complex polynomials. The diagonal entries are polynomial responses, and the off-diagonal entries
carry the factor i√(1 − x²), with degree and parity determined by the phase-list length.
Background and related constructions are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `functionFormSubgoal`: proves the polynomial entry representation.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.QspSimulation.WordModel

open Qatlib

/-- Every QSP phase list has the polynomial entry representation specified by
`FunctionFormSubgoal`, with the stated degree bounds, parity, and off-diagonal square-root
factors. -/
theorem functionFormSubgoal : FunctionFormSubgoal := by
  intro phis
  exact qsp_function_form phis

end Qatlib.Concepts.QspSimulation.WordModel
