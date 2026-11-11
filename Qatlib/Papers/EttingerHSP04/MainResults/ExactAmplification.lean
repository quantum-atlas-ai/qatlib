/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EttingerHSP04.MainResults.ExactTest
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Exact amplification of the hidden-subgroup ancilla test

Source: Ettinger–Høyer–Knill (2004), arXiv:quant-ph/0401083v1, section 2.2.
The promoted amplification probabilities turn the `1/4` versus `3/4` ancilla
test into an exact distinguisher after one amplification round.
-/

namespace Qatlib.Papers.EttingerHSP04.MainResults

open Qatlib.Papers.EttingerHSP04.MainResults

open scoped BigOperators


/-- One round of amplitude amplification turns the `1/4` versus `3/4` test into
an exact distinguisher. -/
theorem ampProb_exact_distinguish :
    ampProb (1 / 4) = 1 ∧ ampProb (3 / 4) = 0 :=
  ⟨ampProb_quarter, ampProb_three_quarters⟩

end Qatlib.Papers.EttingerHSP04.MainResults
