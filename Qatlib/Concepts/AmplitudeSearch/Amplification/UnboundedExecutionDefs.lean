/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds
import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedClock
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstruction
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumSourceCalibration
import Qatlib.Concepts.AmplitudeSearch.Amplification.SearchStoppingDefs

/-!
# Execution outcomes and resource accounting

This module represents execution outcomes by `ExecOutcome`, with `none` recording
nontermination, and finite outcome laws by `ExecLaw`. It defines halted mass, expected cost,
peak space on outcomes of positive mass, and resource records.

The cutoff aliases distinguish the source clock from the charged query budget used in
minimum-search analysis [DurrHoyer1996].

## Main statements

* `ExecLaw`: A finite probability distribution on execution outcomes.
* `execExpectedCost`: The expected natural-valued outcome cost, expressed in the extended
  nonnegative reals.
* `ExecResource`: A resource record containing query, gate, and fair-bit counts.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open scoped ENNReal BigOperators Classical

/-- Execution outcomes consisting of a returned value or `none` for nontermination. -/
abbrev ExecOutcome (α : Type) := Option α

/-- A finite probability distribution on execution outcomes. -/
abbrev ExecLaw (α : Type) [Fintype α] := FinDist (Option α)

/-- The probability mass assigned to the nonterminating outcome `none`. -/
noncomputable def neverMass {α : Type} [Fintype α] (p : ExecLaw α) : ℝ := p.prob none

/-- The halted mass, defined as one minus the nontermination mass. -/
noncomputable def haltedMass {α : Type} [Fintype α] (p : ExecLaw α) : ℝ :=
  1 - neverMass p

/-- The expected natural-valued outcome cost, expressed in the extended nonnegative reals. -/
noncomputable def execExpectedCost {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) : ENNReal :=
  ∑ o, ENNReal.ofReal (p.prob o) * (c o : ENNReal)

/-- The maximum space cost among outcomes with strictly positive probability mass. -/
noncomputable def execPeakSpace {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) : ℕ :=
  Finset.sup (Finset.univ.filter (fun o => 0 < p.prob o)) c

/-- A resource record containing query, gate, and fair-bit counts. -/
structure ExecResource where

  queries : ℕ

  gates : ℕ

  fairBits : ℕ
  deriving DecidableEq, Repr

/-- Evaluates an outcome-dependent resource assignment at the given outcome. -/
def execResource {α : Type} (c : ExecOutcome α → ExecResource) (o : ExecOutcome α) : ExecResource :=
  c o

/-- The natural-valued source deadline, aliased from `sourceDeadline`. -/
noncomputable def sourceCutoff (N : ℕ) : ℕ := sourceDeadline N

/-- The charged query cutoff, aliased from `chargedBudget`. -/
noncomputable def chargedCutoff (N : ℕ) : ℕ := chargedBudget N

/-- The real-valued source timeout, aliased from `sourceTimeout`. -/
noncomputable def sourceCutoffReal (N : ℕ) : ℝ := sourceTimeout N

end Qatlib.Concepts.AmplitudeSearch.Amplification
