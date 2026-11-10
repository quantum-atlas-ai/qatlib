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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open scoped ENNReal BigOperators Classical

abbrev ExecOutcome (α : Type) := Option α

abbrev ExecLaw (α : Type) [Fintype α] := FinDist (Option α)

noncomputable def neverMass {α : Type} [Fintype α] (p : ExecLaw α) : ℝ := p.prob none

noncomputable def haltedMass {α : Type} [Fintype α] (p : ExecLaw α) : ℝ :=
  1 - neverMass p

noncomputable def execExpectedCost {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) : ENNReal :=
  ∑ o, ENNReal.ofReal (p.prob o) * (c o : ENNReal)

noncomputable def execPeakSpace {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) : ℕ :=
  Finset.sup (Finset.univ.filter (fun o => 0 < p.prob o)) c

structure ExecResource where

  queries : ℕ

  gates : ℕ

  fairBits : ℕ
  deriving DecidableEq, Repr

def execResource {α : Type} (c : ExecOutcome α → ExecResource) (o : ExecOutcome α) : ExecResource :=
  c o

noncomputable def sourceCutoff (N : ℕ) : ℕ := sourceDeadline N

noncomputable def chargedCutoff (N : ℕ) : ℕ := chargedBudget N

noncomputable def sourceCutoffReal (N : ℕ) : ℝ := sourceTimeout N

end Qatlib.Concepts.AmplitudeSearch.Amplification
