/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability

/-!
# Combining charged minimum-finding runs

`amplifiedCombine` keeps the better of two candidate indices. `amplifiedStep` combines a
previous candidate with an independent charged minimum-finding run and adds their recorded
costs; `amplifiedMinimumPMF` iterates this construction.

These distributions model the repeated-run success amplification discussed for quantum minimum
finding in [DurrHoyer1996].

## Main statements

* `amplifiedStep`: combines candidates and accumulates their costs.
* `amplifiedMinimumPMF`: defines the distribution after a specified number of charged runs.

## References

* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib

variable {N : ℕ} {α : Type*} [LinearOrder α]

/-- Select the lower-valued of two candidates, retaining the first candidate in case of a tie. -/
def amplifiedCombine (T : Fin N → α) (a b : Fin N) : Fin N :=
  if T b < T a then b else a

/-- Combine a previous minimum-finding distribution with an independent charged run, selecting
the better candidate and adding their costs. -/
noncomputable def amplifiedStep (T : Fin N → α) (hN : 0 < N)
    (prev : PMF (Fin N × ℕ)) : PMF (Fin N × ℕ) :=
  prev.bind fun p =>
    (chargedInitialPMF T hN (chargedBudget N)).bind fun f =>
      PMF.pure (amplifiedCombine T p.1 f.1, p.2 + f.2)

/-- The costed minimum-finding distribution obtained by combining `c` charged runs, starting
from index zero at zero cost. -/
noncomputable def amplifiedMinimumPMF (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    PMF (Fin N × ℕ) :=
  match c with
  | 0 => PMF.pure (⟨0, hN⟩, 0)
  | c' + 1 => amplifiedStep T hN (amplifiedMinimumPMF T hN c')

end Qatlib.Concepts.AmplitudeSearch.Amplification
