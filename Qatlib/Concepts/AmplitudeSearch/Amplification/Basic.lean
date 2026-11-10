/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib

variable {N : ℕ} {α : Type*} [LinearOrder α]

def amplifiedCombine (T : Fin N → α) (a b : Fin N) : Fin N :=
  if T b < T a then b else a

noncomputable def amplifiedStep (T : Fin N → α) (hN : 0 < N)
    (prev : PMF (Fin N × ℕ)) : PMF (Fin N × ℕ) :=
  prev.bind fun p =>
    (chargedInitialPMF T hN (chargedBudget N)).bind fun f =>
      PMF.pure (amplifiedCombine T p.1 f.1, p.2 + f.2)

noncomputable def amplifiedMinimumPMF (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    PMF (Fin N × ℕ) :=
  match c with
  | 0 => PMF.pure (⟨0, hN⟩, 0)
  | c' + 1 => amplifiedStep T hN (amplifiedMinimumPMF T hN c')

end Qatlib.Concepts.AmplitudeSearch.Amplification
