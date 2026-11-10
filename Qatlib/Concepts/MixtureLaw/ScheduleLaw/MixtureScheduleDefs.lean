/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixtureLaw.ScheduleLaw

noncomputable def referenceMixtureSchedule {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : ℕ → FinDist J) (U : ℕ → J → Operator D) (r : ℕ) :
    ℕ → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ →
      Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ
  | 0, ρ => ρ
  | n + 1, ρ => referenceMixture (d n) (U n) r (referenceMixtureSchedule d U r n ρ)

end Qatlib.Concepts.MixtureLaw.ScheduleLaw
