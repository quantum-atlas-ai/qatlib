/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# Reference extended mixture schedules

`referenceMixtureSchedule` recursively composes finite mixture maps with time dependent sampling
laws and operator families. The zero step map is the identity, and step `n + 1` applies the
mixture indexed by `n` after the preceding schedule. This is the finite mixture framework for
channels with a reference system [Watrous2018].

## Main statements

* `referenceMixtureSchedule`: The chronological composition of the first `n` reference extended
  mixture maps with sampling laws `d` and operator families `U`, starting from the identity map.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixtureLaw.ScheduleLaw

/-- The chronological composition of the first `n` reference extended mixture maps with sampling
laws `d` and operator families `U`, starting from the identity map. -/
noncomputable def referenceMixtureSchedule {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : ℕ → FinDist J) (U : ℕ → J → Operator D) (r : ℕ) :
    ℕ → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ →
      Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ
  | 0, ρ => ρ
  | n + 1, ρ => referenceMixture (d n) (U n) r (referenceMixtureSchedule d U r n ρ)

end Qatlib.Concepts.MixtureLaw.ScheduleLaw
