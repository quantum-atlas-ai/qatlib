/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.SampledAttemptSuccessStat

/-!
# Single-attempt probability and factor soundness

Provides the one-sample event mass formula and soundness of the continued-fraction-based
factoring attempt. The theorem `attemptFactor_sound` guarantees that every returned value is a
proper nontrivial divisor, as needed by the factoring construction associated with [Shor1997].

## Main statements

* `singleEvent_mass`: Expands a one-sample event probability as a finite sum.
* `attemptFactor_sound`: Proves soundness of every returned factor.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.OrderRecovery

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

open Qatlib
open scoped Classical

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
noncomputable section

/-- A one-sample event probability is the sum of the masses of all outcomes satisfying its
predicate. -/
theorem singleEvent_mass {A : Type*} [Fintype A] [DecidableEq A]
    (p : FinDist A) (P : A → Prop) [DecidablePred P] :
    p.probEvent (L := 1) (fun ω => P (ω 0)) =
      ∑ a ∈ Finset.univ.filter P, p.prob a := by
  have he := p.expect_coord (L := 1) 0 (fun a => if P a then (1 : ℝ) else 0)
  simpa only [FinDist.probEvent, Finset.sum_filter, mul_ite, mul_one, mul_zero] using! he
end
noncomputable section

/-- If `attemptFactor` returns `d`, then `d` divides `N` and satisfies `1 < d < N`. -/
theorem attemptFactor_sound (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (y z : Fin M) (d : ℕ) (h : attemptFactor N M a (y, z) = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  obtain ⟨r, _, hr⟩ := Option.bind_eq_some_iff.mp h
  exact orderFactor_sound N a r d hr
end
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
