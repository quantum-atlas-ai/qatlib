/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.SampledAttemptSuccessStat
set_option warningAsError false
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

theorem singleEvent_mass {A : Type*} [Fintype A] [DecidableEq A]
    (p : FinDist A) (P : A → Prop) [DecidablePred P] :
    p.probEvent (L := 1) (fun ω => P (ω 0)) =
      ∑ a ∈ Finset.univ.filter P, p.prob a := by
  have he := p.expect_coord (L := 1) 0 (fun a => if P a then (1 : ℝ) else 0)
  simpa only [FinDist.probEvent, Finset.sum_filter, mul_ite, mul_one, mul_zero] using! he
end
noncomputable section

theorem attemptFactor_sound (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (y z : Fin M) (d : ℕ) (h : attemptFactor N M a (y, z) = some d) :
    1 < d ∧ d < N ∧ d ∣ N := by
  obtain ⟨r, _, hr⟩ := Option.bind_eq_some_iff.mp h
  exact orderFactor_sound N a r d hr
end
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
