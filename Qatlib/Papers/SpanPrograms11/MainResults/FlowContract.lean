/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanPrograms11.MainResults.SpanProgramWitness

@[expose] public section


set_option autoImplicit false
open scoped BigOperators

open Qatlib.Papers.SpanPrograms11.MainResults

namespace Qatlib.Papers.SpanPrograms11.MainResults

/-- A finite loading graph cannot have a unit source and conservation at every
other vertex; accepting certificate sinks must absorb the outgoing flow. -/
theorem legacy_flow_impossible {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E]
    (src : E → Finset ι) (j : E → ι) (flow : E → ℝ)
    (hcons : ∀ T : Finset ι, T ≠ ∅ → inFlow src j flow T = outFlow src flow T)
    (hsrc : outFlow src flow ∅ = 1) : False := by
  classical
  have htotal : (∑ T : Finset ι, outFlow src flow T) =
      ∑ T : Finset ι, inFlow src j flow T := by
    simp only [outFlow, inFlow]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp
  have hdiv : (∑ T : Finset ι, (outFlow src flow T - inFlow src j flow T)) =
      outFlow src flow ∅ - inFlow src j flow ∅ := by
    apply Finset.sum_eq_single ∅
    · intro T _ hT
      rw [hcons T hT, sub_self]
    · intro h
      exact False.elim (h (Finset.mem_univ ∅))
  rw [Finset.sum_sub_distrib, htotal, sub_self] at hdiv
  rw [inFlow_empty, hsrc] at hdiv
  norm_num at hdiv

end Qatlib.Papers.SpanPrograms11.MainResults
