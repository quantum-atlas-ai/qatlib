/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientReadoutStat
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientLaws

/-!
# Full-range gradient readout

`fullRangeGradientReadout` proves the readout specification for the dyadic value-oracle program.
It combines clean character kickback with phase-error transport and an affine-output probability
bound, following the finite-grid mechanism of [Jordan2005Gradient].

## Main statements

* `fullRangeGradientReadout`: one-query readout has the specified resources, event-error bound,
  and affine success guarantee.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ReadoutWindow

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical BigOperators

/-- Proves the full-range readout specification, including one-query resources, normalization,
clean output factorization, event stability, and the affine cosine-squared success bound.
This formalizes the finite-grid value-oracle construction associated with
[Jordan2005Gradient]. -/
theorem fullRangeGradientReadout : FullRangeGradientReadout := by
  intro d M hM K k f lo s R hk hs hR hguard hf
  obtain ⟨hunit,hqueries,hgates⟩ := full_range_program_resources d M hM K k
  refine ⟨hunit,hqueries,hgates,full_range_output_normalized d M hM K k f lo s,
    full_range_program_clean d M hM K k f lo s,?_,?_⟩
  · intro E
    rw [full_range_output_marginal]
    have he := gradient_actual_phase_event_error d M hM
      (fullRangePhase K k (fullRangeValueTable K k f lo s)) (fun x => s*(f x-lo))
      (1/(2:ℝ)^k) (by positivity) (full_range_phase_precision K k f lo s R hs hR hguard hf) E
    convert! he using 1
    ring
  · intro q c haffine
    rw [full_range_output_marginal]
    have hQ : (0:ℝ)<(2:ℝ)^k := by positivity
    have hQ4 : (4:ℝ)≤(2:ℝ)^k := by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1≤2) hk
    apply gradient_affine_precision_cos2_window d M hM q c (2*Real.pi/(2:ℝ)^k)
    · positivity
    · apply (div_le_iff₀ hQ).mpr
      nlinarith [Real.pi_pos]
    · intro x
      refine ⟨0,?_⟩
      have hp := full_range_phase_precision K k f lo s R hs hR hguard hf x
      rw [← haffine x]
      simp only [Int.cast_zero,sub_zero]
      have he : (2*Real.pi/(2:ℝ)^k)/(2*Real.pi)=1/(2:ℝ)^k := by field_simp
      rw [he]
      exact hp
end Qatlib.Concepts.GradientOracle.FullRange
