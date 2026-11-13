/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.AdversaryValue.GeneralAdversaryValueIdentStat

/-!
# Identifying the general adversary value

`generalAdversaryValueIdentification` identifies the general adversary value with the filtered
γ₂ value using the evaluation mask. It also compares this value with the version using the
unmasked query filters, with factor `2 * (1 - 1 / Fintype.card E)`.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `generalAdversaryValueIdentification`: The identification and two comparison inequalities.
* `generalAdversaryValueIdentification_constant`: The identification and comparisons for a
  constant function.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.AdversaryValue
open Qatlib
open scoped ENNReal

/-- For a constant function, the general adversary value equals the evaluation-masked filtered
γ₂ value and satisfies both comparison inequalities with the unmasked value. -/
theorem generalAdversaryValueIdentification_constant {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → E) (hf : ∀ x y, f x = f y) :
    generalAdversaryValue input f = filteredGamma2 (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) ∧
    generalAdversaryValue input f ≤
      filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ∧
    filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ≤
      ENNReal.ofReal (2 * (1 - 1 / (Fintype.card E : ℝ))) * generalAdversaryValue input f := by
  have hz : gramFunctionEvaluationMatrix f = (0 : Matrix X X ℂ) := by
    ext x y; simp [gramFunctionEvaluationMatrix, hf x y]
  have he : generalAdversaryValue input f = filteredGamma2 (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) := by
    rw [generalAdversaryValue_constant input f hf, hz, filteredGamma2_zero_matrix]
  exact ⟨he, generalAdversaryValueComparison_of_identification input f he⟩

/-- The general adversary value equals the evaluation-masked filtered γ₂ value, and the unmasked
value lies between it and `2 * (1 - 1 / Fintype.card E)` times it [LeeEtAl2011]. -/
theorem generalAdversaryValueIdentification : GeneralAdversaryValueIdentification := by
  intro X E _ _ _ _ n input f
  have he : generalAdversaryValue input f = filteredGamma2 (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y*gramFunctionEvaluationMatrix f x y) := by
    rw [generalAdversaryValue_eq_relaxed_dual]
    exact (filteredGamma2_strong_duality X n (gramFunctionEvaluationMatrix f) _).1.symm
  exact ⟨he,generalAdversaryValueComparison_of_identification input f he⟩
end Qatlib.Concepts.ConversionCore.AdversaryValue
