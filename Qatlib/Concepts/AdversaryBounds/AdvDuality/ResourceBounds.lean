/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsRefinedDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportFreshCopy

/-!
# Resource ledger endpoints

This module exposes exact copy-driven and numeric-copy resource ledgers and the scaling of work
under repetition. It also records the failure of universal workspace-peak transport through
`Account.ofFreshCost`. The distinction between circuit work and space resources is part of the
computational framework in [NielsenChuang2010].

`thresholdGoal_endpoint` and the numbered clause endpoints package these statements together
with direct consequences of the uniform resource-bound predicates.

## Main statements

* `thresholdGoal_endpoint`: Exact copy-driven and numeric-copy ledger formulas.
* `clause11_endpoint`: Repetition multiplies the work ledger.
* `clause12_endpoint`: Workspace peaks do not universally commute with cost conversion.
* `clause13_endpoint`: Pointwise consequences of uniform upper and lower bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.ResourceBounds.AsymBounds

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib

set_option autoImplicit false

/-- If `M ≥ 2` and `n > 0`, the copy-driven ledger has `(M - 1) * n` copies, partial swaps, and
discards, with no local gates or bit queries. -/
theorem copy_driven_ledger_derived (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n) :
    copyDrivenLedger D M n = ⟨(M - 1) * n, (M - 1) * n, 0, (M - 1) * n, 0⟩ :=
  copyDrivenLedger_eq D M n hM hn

/-- If `M > 0`, the numeric-copy ledger has `(M - 1) * 2 ^ b` copies and discards, that many
times `36 * n + 4` local gates, and no partial swaps or bit queries. -/
theorem numeric_copy_ledger_derived (n M b : ℕ) (hM : 0 < M) :
    numericCopyLedger n M b =
      ⟨(M - 1) * 2 ^ b, 0, (M - 1) * 2 ^ b * (36 * n + 4), (M - 1) * 2 ^ b, 0⟩ :=
  numericCopyLedger_eq n M b hM

/-- Repeating an account `k` times multiplies its work ledger by `k`. -/
theorem repeat_multiplies_work (a : Account) (k : ℕ) :
    workOf (Account.repeat a k) = (workOf a).smul k :=
  workOf_repeat a k

/-- Converting fresh costs to accounts does not preserve sequential composition of workspace
peaks for all pairs of costs. -/
theorem peak_workspace_not_transported :
    ¬ (∀ a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost,
        (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).peakWorkspace =
          (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).peakWorkspace) :=
  ofFreshCost_peakWorkspace_not_transported

/-- Packages the exact copy-driven and numeric-copy ledger formulas under their respective
positivity assumptions. -/
theorem thresholdGoal_endpoint :
    (∀ (D M n : ℕ), 2 ≤ M → 0 < n →
      copyDrivenLedger D M n = ⟨(M - 1) * n, (M - 1) * n, 0, (M - 1) * n, 0⟩) ∧
    (∀ (n M b : ℕ), 0 < M →
      numericCopyLedger n M b =
        ⟨(M - 1) * 2 ^ b, 0, (M - 1) * 2 ^ b * (36 * n + 4), (M - 1) * 2 ^ b, 0⟩) := by
  refine ⟨?_, ?_⟩
  · intro D M n hM hn
    exact copy_driven_ledger_derived D M n hM hn
  · intro n M b hM
    exact numeric_copy_ledger_derived n M b hM

/-- Every account satisfies linear scaling of its work ledger under finite repetition. -/
theorem clause11_endpoint :
    ∀ (a : Account) (k : ℕ), workOf (Account.repeat a k) = (workOf a).smul k := by
  intro a k
  exact repeat_multiplies_work a k

/-- Universal preservation of workspace peaks under conversion and sequential composition of
fresh costs fails. -/
theorem clause12_endpoint :
    ¬ (∀ a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost,
        (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).peakWorkspace =
          (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).peakWorkspace) := by
  exact peak_workspace_not_transported

/-- Uniform upper and lower resource bounds imply their pointwise inequalities, together with
the reflexive identity for the sum of the two growth coordinates. -/
theorem clause13_endpoint :
    (∀ (R : ℕ → ℕ) (C d : ℕ), uniformUpperBound R C d →
      ∀ n : ℕ, R n ≤ C * (n + 1) ^ d) ∧
    (∀ (R : ℕ → ℕ) (f : ℕ → ℕ), uniformLowerBound R f →
      ∀ n : ℕ, f n ≤ R n) ∧
    (∀ (g : GrowthFilter), g.inputSize + g.inverseEpsilon = g.inputSize + g.inverseEpsilon) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R C d h n
    exact h n
  · intro R f h n
    exact h n
  · intro g
    rfl

end Qatlib.Concepts.AdversaryBounds.AdvDuality
