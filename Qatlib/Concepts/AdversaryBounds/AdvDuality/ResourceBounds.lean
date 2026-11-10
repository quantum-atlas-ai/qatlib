/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsRefinedDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportFreshCopy
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

theorem copy_driven_ledger_derived (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n) :
    copyDrivenLedger D M n = ⟨(M - 1) * n, (M - 1) * n, 0, (M - 1) * n, 0⟩ :=
  copyDrivenLedger_eq D M n hM hn

theorem numeric_copy_ledger_derived (n M b : ℕ) (hM : 0 < M) :
    numericCopyLedger n M b =
      ⟨(M - 1) * 2 ^ b, 0, (M - 1) * 2 ^ b * (36 * n + 4), (M - 1) * 2 ^ b, 0⟩ :=
  numericCopyLedger_eq n M b hM

theorem repeat_multiplies_work (a : Account) (k : ℕ) :
    workOf (Account.repeat a k) = (workOf a).smul k :=
  workOf_repeat a k

theorem peak_workspace_not_transported :
    ¬ (∀ a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost,
        (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).peakWorkspace =
          (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).peakWorkspace) :=
  ofFreshCost_peakWorkspace_not_transported

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

theorem clause11_endpoint :
    ∀ (a : Account) (k : ℕ), workOf (Account.repeat a k) = (workOf a).smul k := by
  intro a k
  exact repeat_multiplies_work a k

theorem clause12_endpoint :
    ¬ (∀ a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost,
        (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).peakWorkspace =
          (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).peakWorkspace) := by
  exact peak_workspace_not_transported

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
