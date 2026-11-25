/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.Model.StateModel

@[expose] public section

/-!
# Copy budgets are monotone

Copy complexity is measured by the total number of copies `k * t` of a `k`-block, `t`-copy
scheme, and every display in the paper compares that number with a budget `m`. This module
records the bookkeeping step that makes those comparisons usable: a scheme certifying the
hypothesis within `m` copies still does so within any larger budget `m'`. It is the bridge
between the model layer's `FixedCertifiable d t ε m` and the `O(·)`/`Õ(·)` bounds of
Theorem 1.1, whose right-hand sides are real-valued budget functions.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Section 1.1 and Theorem 1.1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StateTesting26.MainResults.CostAccounting

open Qatlib.Papers.StateTesting26.MainResults.Model

/-- Fixed `t`-copy certification within a copy budget is monotone in the budget. -/
theorem FixedCertifiable_mono {d t : ℕ} {ε m m' : ℝ} (h : FixedCertifiable d t ε m)
    (hm : m ≤ m') : FixedCertifiable d t ε m' := by
  intro σ
  obtain ⟨k, Ω, hΩ, S, hcost, hcert⟩ := h σ
  exact ⟨k, Ω, hΩ, S, hcost.trans hm, hcert⟩

end Qatlib.Papers.StateTesting26.MainResults.CostAccounting
