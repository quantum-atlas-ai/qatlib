/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction

/-!
# Approximate channel words

This module defines finite words of quantum channels and records actual and ideal channels with
a real error allowance in `ApproxStep`. `actualWord` and `idealWord` compose the corresponding
channels in execution order, while `budget` sums the allowances. These definitions support
channel comparison by the trace and diamond norms described in [Watrous2018].

## Main definitions

* `run`: sequential composition of a channel list.
* `ApproxStep`: actual and ideal channels with a step error allowance.
* `actualWord`, `idealWord`, and `budget`: composed channels and their total allowance.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.RawChannelWord.CptpWordBound
open Matrix
set_option autoImplicit false
noncomputable section

/-- The sequential composition of the channels in a list, with the identity channel for the
empty list. -/
def run {D : ℕ} : List (QuantumChannel D D) → QuantumChannel D D
  | [] => QuantumChannel.id D
  | T::ts => (run ts).comp T

/-- An actual channel, an ideal channel, and a real step error allowance. -/
structure ApproxStep (D : ℕ) where
  actual : QuantumChannel D D
  ideal : QuantumChannel D D
  error : ℝ

/-- The channel obtained by executing all actual channels in the approximate-step list. -/
def actualWord {D : ℕ} (p : List (ApproxStep D)) := run (p.map ApproxStep.actual)
/-- The channel obtained by executing all ideal channels in the approximate-step list. -/
def idealWord {D : ℕ} (p : List (ApproxStep D)) := run (p.map ApproxStep.ideal)
/-- The sum of the real step error allowances in the channel word. -/
def budget {D : ℕ} (p : List (ApproxStep D)) : ℝ := (p.map ApproxStep.error).sum
end
end Qatlib.Concepts.RawChannelWord.CptpWordBound
