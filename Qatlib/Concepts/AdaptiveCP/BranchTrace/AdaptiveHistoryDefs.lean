/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Mathlib.Data.Vector.Basic

/-!
# Adaptive branch histories and accumulated charges

This module defines the operator map and accumulated cost along a finite adaptive outcome
history. `branch` composes instrument branches chosen by the current history, `charge` adds the
associated costs, and `record` pairs the two. For background, see [Watrous2018].

## Main statements

* `branch`: The linear map obtained by following a list of outcomes under a history-dependent
  instrument policy, extending the history after each outcome.
* `charge`: The sum of the costs assigned to the successive histories encountered along an
  outcome list.
* `record`: The branch linear map and accumulated history-dependent charge associated with a
  finite outcome sequence.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib
variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

/-- The linear map obtained by following a list of outcomes under a history-dependent instrument
policy, extending the history after each outcome. -/
def branch (policy : List O → Instrument O D D) :
    List O → List O → (Operator D →ₗ[ℂ] Operator D)
  | _, [] => LinearMap.id
  | h, o :: os => (branch policy (h ++ [o]) os).comp ((policy h).branch o)
/-- The sum of the costs assigned to the successive histories encountered along an outcome list. -/
def charge (cost : List O → ℕ) : List O → List O → ℕ
  | _, [] => 0
  | h, o :: os => cost h + charge cost (h ++ [o]) os

/-- The branch linear map and accumulated history-dependent charge associated with a finite
outcome sequence. -/
def record (policy : List O → Instrument O D D) (cost : List O → ℕ)
    (h : List O) {n : ℕ} (xs : Fin n → O) :
    (Operator D →ₗ[ℂ] Operator D) × ℕ :=
  (branch policy h (List.ofFn xs), charge cost h (List.ofFn xs))
end Qatlib.Concepts.AdaptiveCP.BranchTrace
