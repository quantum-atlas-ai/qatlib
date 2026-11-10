/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Mathlib.Data.Vector.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib
variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

def branch (policy : List O → Instrument O D D) :
    List O → List O → (Operator D →ₗ[ℂ] Operator D)
  | _, [] => LinearMap.id
  | h, o :: os => (branch policy (h ++ [o]) os).comp ((policy h).branch o)
def charge (cost : List O → ℕ) : List O → List O → ℕ
  | _, [] => 0
  | h, o :: os => cost h + charge cost (h ++ [o]) os

def record (policy : List O → Instrument O D D) (cost : List O → ℕ)
    (h : List O) {n : ℕ} (xs : Fin n → O) :
    (Operator D →ₗ[ℂ] Operator D) × ℕ :=
  (branch policy h (List.ofFn xs), charge cost h (List.ofFn xs))
end Qatlib.Concepts.AdaptiveCP.BranchTrace
